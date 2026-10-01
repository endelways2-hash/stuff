from __future__ import annotations

import argparse
import contextlib
import copy
import faulthandler
import gzip
import hashlib
import importlib.util
import json
import math
import os
import re
import secrets
import signal
import sqlite3
import subprocess
import sys
import threading
import time
import traceback
import uuid
import webbrowser

from collections import Counter, defaultdict
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlsplit

import psutil
from filelock import FileLock, Timeout as LockTimeout


DEFAULT_RUN_DIR = Path(
    r"C:\Users\Nick\Desktop\deck_runs\afef7e2f8d64ab52d713"
)

MINIMAL_KEY = "_minimal_root_v1"
STORE_NAME = "deck_web_v1"

AUTO_SECONDS = 600.0
GIB = 1024 ** 3
HARD_MEMORY = 8 * GIB
HARD_SECONDS = 3600.0

# У CP-SAT max_memory_in_mb — целочисленный параметр, а не float.
# Не оставляем его на стандартном значении.
# 2**40 MiB — приблизительно 1 EiB, практически недостижимый порог.
# Внешних ограничений RSS, RAM guard и проверок "оставить резерв RAM" НЕТ.
CP_SAT_MEMORY_MB = 1 << 40

TERMINAL = {"SAT", "UNSAT"}
RESULT_STATUSES = {"SAT", "UNSAT", "UNKNOWN", "ERROR", "STOPPED"}

FILE_COORDS = re.compile(
    r"^d(-?\d+)_s(-?\d+)(?:_.*)?\.json$", re.IGNORECASE
)


# ----------------------------------------------------------------------
# Общие функции
# ----------------------------------------------------------------------

def finite(value, default=None):
    try:
        value = float(value)
        return value if math.isfinite(value) else default
    except (TypeError, ValueError, OverflowError):
        return default


def integer(value, default=0):
    try:
        return int(value)
    except (TypeError, ValueError, OverflowError):
        return default


def maximum_known(*values):
    values = [finite(v) for v in values]
    values = [v for v in values if v is not None]
    return max(values) if values else None


def read_json(path):
    path = Path(path)
    for attempt in range(3):
        try:
            with path.open("r", encoding="utf-8-sig") as stream:
                return json.load(stream)
        except (OSError, ValueError, UnicodeError):
            if attempt == 2:
                raise
            time.sleep(0.05 * (attempt + 1))


def quiet_json(path):
    try:
        value = read_json(path)
        return value if isinstance(value, dict) else None
    except (OSError, ValueError, UnicodeError):
        return None


def atomic_json(path, obj, durable=True):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)

    raw = (
        json.dumps(
            obj,
            ensure_ascii=False,
            allow_nan=False,
            separators=(",", ":"),
        ) + "\n"
    ).encode("utf-8")

    temporary = path.with_name(
        "." + path.name + "." + uuid.uuid4().hex + ".tmp"
    )

    try:
        with temporary.open("wb") as stream:
            stream.write(raw)
            if durable:
                stream.flush()
                os.fsync(stream.fileno())

        for attempt in range(6):
            try:
                os.replace(temporary, path)
                break
            except OSError:
                if attempt == 5:
                    raise
                time.sleep(0.05 * (2 ** attempt))

        if durable and os.name == "posix":
            with contextlib.suppress(OSError):
                fd = os.open(
                    str(path.parent),
                    os.O_RDONLY | getattr(os, "O_DIRECTORY", 0),
                )
                try:
                    os.fsync(fd)
                finally:
                    os.close(fd)
    finally:
        with contextlib.suppress(OSError):
            temporary.unlink(missing_ok=True)


def read_data_csv(path=None):
    import csv

    path = (
        Path(path).expanduser().resolve()
        if path is not None
        else Path(__file__).resolve().with_name("data.csv")
    )

    messages = []
    names = []
    seen = set()

    with path.open("r", encoding="utf-8-sig", newline="") as stream:
        reader = csv.reader(stream)

        header = None
        for row in reader:
            if any(cell.strip() for cell in row):
                header = [cell.strip() for cell in row]
                break

        if (
            header is None
            or len(header) < 3
            or header[0] != "#"
            or header[1].lower() != "pos"
        ):
            raise ValueError(
                "Ожидается CSV с заголовком #,Pos,1,2,..."
            )

        ids = set()

        for row in reader:
            line = reader.line_num
            if not any(cell.strip() for cell in row):
                continue

            if len(row) < 2:
                raise ValueError(f"data.csv, строка {line}: нет #/Pos")

            record_id = row[0].strip()
            if not record_id:
                raise ValueError(f"data.csv, строка {line}: пустой #")
            if record_id in ids:
                raise ValueError(
                    f"data.csv, строка {line}: повторный #={record_id}"
                )
            ids.add(record_id)

            cells = [cell.strip() for cell in row[2:]]

            # Нули НЕ удаляются. Убираем только пустой хвост.
            while cells and cells[-1] == "":
                cells.pop()

            if any(cell == "" for cell in cells):
                raise ValueError(
                    f"data.csv, строка {line}: "
                    "пустая ячейка внутри последовательности"
                )

            sequence = []
            for cell in cells:
                if not re.fullmatch(r"[+-]?\d+", cell):
                    raise ValueError(
                        f"data.csv, строка {line}: "
                        f"нецелая карта {cell!r}"
                    )
                card = int(cell)
                if card < 0:
                    raise ValueError(
                        f"data.csv, строка {line}: отрицательная карта"
                    )
                sequence.append(card)
                seen.add(card)

            messages.append(sequence)
            names.append(row[1].strip() or record_id)

    if not messages or not seen:
        raise ValueError("data.csv не содержит карт; невозможно определить N")

    n = max(seen) + 1

    # Для определения N из CSV требуем все карты 0..N-1.
    if len(seen) != n:
        raise ValueError(
            "В data.csv должны встречаться все номера карт 0..N-1; "
            "номера не перенумеровываются автоматически"
        )

    canonical = json.dumps(
        {"n": n, "messages": messages},
        separators=(",", ":"),
    ).encode("utf-8")
    dataset = hashlib.sha256(canonical).hexdigest()

    metadata = {
        "n": n,
        "messages": messages,
        "names": names,
        "source": str(path),
        "dataset": dataset,

        # Старый fingerprint мог вычисляться другим алгоритмом.
        # Совместимость проверяется по canonical N/messages dataset.
        "fingerprint": None,
    }

    return metadata, n, messages, dataset


def circular_distance(value, n):
    value %= n
    return min(value, n - value)


def k_limit(d, s, n):
    return circular_distance(d - s, n)


def process_memory(process, own=False):
    """RSS и известный пик RSS. Не устанавливает никаких ограничений."""
    rss = 0
    peak = 0

    with contextlib.suppress(psutil.Error, OSError):
        info = process.memory_info()
        rss = int(info.rss)
        peak = max(rss, int(getattr(info, "peak_wset", 0)))

    if own and os.name == "posix":
        with contextlib.suppress(Exception):
            import resource
            usage = resource.getrusage(resource.RUSAGE_SELF)
            multiplier = 1 if sys.platform == "darwin" else 1024
            peak = max(peak, int(usage.ru_maxrss) * multiplier)

    return rss, peak


# ----------------------------------------------------------------------
# Чтение старых результатов. Старые states не изменяются.
# Критерий закрытия сохранён из присланного кода.
# ----------------------------------------------------------------------

def proof_closes(proof):
    if proof is None:
        return False

    if not isinstance(proof, dict):
        return True

    return (
        proof.get("status", "UNSAT") in ("UNSAT", "INFEASIBLE")
        and not proof.get("assumption9")
        and proof.get("assumption9_id") is None
        and not proof.get("assumptions")
    )


def whole_config_closed(root):
    stack = [root]

    while stack:
        node = stack.pop()

        if not isinstance(node, dict):
            return False

        if proof_closes(node.get("proof")):
            continue

        if (
            "split" not in node
            or "left" not in node
            or "right" not in node
        ):
            return False

        stack.append(node["right"])
        stack.append(node["left"])

    return True


def legacy_row(cfg, filename, n):
    if not isinstance(cfg, dict):
        raise ValueError("State должен быть JSON-объектом")

    if not isinstance(cfg.get("tree"), dict):
        raise ValueError("В state отсутствует корректное tree")

    d, s, k = (int(cfg[key]) for key in ("d", "s", "k"))
    d %= n
    s %= n

    record = cfg.get(MINIMAL_KEY, {})
    if not isinstance(record, dict):
        raise ValueError(f"Некорректная запись {MINIMAL_KEY}")

    raw_status = str(record.get("status") or "").upper()
    closed = whole_config_closed(cfg["tree"])

    if closed:
        status = "UNSAT"
    elif raw_status == "ERROR":
        status = "ERROR"
    elif not raw_status:
        status = "PENDING"
    elif raw_status == "UNSAT":
        status = "ERROR"
    else:
        # Старый RUNNING без старого живого вычислителя — незавершённая
        # попытка, а не доказательство.
        status = "UNKNOWN"

    result = record.get("result")
    if not isinstance(result, dict):
        result = {}

    wall = finite(result.get("wall"))

    if closed and wall is None:
        proof = cfg["tree"].get("proof")
        if isinstance(proof, dict) and proof_closes(proof):
            proof_result = proof.get("result")
            if isinstance(proof_result, dict):
                wall = finite(proof_result.get("wall"))

    notes = []

    if closed:
        notes.append(
            "Старое безусловное закрытие принято без независимого аудита."
        )
    elif raw_status == "RUNNING":
        notes.append("В старом state осталась незавершённая попытка RUNNING.")
    elif raw_status == "UNSAT":
        notes.append(
            "Старая запись сообщает UNSAT, но tree не подтверждает "
            "безусловное закрытие всей конфигурации."
        )

    limit = k_limit(d, s, n)
    if not 1 <= k <= limit:
        notes.append(
            f"Сохранённый K={k} вне диапазона INPUT_RULE 1..{limit}. "
            "K автоматически не заменяется."
        )

    solved_elapsed = wall if closed else None

    return {
        "file": filename,
        "d": d,
        "s": s,
        "k": k,
        "status": status,
        "resolved": "UNSAT" if closed else None,
        "raw_status": raw_status,
        "last_status": raw_status or None,
        "attempts": integer(record.get("attempts")),
        "attempts_new": 0,
        "wall": wall,
        "elapsed": wall,
        "peak_bytes": None,
        "solved_peak_bytes": None,
        "solved_elapsed": solved_elapsed,
        "hard_memory": False,
        "hard_time": (
            solved_elapsed is not None and solved_elapsed > HARD_SECONDS
        ),
        "runnable": True,
        "note": "\n".join(notes),
        "error": str(record.get("error") or "")[:4000],
        "last_result_file": None,
        "solution_file": None,
    }


def load_catalog(directory, n, fingerprint, saved_records):
    grouped = defaultdict(list)
    warnings = []

    paths = sorted(
        path
        for path in (directory / "states").iterdir()
        if path.is_file()
        and path.name.lower().startswith("d")
        and "_s" in path.name.lower()
        and path.suffix.lower() == ".json"
    )

    for path in paths:
        try:
            row = legacy_row(read_json(path), path.name, n)
        except Exception as exc:
            message = f"{path.name}: {type(exc).__name__}: {exc}"
            match = FILE_COORDS.match(path.name)

            if not match:
                warnings.append(message)
                continue

            row = {
                "file": path.name,
                "d": int(match[1]) % n,
                "s": int(match[2]) % n,
                "k": None,
                "status": "ERROR",
                "resolved": None,
                "runnable": False,
                "attempts": 0,
                "attempts_new": 0,
                "hard_memory": False,
                "hard_time": False,
                "peak_bytes": None,
                "elapsed": None,
                "error": message,
                "note": (
                    "Файл не удалось корректно прочитать. "
                    "Без известного K вычисление не запускается."
                ),
            }

        grouped[row["d"], row["s"]].append(row)

    rows = {}

    for coordinates, group in grouped.items():
        row = group[0]

        if len(group) > 1:
            row = dict(row)
            ks = {item.get("k") for item in group}

            row.update(
                status="ERROR",
                runnable=False,
                resolved=None,
                k=next(iter(ks)) if len(ks) == 1 else None,
                variants=[
                    {
                        "file": item["file"],
                        "k": item.get("k"),
                        "status": item["status"],
                    }
                    for item in group
                ],
                error="Несколько state-файлов для одной пары D/S.",
                note=(
                    "Не выбирается произвольный файл или максимальный K. "
                    "Сначала нужно устранить неоднозначность в states."
                ),
            )

            warnings.append(
                f"D={coordinates[0]}, S={coordinates[1]}: "
                f"найдено {len(group)} state-файлов."
            )

        rows[row["file"]] = row

    positions = {
        (row["d"], row["s"]): row["file"]
        for row in rows.values()
    }

    # Старый решатель сохранял SAT отдельно от MINIMAL-записи.
    sat_path = directory / "SAT.json"

    if sat_path.exists():
        try:
            sat = read_json(sat_path)

            if int(sat.get("n", n)) != n:
                raise ValueError("SAT.json имеет другой N")

            other_fingerprint = sat.get("fingerprint")
            if (
                fingerprint is not None
                and other_fingerprint is not None
                and fingerprint != other_fingerprint
            ):
                raise ValueError("fingerprint SAT.json не совпадает")

            if sat.get("status", "SAT") not in (
                "SAT", "FEASIBLE", "OPTIMAL"
            ):
                raise ValueError("Неожиданный статус SAT.json")

            d, s, k = (int(sat[key]) for key in ("d", "s", "k"))
            d %= n
            s %= n

            if not 1 <= k <= k_limit(d, s, n):
                raise ValueError("K из SAT.json несовместим с INPUT_RULE")

            filename = positions.get((d, s))
            row = rows.get(filename)

            if (
                row is None
                or not row.get("runnable")
                or row.get("k") != k
            ):
                raise ValueError(
                    "Нет однозначного читаемого state с тем же D/S/K"
                )

            if row.get("resolved") == "UNSAT":
                row.update(
                    status="ERROR",
                    runnable=False,
                    error="Конфликт: старые SAT и UNSAT для одного D/S/K.",
                )
            else:
                wall = finite(sat.get("wall"))
                row.update(
                    status="SAT",
                    resolved="SAT",
                    wall=wall,
                    elapsed=wall,
                    solved_elapsed=wall,
                    hard_time=wall is not None and wall > HARD_SECONDS,
                    solution_file="SAT.json",
                    last_result_file="SAT.json",
                    note="Старый SAT.json принят без независимого аудита.",
                )
        except Exception as exc:
            warnings.append(f"SAT.json: {exc}")

    # Накладываем новые сохранённые результаты только на тот же D/S/K.
    for filename, base in list(rows.items()):
        saved = saved_records.get(filename)

        if not saved or not base.get("runnable"):
            continue

        if any(saved.get(key) != base.get(key) for key in ("d", "s", "k")):
            warnings.append(
                f"{filename}: D/S/K изменились; прежний web-результат "
                "не применён к изменённой конфигурации."
            )
            continue

        merged = {**base, **saved}
        old_terminal = base.get("resolved")
        new_terminal = saved.get("resolved")

        merged["attempts"] = max(
            integer(base.get("attempts")),
            integer(saved.get("attempts")),
        )
        merged["solved_elapsed"] = maximum_known(
            base.get("solved_elapsed"),
            saved.get("solved_elapsed"),
        )
        merged["solved_peak_bytes"] = maximum_known(
            base.get("solved_peak_bytes"),
            saved.get("solved_peak_bytes"),
        )
        merged["hard_memory"] = bool(
            base.get("hard_memory") or saved.get("hard_memory")
        )
        merged["hard_time"] = bool(
            base.get("hard_time") or saved.get("hard_time")
        )

        if (
            old_terminal in TERMINAL
            and new_terminal in TERMINAL
            and old_terminal != new_terminal
        ):
            merged.update(
                status="ERROR",
                runnable=False,
                error="Конфликт между старым и новым SAT/UNSAT.",
            )
        elif old_terminal in TERMINAL and new_terminal not in TERMINAL:
            merged["resolved"] = old_terminal
            merged["status"] = old_terminal

        rows[filename] = merged

    if not paths:
        warnings.append("В states не найдено файлов конфигураций.")

    blocked = sum(not row.get("runnable") for row in rows.values())
    if blocked:
        warnings.append(
            f"Незапускаемых ячеек: {blocked}. "
            "Повреждённые или неоднозначные states не вычисляются."
        )

    return rows, warnings, len(paths)


# ----------------------------------------------------------------------
# BASE-модель из присланного решателя:
# целая конфигурация, без assumptions, splits и дополнительного аудита.
# ----------------------------------------------------------------------

class Halt(Exception):
    pass


def _v2_previous_build_model(messages, n, d, s, k, check):
    from ortools.sat.python import cp_model

    d %= n
    s %= n

    model = cp_model.CpModel()

    initial = [
        model.new_int_var(0, n - 1, f"P_{card}")
        for card in range(n)
    ]
    model.add_all_different(initial)

    initial_indices = [variable.index for variable in initial]

    if not 1 <= k <= n or circular_distance(d - s, n) < k:
        model.add_bool_or([])
        return model, initial_indices, []

    windows = [
        cp_model.Domain.from_values(
            sorted({(t * s + u) % n for u in range(k)})
        )
        for t in range(n)
    ]

    def position():
        return model.new_int_var(0, n - 1, "")

    nonzero_difference = cp_model.Domain.from_intervals([
        [-(n - 1), -1], [1, n - 1]
    ])

    first_edges = {}
    outputs = []

    for sequence in messages:
        check()

        remaining = Counter(sequence)
        pos = {
            card: initial[card]
            for card in sorted(remaining)
        }
        row = []

        for t, card in enumerate(sequence):
            check()

            a = pos[card]
            restricted = a.domain.intersection_with(windows[t % n])
            if restricted.is_empty():
                return _reduced_impossible(n)
            a.domain = restricted
            row.append(a.index)

            remaining[card] -= 1
            if remaining[card] == 0:
                del pos[card]

            if not pos or d == 0:
                continue

            b = position()
            model.add_modulo_equality(b, a + d, n)

            if remaining[card]:
                pos[card] = b

            for other in list(pos):
                if other == card:
                    continue

                old = pos[other]
                edge = (card, other)

                hit = first_edges.get(edge) if t == 0 else None

                if hit is None:
                    hit = model.new_bool_var("")
                    model.add(old == b).only_enforce_if(hit)
                    model.add_linear_expression_in_domain(
                        old - b, nonzero_difference
                    ).only_enforce_if(hit.Not())

                    if t == 0:
                        first_edges[edge] = hit

                new = position()
                model.add(new == a).only_enforce_if(hit)
                model.add(new == old).only_enforce_if(hit.Not())
                pos[other] = new

        outputs.append(row)

    return model, initial_indices, outputs


def build_model(messages, n, d, s, k, check):
    return _v2_build_model(messages, n, d, s, k, check)


def _reduced_reference_build_model(messages, n, d, s, k, check):
    from ortools.sat.python import cp_model

    d %= n
    s %= n

    model = cp_model.CpModel()

    initial = [
        model.new_int_var(0, n - 1, f"P_{card}")
        for card in range(n)
    ]
    model.add_all_different(initial)

    initial_indices = [variable.index for variable in initial]

    if not 1 <= k <= n or circular_distance(d - s, n) < k:
        model.add_bool_or([])
        return model, initial_indices, []

    windows = [
        cp_model.Domain.from_values(
            sorted({(t * s + u) % n for u in range(k)})
        )
        for t in range(n)
    ]

    def position():
        return model.new_int_var(0, n - 1, "")

    first_edges = {}
    outputs = []

    for sequence in messages:
        check()

        remaining = Counter(sequence)
        pos = {
            card: initial[card]
            for card in sorted(remaining)
        }
        row = []

        for t, card in enumerate(sequence):
            check()

            a = pos[card]
            model.add_linear_expression_in_domain(a, windows[t % n])
            row.append(a.index)

            remaining[card] -= 1
            if remaining[card] == 0:
                del pos[card]

            if not pos or d == 0:
                continue

            b = position()
            carry = model.new_bool_var("")
            model.add(b == a + d - n * carry)

            if remaining[card]:
                pos[card] = b

            for other in list(pos):
                if other == card:
                    continue

                old = pos[other]
                edge = (card, other)

                hit = first_edges.get(edge) if t == 0 else None

                if hit is None:
                    hit = model.new_bool_var("")
                    model.add(old == b).only_enforce_if(hit)
                    model.add(old != b).only_enforce_if(hit.Not())

                    if t == 0:
                        first_edges[edge] = hit

                new = position()
                model.add(new == a).only_enforce_if(hit)
                model.add(new == old).only_enforce_if(hit.Not())
                pos[other] = new

        outputs.append(row)

    return model, initial_indices, outputs


# ----------------------------------------------------------------------
# Внутренний вычислительный процесс.
# Запускается автоматически тем же самым deck_server.py.
# Обмен через атомарные JSON-файлы, не через multiprocessing Pipe.
# ----------------------------------------------------------------------

# BEGIN DECK_CUSTOM8_V2

DECK_CUSTOM8_PROFILE = 'incumbent/pair/satx5+lp1x3'

DECK_CUSTOM8_NAMES = (
    "tile_sat",
    "tile_erwa",
    "tile_restart",
    "tile_probe",
    "tile_positions",
    "tile_random",
    "tile_lp1",
    "tile_lp2_lazy",
)


# BEGIN DECK_BENCH_WINNER_V1
_DECK_BENCH_WINNER = json.loads('{"format": 1, "ortools": "9.15.6755", "dataset": "ba4f67d98e740ea3714c946323f8aad8a9ec1c9385dab299918b4e78df306f12", "candidate": {"id": "f339c73ccd98c21c1009", "name": "incumbent/pair/satx5+lp1x3", "decision": "freq_min", "params": "use_pb_resolution: false\\nsearch_branching: AUTOMATIC_SEARCH\\ncp_model_presolve: true\\nenumerate_all_solutions: false\\nstop_after_first_solution: true\\nuse_lns_only: false\\ninstantiate_all_variables: true\\nuse_optional_variables: false\\nuse_exact_lp_reason: true\\nshare_level_zero_bounds: true\\nuse_rins_lns: false\\ninterleave_search: false\\nuse_sat_inprocessing: true\\nuse_feasibility_pump: false\\nfix_variables_to_their_hinted_value: false\\nshare_binary_clauses: true\\nnum_workers: 8\\nsubsolvers: \\"bench_00\\"\\nsubsolvers: \\"bench_01\\"\\nsubsolvers: \\"bench_02\\"\\nsubsolvers: \\"bench_03\\"\\nsubsolvers: \\"bench_04\\"\\nsubsolvers: \\"bench_05\\"\\nsubsolvers: \\"bench_06\\"\\nsubsolvers: \\"bench_07\\"\\nsubsolver_params {\\n  search_branching: AUTOMATIC_SEARCH\\n  linearization_level: 0\\n  name: \\"bench_00\\"\\n}\\nsubsolver_params {\\n  search_branching: AUTOMATIC_SEARCH\\n  linearization_level: 0\\n  name: \\"bench_01\\"\\n}\\nsubsolver_params {\\n  search_branching: AUTOMATIC_SEARCH\\n  linearization_level: 0\\n  name: \\"bench_02\\"\\n}\\nsubsolver_params {\\n  search_branching: AUTOMATIC_SEARCH\\n  linearization_level: 0\\n  name: \\"bench_03\\"\\n}\\nsubsolver_params {\\n  search_branching: AUTOMATIC_SEARCH\\n  linearization_level: 0\\n  name: \\"bench_04\\"\\n}\\nsubsolver_params {\\n  search_branching: AUTOMATIC_SEARCH\\n  linearization_level: 1\\n  add_lp_constraints_lazily: true\\n  name: \\"bench_05\\"\\n}\\nsubsolver_params {\\n  search_branching: AUTOMATIC_SEARCH\\n  linearization_level: 1\\n  add_lp_constraints_lazily: true\\n  name: \\"bench_06\\"\\n}\\nsubsolver_params {\\n  search_branching: AUTOMATIC_SEARCH\\n  linearization_level: 1\\n  add_lp_constraints_lazily: true\\n  name: \\"bench_07\\"\\n}\\nshared_tree_num_workers: 0\\nuse_ls_only: false\\nnum_violation_ls: 0\\nuse_feasibility_jump: false\\nuse_lns: false\\nshare_glue_clauses: true\\nvariables_shaving_level: 0\\nfilter_subsolvers: \\"bench_00\\"\\nfilter_subsolvers: \\"bench_01\\"\\nfilter_subsolvers: \\"bench_02\\"\\nfilter_subsolvers: \\"bench_03\\"\\nfilter_subsolvers: \\"bench_04\\"\\nfilter_subsolvers: \\"bench_05\\"\\nfilter_subsolvers: \\"bench_06\\"\\nfilter_subsolvers: \\"bench_07\\"\\nnum_full_subsolvers: 8\\n", "expected_full": 8}}')

def _deck8_check_version():
    import ortools

    actual = str(ortools.__version__)
    expected = _DECK_BENCH_WINNER["ortools"]
    if actual != expected:
        raise RuntimeError(
            f"Победитель измерен на OR-Tools {expected}, "
            f"установлено {actual}. Запустите сервер тем же "
            "Python-окружением, что и бенчмарк."
        )
    return actual

def _deck_bench_apply(solver, model, initial_indices, messages):
    import hashlib
    import json
    import ortools

    from collections import Counter
    from google.protobuf import text_format
    from google.protobuf.message import Message
    from ortools.sat import sat_parameters_pb2
    from ortools.sat.python import cp_model

    SP = sat_parameters_pb2.SatParameters
    FORMAT_VERSION = 1
    RUNTIME_FIELDS = ('max_time_in_seconds', 'max_deterministic_time', 'max_number_of_conflicts', 'max_num_deterministic_batches', 'max_memory_in_mb', 'random_seed', 'log_search_progress', 'log_to_stdout', 'log_to_response', 'log_subsolver_statistics', 'log_prefix', 'catch_sigint_signal')

    # Локальный загрузчик встроенного winner, без чтения файлов.
    def get_json(_path):
        return _DECK_BENCH_WINNER

    def snapshot_parameters(parameters):
        result = SP()
        if isinstance(parameters, Message):
            result.CopyFrom(parameters)
        else:
            text_format.Parse(str(parameters), result)
        return result

    def parse_parameters(text):
        result = SP()
        text_format.Parse(text, result)
        return result

    def native_parameters(proto):
        """
        Construct a fresh parameter object of the type required by CpSolver.

        The native 9.15 binding is not assumed to be a standard protobuf.
        Child profiles are built separately before extending subsolver_params.
        A protobuf round-trip verifies that nothing was lost.
        """
        native_type = type(cp_model.CpSolver().parameters)

        def convert(source):
            target = native_type()

            if isinstance(target, Message):
                target.CopyFrom(source)
                return target

            for field, value in source.ListFields():
                name = field.name

                if field.is_repeated:
                    if field.message_type is not None:
                        if name != "subsolver_params":
                            raise TypeError(
                                f"Unsupported repeated parameter message: {name}"
                            )
                        children = [convert(item) for item in value]
                        getattr(target, name).extend(children)
                    elif field.enum_type is not None:
                        # Generated candidates use default_restart_algorithms
                        # instead of the repeated restart_algorithms field.
                        raise TypeError(
                            f"Unsupported repeated enum in native bridge: {name}"
                        )
                    else:
                        getattr(target, name).extend(list(value))
                elif field.message_type is not None:
                    raise TypeError(
                        f"Unsupported singular parameter message: {name}"
                    )
                elif field.enum_type is not None:
                    current = getattr(target, name)
                    setattr(target, name, type(current)(int(value)))
                else:
                    setattr(target, name, value)

            return target

        native = convert(proto)
        actual = snapshot_parameters(native)
        if actual != proto:
            raise RuntimeError(
                "SatParameters round-trip mismatch. "
                "The native binding did not preserve the requested configuration."
            )
        return native

    def clear_search_strategy(model):
        proto = model.proto
        if isinstance(proto, Message):
            proto.ClearField("search_strategy")
        else:
            proto.search_strategy.clear()

    def add_decisions(model, initial_indices, messages, mode):
        if model.has_objective():
            raise ValueError("Expected a satisfaction model without an objective.")
        if len(model.proto.assumptions):
            raise ValueError("Benchmark models must not contain assumptions.")
        if len(model.proto.solution_hint.vars):
            raise ValueError("Benchmark models must not contain solution hints.")

        clear_search_strategy(model)

        if mode == "none":
            return

        frequency = Counter()
        coverage = Counter()
        for sequence in messages:
            frequency.update(sequence)
            coverage.update(set(sequence))

        order = sorted(
            range(len(initial_indices)),
            key=lambda card: (-coverage[card], -frequency[card], card),
        )

        if mode == "natural_min":
            order = list(range(len(initial_indices)))

        options = {
            "freq_min": (
                cp_model.CHOOSE_MIN_DOMAIN_SIZE,
                cp_model.SELECT_MIN_VALUE,
            ),
            "natural_min": (
                cp_model.CHOOSE_MIN_DOMAIN_SIZE,
                cp_model.SELECT_MIN_VALUE,
            ),
            "freq_max": (
                cp_model.CHOOSE_MIN_DOMAIN_SIZE,
                cp_model.SELECT_MAX_VALUE,
            ),
            "freq_lower_half": (
                cp_model.CHOOSE_MIN_DOMAIN_SIZE,
                cp_model.SELECT_LOWER_HALF,
            ),
            "freq_upper_half": (
                cp_model.CHOOSE_MIN_DOMAIN_SIZE,
                cp_model.SELECT_UPPER_HALF,
            ),
            "freq_first": (
                cp_model.CHOOSE_FIRST,
                cp_model.SELECT_MIN_VALUE,
            ),
            "bool_first": (
                cp_model.CHOOSE_MIN_DOMAIN_SIZE,
                cp_model.SELECT_MIN_VALUE,
            ),
        }
        if mode not in options:
            raise ValueError(f"Unknown decision mode: {mode}")

        used = set()

        if mode == "bool_first":
            boolean_indices = [
                index
                for index, variable in enumerate(model.proto.variables)
                if list(variable.domain) == [0, 1]
            ]
            used.update(boolean_indices)
            if boolean_indices:
                model.add_decision_strategy(
                    [
                        model.get_int_var_from_proto_index(index)
                        for index in boolean_indices
                    ],
                    cp_model.CHOOSE_FIRST,
                    cp_model.SELECT_MIN_VALUE,
                )

        indices = [
            int(initial_indices[card])
            for card in order
            if int(initial_indices[card]) not in used
        ]
        if indices:
            variable_rule, value_rule = options[mode]
            model.add_decision_strategy(
                [
                    model.get_int_var_from_proto_index(index)
                    for index in indices
                ],
                variable_rule,
                value_rule,
            )

    def dataset_hash(n, messages):
        # Deliberately matches read_data_csv() from the supplied server.
        payload = {
            "n": int(n),
            "messages": [[int(card) for card in seq] for seq in messages],
        }
        raw = json.dumps(payload, separators=(",", ":")).encode("utf-8")
        return hashlib.sha256(raw).hexdigest()

    def apply_winner(
        solver,
        model,
        initial_indices,
        messages,
        winner_path,
    ):
        """
        Install the measured winner into a newly constructed solver/model.

        Search decisions are replaced, but constraints are unchanged.
        The caller's time, memory, seed and logging controls are preserved.
        """
        winner = get_json(winner_path)

        if winner.get("format") != FORMAT_VERSION:
            raise RuntimeError("Unsupported winner file format.")
        if str(ortools.__version__) != winner["ortools"]:
            raise RuntimeError(
                f"Winner was measured with OR-Tools {winner['ortools']}; "
                f"current version is {ortools.__version__}. Re-benchmark."
            )
        if dataset_hash(len(initial_indices), messages) != winner["dataset"]:
            raise RuntimeError("Winner belongs to a different N/messages dataset.")

        candidate = winner["candidate"]
        previous = snapshot_parameters(solver.parameters)
        parameters = parse_parameters(candidate["params"])

        for name in RUNTIME_FIELDS:
            parameters.ClearField(name)
            if previous.HasField(name):
                setattr(parameters, name, getattr(previous, name))

        parameters.num_workers = 8
        parameters.ClearField("num_search_workers")

        add_decisions(
            model,
            initial_indices,
            messages,
            candidate["decision"],
        )
        solver.parameters = native_parameters(parameters)

        configured = list(parameters.filter_subsolvers)
        if not configured:
            configured = list(parameters.subsolvers)
        if not configured:
            configured = ["automatic_portfolio"]

        return {
            "id": candidate["id"],
            "name": candidate["name"],
            "decision": candidate["decision"],
            "subsolvers": configured,
        }

    return apply_winner(
        solver=solver,
        model=model,
        initial_indices=initial_indices,
        messages=messages,
        winner_path=None,
    )
# END DECK_BENCH_WINNER_V1


def _deck8_set(parameters, field, value):
    if not hasattr(parameters, field):
        raise RuntimeError(
            f"CUSTOM8: в установленном API нет параметра {field!r}"
        )

    try:
        setattr(parameters, field, value)
    except (AttributeError, TypeError, ValueError, OverflowError) as exc:
        raise RuntimeError(
            f"CUSTOM8: не удалось установить {field}={value!r}: {exc}"
        ) from exc

    if getattr(parameters, field) != value:
        raise RuntimeError(
            f"CUSTOM8: параметр {field!r} не сохранил заданное значение"
        )


def _deck8_replace_repeated(parameters, field, values):
    """Работает с protobuf API и контейнерами новых Python bindings."""
    values = list(values)

    if not hasattr(parameters, field):
        raise RuntimeError(
            f"CUSTOM8: в установленном API нет поля {field!r}"
        )

    clear_field = getattr(parameters, "ClearField", None)

    if callable(clear_field):
        clear_field(field)
    else:
        container = getattr(parameters, field)
        clear = getattr(container, "clear", None)

        if not callable(clear):
            raise RuntimeError(
                f"CUSTOM8: нет поддерживаемого способа очистить {field!r}"
            )

        clear()

    container = getattr(parameters, field)

    if len(container) != 0:
        raise RuntimeError(
            f"CUSTOM8: поле {field!r} не очистилось"
        )

    container.extend(values)

    if len(getattr(parameters, field)) != len(values):
        raise RuntimeError(
            f"CUSTOM8: поле {field!r} заполнено некорректно"
        )


def _deck8_configure(parameters):
    from ortools.sat.python import cp_model

    _deck8_check_version()

    # Эти настройки принадлежат исходному worker.
    # Портфель не должен менять бюджеты, память или seed попытки.
    protected_fields = (
        "max_time_in_seconds",
        "max_deterministic_time",
        "max_number_of_conflicts",
        "max_memory_in_mb",
        "random_seed",
    )
    protected = {
        field: getattr(parameters, field)
        for field in protected_fields
    }

    common = {
        "num_workers": 8,
        "num_full_subsolvers": 8,
        "search_branching": cp_model.AUTOMATIC_SEARCH,
        "interleave_search": False,
        "shared_tree_num_workers": 0,

        # Здесь выбран портфель full-subsolvers.
        # Дополнительные LS/LNS/first-solution профили не добавляем.
        "use_lns": False,
        "use_rins_lns": False,
        "use_feasibility_pump": False,
        "use_feasibility_jump": False,
        "num_violation_ls": 0,

        # Обмен информацией между выбранными поисковыми профилями.
        "share_level_zero_bounds": True,
        "share_binary_clauses": True,
        "share_glue_clauses": True,
        "use_sat_inprocessing": True,

        # Вспомогательные переменные дополняются обычным поиском.
        "instantiate_all_variables": True,
    }

    for field, value in common.items():
        _deck8_set(parameters, field, value)

    # Отдельный механизм variable shaving изменился между версиями.
    # Shaving внутри tile_probe настраивается отдельно ниже.
    if hasattr(parameters, "variables_shaving_level"):
        _deck8_set(parameters, "variables_shaving_level", 0)
    elif hasattr(parameters, "use_variables_shaving_search"):
        _deck8_set(parameters, "use_variables_shaving_search", False)
    else:
        raise RuntimeError(
            "CUSTOM8: неизвестный API настройки variable shaving"
        )

    probe = {
        "search_branching": cp_model.AUTOMATIC_SEARCH,
        "linearization_level": 0,
        "use_probing_search": True,
        "use_extended_probing": True,
        "at_most_one_max_expansion_size": 2,
        "shaving_search_deterministic_time": 0.001,
    }

    # В 9.12 это bool; в более новых версиях — отдельный бюджет.
    # Это локальный бюджет шага probing/shaving, не лимит всей попытки.
    if hasattr(
        parameters, "shaving_deterministic_time_in_probing_search"
    ):
        probe["shaving_deterministic_time_in_probing_search"] = 0.001
    elif hasattr(parameters, "use_shaving_in_probing_search"):
        probe["use_shaving_in_probing_search"] = True
    else:
        raise RuntimeError(
            "CUSTOM8: неизвестный API настройки shaving в probing"
        )

    specs = (
        (
            "tile_sat",
            {
                "search_branching": cp_model.AUTOMATIC_SEARCH,
                "linearization_level": 0,
                "use_erwa_heuristic": False,
            },
        ),
        (
            "tile_erwa",
            {
                "search_branching": cp_model.AUTOMATIC_SEARCH,
                "linearization_level": 0,
                "use_erwa_heuristic": True,
                "initial_variables_activity": 0.01,
            },
        ),
        (
            "tile_restart",
            {
                "search_branching": (
                    cp_model.PORTFOLIO_WITH_QUICK_RESTART_SEARCH
                ),
                "linearization_level": 0,
                "search_random_variable_pool_size": 5,
            },
        ),
        (
            "tile_probe",
            probe,
        ),
        (
            "tile_positions",
            {
                "search_branching": cp_model.PARTIAL_FIXED_SEARCH,
                "linearization_level": 0,
                "search_random_variable_pool_size": 1,
            },
        ),
        (
            "tile_random",
            {
                "search_branching": cp_model.RANDOMIZED_SEARCH,
                "linearization_level": 0,
                "search_random_variable_pool_size": 5,
            },
        ),
        (
            "tile_lp1",
            {
                "search_branching": cp_model.AUTOMATIC_SEARCH,
                "linearization_level": 1,
            },
        ),
        (
            "tile_lp2_lazy",
            {
                "search_branching": cp_model.AUTOMATIC_SEARCH,
                "linearization_level": 2,
                "add_lp_constraints_lazily": True,
            },
        ),
    )

    names = [name for name, _ in specs]

    if tuple(names) != DECK_CUSTOM8_NAMES or len(set(names)) != 8:
        raise RuntimeError("CUSTOM8: некорректный список профилей")

    profiles = []

    for name, settings in specs:
        # Не копируем весь родительский объект параметров:
        # CP-SAT сам объединит этот профиль с базовыми параметрами.
        profile = type(parameters)()
        _deck8_set(profile, "name", name)

        for field, value in settings.items():
            _deck8_set(profile, field, value)

        profiles.append(profile)

    for field, values in (
        ("extra_subsolvers", []),
        ("ignore_subsolvers", []),
        ("subsolver_params", profiles),
        ("subsolvers", names),
        ("filter_subsolvers", names),
    ):
        _deck8_replace_repeated(parameters, field, values)

    if list(parameters.subsolvers) != names:
        raise RuntimeError("CUSTOM8: список subsolvers не совпадает")

    if list(parameters.filter_subsolvers) != names:
        raise RuntimeError("CUSTOM8: фильтр subsolvers не совпадает")

    # Проверяем вложенные профили через protobuf-снимок,
    # минуя проблему владения pybind-ссылками на subsolver_params.
    from google.protobuf import text_format
    from ortools.sat import sat_parameters_pb2

    snapshot = sat_parameters_pb2.SatParameters()
    text_format.Parse(str(parameters), snapshot)

    actual_profiles = list(snapshot.subsolver_params)

    if [p.name for p in actual_profiles] != names:
        raise RuntimeError(
            "CUSTOM8: именованные параметры не совпадают"
        )

    for snap_profile, (_, settings) in zip(actual_profiles, specs):
        for field, expected in settings.items():
            # В protobuf enum представлен числом, а в pybind —
            # объектом enum.  Приводим к int для сравнения.
            expected_value = (
                int(expected)
                if field == "search_branching"
                else expected
            )

            actual_value = getattr(snap_profile, field)

            if actual_value != expected_value:
                raise RuntimeError(
                    f"CUSTOM8: профиль {snap_profile.name!r}, "
                    f"параметр {field!r}: "
                    f"ожидалось {expected_value!r}, "
                    f"получено {actual_value!r}"
                )

    for field, expected in protected.items():
        if getattr(parameters, field) != expected:
            raise RuntimeError(
                f"CUSTOM8 неожиданно изменил защищённый параметр {field!r}"
            )

    return names


def _deck8_add_decisions(model, initial_indices, messages, check):
    from collections import Counter
    from ortools.sat.python import cp_model

    check()

    if model.has_objective():
        raise RuntimeError(
            "CUSTOM8 для этого deck_server ожидает модель без objective"
        )

    if len(model.proto.assumptions):
        raise RuntimeError(
            "CUSTOM8 для этого deck_server ожидает модель без assumptions"
        )

    if len(model.proto.search_strategy):
        raise RuntimeError(
            "CUSTOM8: в модели уже есть пользовательская стратегия поиска"
        )

    if not initial_indices:
        return

    frequency = Counter()
    message_count = Counter()

    for sequence in messages:
        check()
        frequency.update(sequence)
        message_count.update(set(sequence))

    # При равном диапазоне переменных предпочитаем карты,
    # участвующие в большем числе сообщений, затем более частые.
    order = sorted(
        range(len(initial_indices)),
        key=lambda card: (
            -message_count[card],
            -frequency[card],
            card,
        ),
    )

    variables = [
        model.get_int_var_from_proto_index(int(initial_indices[card]))
        for card in order
    ]

    # D/S/K здесь константы конфигурации.
    # Добавляем только предпочтение ветвления по начальной перестановке.
    # Новых переменных, равенств, hints и ограничений не создаём.
    model.add_decision_strategy(
        variables,
        cp_model.CHOOSE_MIN_DOMAIN_SIZE,
        cp_model.SELECT_MIN_VALUE,
    )

    check()

# END DECK_CUSTOM8_V2


def worker_main(job_directory):
    job_directory = Path(job_directory).resolve()
    job = read_json(job_directory / "job.json")

    cancel_path = job_directory / "cancel.json"
    progress_path = job_directory / "progress.json"
    result_path = job_directory / "result.json"

    for name in ("SIGINT", "SIGBREAK", "SIGHUP"):
        if hasattr(signal, name):
            with contextlib.suppress(OSError, ValueError):
                signal.signal(getattr(signal, name), signal.SIG_IGN)

    with contextlib.suppress(Exception):
        faulthandler.enable(all_threads=True)

    started = time.time()
    began = time.monotonic()

    stop = threading.Event()
    finished = threading.Event()
    state_lock = threading.RLock()
    current_solver = [None]

    own_process = psutil.Process()
    state = {
        "job_id": job["id"],
        "pid": os.getpid(),
        "created": own_process.create_time(),
        "phase": "IMPORT",
        "started": started,
        "solve_started": None,
        "solve_mono": None,
        "rss_bytes": 0,
        "peak_bytes": 0,
        "variables": 0,
        "constraints": 0,
    }

    try:
        parent = psutil.Process(int(job["parent_pid"]))
        correct_parent = (
            abs(parent.create_time() - float(job["parent_created"])) < 0.02
        )
    except psutil.Error:
        parent = None
        correct_parent = False

    def parent_alive():
        if parent is None or not correct_parent:
            return False
        try:
            return parent.is_running()
        except psutil.AccessDenied:
            return True
        except psutil.Error:
            return False

    def check():
        if stop.is_set():
            raise Halt()

    def update(**values):
        with state_lock:
            state.update(values)

    def sample():
        rss, peak = process_memory(own_process, own=True)

        with state_lock:
            state["rss_bytes"] = rss
            state["peak_bytes"] = max(state["peak_bytes"], peak)

            snapshot = dict(state)
            solve_mono = snapshot.pop("solve_mono")

        now = time.monotonic()
        snapshot["updated"] = time.time()
        snapshot["elapsed"] = max(0.0, now - began)
        snapshot["solve_elapsed"] = (
            max(0.0, now - solve_mono)
            if solve_mono is not None else 0.0
        )
        return snapshot

    def watch():
        stopping_since = None
        published = 0.0

        while not finished.wait(0.20):
            now = time.monotonic()

            if cancel_path.exists() or not parent_alive():
                stop.set()

            if stop.is_set():
                if stopping_since is None:
                    stopping_since = now

                solver = current_solver[0]
                if solver is not None:
                    with contextlib.suppress(Exception):
                        solver.stop_search()

                # Только явная отмена или исчезновение родителя.
                # Это НЕ watchdog времени безлимитного решения
                # и НЕ ограничитель памяти.
                if now - stopping_since > 8.0:
                    os._exit(130)

            if now - published >= 0.5:
                published = now
                with contextlib.suppress(Exception):
                    atomic_json(progress_path, sample(), durable=False)

    if cancel_path.exists() or not parent_alive():
        stop.set()

    with contextlib.suppress(Exception):
        atomic_json(progress_path, sample(), durable=False)

    watcher = threading.Thread(target=watch, daemon=True)
    watcher.start()

    result = {
        "job_id": job["id"],
        "file": job["file"],
        "dataset": job["dataset"],
        "d": job["d"],
        "s": job["s"],
        "k": job["k"],
        "status": "ERROR",
        "wall": None,
        "scope": "whole_config",
        "model": "REDUCED",
        "model_version": REDUCED_VERSION,
        "assumption9": False,
        "assumption9_id": None,
        "cube": [],
        "independently_verified": False,
        "limit_seconds": job["budget"],
        "workers": job["workers"],
        "seed": job["seed"],
    }

    print(
        f"JOB {job['id']} "
        f"D={job['d']} S={job['s']} K={job['k']} "
        f"mode={job['mode']} budget={job['budget']}",
        flush=True,
    )

    try:
        check()

        import ortools
        from ortools.sat.python import cp_model

        result["ortools"] = _deck8_check_version()

        if int(job["workers"]) != 8:
            raise RuntimeError(
                "CUSTOM8 требует ровно 8 поисковых workers"
            )

        manifest, n, messages, dataset = read_data_csv(job["data_csv"])

        if dataset != job["dataset"]:
            result["fatal_input"] = True
            raise RuntimeError(
                "data.csv изменился после запуска сервера. "
                "Вычисление с изменёнными входными данными запрещено."
            )

        result["n"] = n
        result["fingerprint"] = manifest.get("fingerprint")

        check()
        update(phase="BUILD")

        model, initial_indices, output_indices = build_model(
            messages,
            n,
            int(job["d"]),
            int(job["s"]),
            int(job["k"]),
            check,
        )

        update(
            variables=len(model.proto.variables),
            constraints=len(model.proto.constraints),
        )


        solver = cp_model.CpSolver()
        parameters = solver.parameters

        parameters.num_workers = 8
        parameters.random_seed = int(job["seed"])
        parameters.cp_model_presolve = True
        parameters.stop_after_first_solution = True
        parameters.log_search_progress = False
        parameters.log_to_stdout = False

        parameters.max_memory_in_mb = CP_SAT_MEMORY_MB

        if job["budget"] is None:
            parameters.max_time_in_seconds = float("inf")
        else:
            parameters.max_time_in_seconds = float(job["budget"])

        # Никаких дополнительных ограничений deterministic time,
        # числа конфликтов, RSS или свободной RAM не устанавливается.

        bench_winner = _deck_bench_apply(
            solver, model, initial_indices, messages,
        )

        # apply_winner устанавливает НОВЫЙ объект параметров.
        # Последующее включение логов должно менять именно его.
        parameters = solver.parameters
        configured_subsolvers = bench_winner["subsolvers"]
        result["search_profile_id"] = bench_winner["id"]
        result["search_decision"] = bench_winner["decision"]

        # stdout дочернего процесса уже направлен в worker.log.
        # Для отключения подробного лога:
        # DECK_CUSTOM8_LOG=0
        custom8_log = (
            os.environ.get("DECK_CUSTOM8_LOG", "1").strip().lower()
            not in {"0", "false", "no", "off"}
        )
        parameters.log_search_progress = custom8_log
        parameters.log_to_stdout = custom8_log
        parameters.log_subsolver_statistics = custom8_log

        result.update(
            workers=8,
            search_profile=DECK_CUSTOM8_PROFILE,
            configured_subsolvers=list(configured_subsolvers),
            solver_parameters=str(parameters),
        )

        update(
            search_profile=DECK_CUSTOM8_PROFILE,
            configured_subsolvers=list(configured_subsolvers),
        )

        print(
            "CP-SAT configured profile: "
            + DECK_CUSTOM8_PROFILE
            + "; full subsolvers: "
            + ", ".join(configured_subsolvers),
            flush=True,
        )

        current_solver[0] = solver
        check()

        update(
            phase="SOLVE",
            solve_started=time.time(),
            solve_mono=time.monotonic(),
        )

        with contextlib.suppress(Exception):
            atomic_json(progress_path, sample(), durable=False)

        status = solver.solve(model)
        current_solver[0] = None

        result["wall"] = float(solver.wall_time)
        result["conflicts"] = int(solver.num_conflicts)
        result["branches"] = int(solver.num_branches)

        if status == cp_model.INFEASIBLE:
            result["status"] = "UNSAT"
        elif status in (cp_model.FEASIBLE, cp_model.OPTIMAL):
            result["status"] = "SAT"
        elif status == cp_model.UNKNOWN:
            result["status"] = "STOPPED" if stop.is_set() else "UNKNOWN"
        else:
            raise RuntimeError(
                "CP-SAT вернул недопустимый статус:\n"
                + solver.response_stats()
            )

        if result["status"] == "SAT":
            update(phase="EXTRACT")

            positions = [
                int(
                    solver.value(
                        model.get_int_var_from_proto_index(index)
                    )
                )
                for index in initial_indices
            ]

            deck = [0] * n
            for card, position in enumerate(positions):
                deck[position] = card

            inputs = []

            for row in output_indices:
                values = []
                for t, index in enumerate(row):
                    variable = model.get_int_var_from_proto_index(index)
                    value = (
                        int(solver.value(variable)) - t * int(job["s"])
                    ) % n
                    values.append(value)
                inputs.append(values)

            result.update(
                positions=positions,
                deck=deck,
                inputs=inputs,
                message_names=manifest.get(
                    "names",
                    [str(i + 1) for i in range(len(messages))],
                ),
            )

            _reduced_validate_sat(
                result, messages, n,
                int(job["d"]), int(job["s"]), int(job["k"])
            )

    except Halt:
        result["status"] = "STOPPED"
        result["error"] = "Попытка прервана."
    except Exception:
        result["status"] = "ERROR"
        result["error"] = traceback.format_exc()
        traceback.print_exc()
    finally:
        current_solver[0] = None
        finished.set()
        watcher.join(timeout=1.0)

    update(phase="FINISHED")
    final_sample = sample()

    result.update(
        started=started,
        finished=time.time(),
        elapsed=max(0.0, time.monotonic() - began),
        peak_bytes=int(final_sample["peak_bytes"]),
        memory_metric="peak RSS / working set of solver process",
    )

    # Сначала атомарно сохраняется полный результат.
    # Только после этого процесс заканчивается.
    atomic_json(result_path, result, durable=True)

    print(
        f"RESULT {result['status']}; "
        f"elapsed={result['elapsed']:.3f}s; "
        f"peak={result['peak_bytes'] / GIB:.3f} GiB",
        flush=True,
    )

    return 0


# ----------------------------------------------------------------------
# Планировщик и долговременное состояние
# ----------------------------------------------------------------------

def default_plan():
    return {
        "version": 1,
        "generation": "",
        "enabled": False,
        "auto": True,
        "anchors": [],
        "queue": [],
        "retry": None,
        "current": None,
        "seen_red": [],
        "seen_orange": [],
        "deferred": [],
        "message": "Выбери конфигурации и запусти список.",
    }


class Controller:
    def __init__(self, directory, workers):
        self.directory = Path(directory).resolve()
        self.workers = int(workers)
        self.script = Path(__file__).resolve()

        self.data_path = Path(__file__).resolve().with_name("data.csv")

        manifest, self.n, _, self.dataset = read_data_csv(
            self.data_path
        )
        self.fingerprint = manifest.get("fingerprint")

        self.store = self.directory / STORE_NAME
        self.attempts_directory = self.store / "attempts"
        self.attempts_directory.mkdir(parents=True, exist_ok=True)

        self.lock = threading.RLock()
        self.wake = threading.Event()
        self.closing = threading.Event()
        self.force_exit = threading.Event()

        self.rows = {}
        self.positions = {}
        self.warnings = []
        self.files_total = 0

        self.loading = True
        self.ready = False
        self.error = ""

        self.process = None
        self.runtime_start = None
        self.live = {}
        self.peak = 0
        self.deadline = None
        self.cancel_sent = None
        self.runtime_reason = None
        self.emergency_cancel = False
        self.distance_cache = {}

        self.parent_created = psutil.Process().create_time()

        self.db = sqlite3.connect(
            self.store / "control.sqlite3",
            check_same_thread=False,
            timeout=30,
        )
        self.db.execute("PRAGMA journal_mode=WAL")
        self.db.execute("PRAGMA synchronous=FULL")
        self.db.execute(
            "CREATE TABLE IF NOT EXISTS meta "
            "(k TEXT PRIMARY KEY, v TEXT NOT NULL)"
        )
        self.db.execute(
            "CREATE TABLE IF NOT EXISTS records "
            "(file TEXT PRIMARY KEY, v TEXT NOT NULL)"
        )

        previous_dataset = self._meta("dataset")

        if (
            previous_dataset is not None
            and previous_dataset != self.dataset
        ):
            self.db.close()
            raise RuntimeError(
                f"В {STORE_NAME} сохранены результаты для других messages/N. "
                "Не смешивай разные задачи в одной папке. "
                "Старую подпапку можно отдельно архивировать."
            )

        stored_plan = self._meta("plan")
        self.plan = default_plan()

        if stored_plan is not None:
            if not isinstance(stored_plan, dict):
                raise ValueError("Повреждена сохранённая очередь")
            self.plan.update(stored_plan)

        # После перезапуска вычисления не стартуют неожиданно.
        # Сначала восстанавливается текущая попытка, затем пользователь
        # нажимает «Продолжить».
        self.plan["enabled"] = False

        with self.db:
            self.db.execute(
                "INSERT OR REPLACE INTO meta(k,v) VALUES(?,?)",
                ("dataset", json.dumps(self.dataset)),
            )

        self._commit(self.plan)

        self.thread = threading.Thread(
            target=self._loop,
            name="deck-scheduler",
            daemon=True,
        )

    def _meta(self, key):
        row = self.db.execute(
            "SELECT v FROM meta WHERE k=?", (key,)
        ).fetchone()
        return json.loads(row[0]) if row else None

    def _commit(self, plan=None, row=None):
        """Вызывать под self.lock, кроме инициализации до запуска потока."""
        with self.db:
            if row is not None:
                self.db.execute(
                    "INSERT OR REPLACE INTO records(file,v) VALUES(?,?)",
                    (
                        row["file"],
                        json.dumps(
                            row, ensure_ascii=False, allow_nan=False
                        ),
                    ),
                )

            if plan is not None:
                self.db.execute(
                    "INSERT OR REPLACE INTO meta(k,v) VALUES(?,?)",
                    (
                        "plan",
                        json.dumps(
                            plan, ensure_ascii=False, allow_nan=False
                        ),
                    ),
                )

        # Память обновляется только после успешного commit.
        if row is not None:
            self.rows[row["file"]] = row
        if plan is not None:
            self.plan = plan

    def start(self):
        self.thread.start()

    def _workdir(self, current):
        job_id = str(current["id"])
        if not re.fullmatch(r"[0-9a-f]{32}", job_id):
            raise ValueError("Некорректный ID сохранённой попытки")
        return self.attempts_directory / job_id

    def resolve(self, d, s):
        filename = self.positions.get((d, s))

        if filename is None and d != s:
            reflected = ((self.n - d) % self.n, (self.n - s) % self.n)
            filename = self.positions.get(reflected)

        if filename is None:
            raise ValueError(
                f"D={d}, S={s}: нет собственного или отражённого state"
            )

        row = self.rows[filename]
        if not row.get("runnable"):
            raise ValueError(
                f"D={d}, S={s}: файл повреждён, неоднозначен "
                "или содержит конфликт результатов"
            )

        return row

    def command(self, request):
        action = request.get("action")

        with self.lock:
            if self.closing.is_set():
                raise RuntimeError("Сервер останавливается")

            if not self.ready or self.loading:
                raise RuntimeError(
                    self.error or "Ещё выполняется чтение states"
                )

            plan = copy.deepcopy(self.plan)
            current = plan.get("current")

            if action == "start":
                if current is not None or plan["enabled"]:
                    raise RuntimeError(
                        "Сначала поставь текущий план на паузу "
                        "и дождись завершения либо прерви текущую попытку."
                    )

                cells = request.get("cells")
                if not isinstance(cells, list) or not cells:
                    raise ValueError("Список конфигураций пуст")
                if len(cells) > self.n * self.n:
                    raise ValueError("Слишком много элементов списка")

                queue = []
                anchors = []
                seen = set()

                for cell in cells:
                    if not isinstance(cell, dict):
                        raise ValueError("Некорректный элемент списка")

                    d = cell.get("d")
                    s = cell.get("s")

                    if (
                        type(d) is not int
                        or type(s) is not int
                        or not 0 <= d < self.n
                        or not 0 <= s < self.n
                    ):
                        raise ValueError("Некорректные координаты D/S")

                    row = self.resolve(d, s)

                    # Отражение и представитель — одна задача.
                    if row["file"] in seen:
                        continue
                    seen.add(row["file"])

                    queue.append({
                        "file": row["file"],
                        "d": row["d"],
                        "s": row["s"],
                        "k": row["k"],
                        "click_d": d,
                        "click_s": s,
                    })
                    anchors.append({"d": d, "s": s})

                plan = default_plan()
                plan.update(
                    generation=uuid.uuid4().hex,
                    enabled=True,
                    auto=bool(request.get("auto", True)),
                    anchors=anchors,
                    queue=queue,
                    message=(
                        f"Новый план: {len(queue)} ручных конфигураций. "
                        "Для ручного списка время не ограничено."
                    ),
                )
                self.distance_cache.clear()

            elif action == "pause":
                plan["enabled"] = False
                plan["message"] = (
                    "Пауза после текущей попытки. "
                    "Текущий поиск продолжает работать."
                )

            elif action == "resume":
                if current and current.get("cancel"):
                    raise RuntimeError(
                        "Подожди завершения прерывания текущей попытки"
                    )

                if not (
                    plan["queue"] or plan["anchors"] or plan.get("retry")
                ):
                    raise ValueError("Нет сохранённого плана")

                plan["enabled"] = True
                plan["message"] = "Продолжение сохранённого плана."

            elif action in ("stop", "skip"):
                expected = request.get("job_id")
                actual = current["id"] if current else None

                if expected != actual:
                    raise RuntimeError(
                        "Текущая попытка уже сменилась. "
                        "Обнови состояние и повтори команду."
                    )

                if action == "skip" and current is None:
                    raise ValueError("Сейчас ничего не вычисляется")

                if action == "stop":
                    plan["enabled"] = False

                if current is not None:
                    if current.get("cancel"):
                        raise RuntimeError("Попытка уже прерывается")
                    current["cancel"] = action

                plan["message"] = (
                    "Прерывание. Незавершённая задача будет доступна "
                    "для повторного запуска через «Продолжить»."
                    if action == "stop"
                    else "Пропуск текущей задачи в этом плане."
                )

            else:
                raise ValueError("Неизвестная команда")

            self._commit(plan)
            if action in ("start", "resume"):
                self.error = ""
                self.emergency_cancel = False

        self.wake.set()

    def _near(self, row, plan):
        key = (plan["generation"], row["file"])
        cached = self.distance_cache.get(key)
        if cached is not None:
            return cached

        points = [(row["d"], row["s"])]
        reflected = (
            (self.n - row["d"]) % self.n,
            (self.n - row["s"]) % self.n,
        )

        # Отражённая плитка видима как представитель только тогда,
        # когда собственного state на ней нет.
        if reflected not in self.positions and reflected != points[0]:
            points.append(reflected)

        anchors = plan["anchors"]
        choices = []

        for d, s in points:
            distance = min(
                (d - anchor["d"]) ** 2 + (s - anchor["s"]) ** 2
                for anchor in anchors
            ) if anchors else 0

            choices.append((distance, d, s, row["file"]))

        answer = min(choices)
        self.distance_cache[key] = answer
        return answer

    def _pick(self, plan):
        # Ручной список — всегда первый.
        while plan["queue"]:
            task = plan["queue"].pop(0)
            row = self.rows.get(task["file"])

            if (
                row
                and row.get("runnable")
                and all(
                    row.get(key) == task.get(key)
                    for key in ("d", "s", "k")
                )
            ):
                return task, "manual", None

        # Прерванная автоматическая задача сохраняет свой режим/бюджет.
        if plan.get("retry"):
            retry = plan["retry"]
            plan["retry"] = None
            task = retry["task"]
            row = self.rows.get(task["file"])

            if (
                row
                and row.get("runnable")
                and row.get("status") not in TERMINAL
                and all(
                    row.get(key) == task.get(key)
                    for key in ("d", "s", "k")
                )
            ):
                return task, retry["mode"], retry["budget"]

        if not plan["auto"] or not plan["anchors"]:
            return None

        deferred = set(plan["deferred"])

        stages = (
            ("PENDING", "gray", AUTO_SECONDS, set()),
            ("ERROR", "red", AUTO_SECONDS, set(plan["seen_red"])),
            ("UNKNOWN", "orange", None, set(plan["seen_orange"])),
        )

        for status, mode, budget, already_seen in stages:
            candidates = [
                row
                for row in self.rows.values()
                if row.get("runnable")
                and row["status"] == status
                and row["file"] not in deferred
                and row["file"] not in already_seen
            ]

            if not candidates:
                continue

            row = min(
                candidates,
                key=lambda item: self._near(item, plan),
            )
            _, click_d, click_s, _ = self._near(row, plan)

            task = {
                "file": row["file"],
                "d": row["d"],
                "s": row["s"],
                "k": row["k"],
                "click_d": click_d,
                "click_s": click_s,
            }
            return task, mode, budget

        return None

    def _launch(self):
        with self.lock:
            if (
                not self.plan["enabled"]
                or self.plan["current"] is not None
                or self.closing.is_set()
            ):
                return

            plan = copy.deepcopy(self.plan)
            selected = self._pick(plan)

            if selected is None:
                plan["enabled"] = False
                plan["message"] = (
                    "План завершён: нет доступных новых задач. "
                    "Повторные ERROR и явно пропущенные задачи "
                    "в этом автопроходе больше не запускаются."
                )
                self._commit(plan)
                return

            task, mode, budget = selected
            row = self.rows[task["file"]]

            current = {
                **task,
                "id": uuid.uuid4().hex,
                "mode": mode,
                "budget": budget,
                "started": time.time(),
                "seed": max(
                    1, (integer(row.get("attempts")) + 1) % 2147483647
                ),
                "cancel": None,
                "pid": None,
                "created": None,
            }

            workdir = self._workdir(current)
            workdir.mkdir(parents=True, exist_ok=True)

            job = {
                **current,
                "dataset": self.dataset,
                "data_csv": str(self.data_path),
                "workers": self.workers,
                "parent_pid": os.getpid(),
                "parent_created": self.parent_created,
            }

            atomic_json(workdir / "job.json", job)

            plan["current"] = current
            plan["message"] = (
                f"Запуск D={current['d']} S={current['s']} "
                f"K={current['k']}; режим {mode}."
            )

            # Сохранение активной попытки и извлечение из очереди
            # происходят одним SQLite commit.
            self._commit(plan)

            self.live = {}
            self.peak = 0
            self.deadline = None
            self.cancel_sent = None
            self.runtime_reason = None
            self.runtime_start = time.monotonic()
            self.emergency_cancel = False

        options = {}

        if os.name == "nt":
            options["creationflags"] = (
                subprocess.CREATE_NEW_PROCESS_GROUP
                | subprocess.CREATE_NO_WINDOW
            )
        else:
            options["start_new_session"] = True

        try:
            with (workdir / "worker.log").open("ab", buffering=0) as log:
                self.process = subprocess.Popen(
                    [
                        sys.executable,
                        "-u",
                        str(self.script),
                        "--_worker",
                        str(workdir),
                    ],
                    stdin=subprocess.DEVNULL,
                    stdout=log,
                    stderr=subprocess.STDOUT,
                    **options,
                )
        except Exception as exc:
            self.process = None
            self._finish(
                self._synthetic("ERROR", f"Worker не запущен: {exc}")
            )
            return

        created = None
        with contextlib.suppress(psutil.Error):
            created = psutil.Process(self.process.pid).create_time()

        with self.lock:
            plan = copy.deepcopy(self.plan)
            plan["current"]["pid"] = self.process.pid
            plan["current"]["created"] = created
            self._commit(plan)

    def _synthetic(self, status, message):
        with self.lock:
            current = dict(self.plan["current"])
            elapsed = finite(self.live.get("elapsed"))

            if self.runtime_start is not None:
                elapsed = max(
                    elapsed or 0.0,
                    time.monotonic() - self.runtime_start,
                )

            return {
                "job_id": current["id"],
                "dataset": self.dataset,
                "file": current["file"],
                "d": current["d"],
                "s": current["s"],
                "k": current["k"],
                "status": status,
                "started": current["started"],
                "finished": time.time(),
                "elapsed": elapsed,
                "wall": None,
                "peak_bytes": self.peak,
                "error": message,
                "independently_verified": False,
            "model_version": REDUCED_VERSION,
            }

    def _read_result(self, workdir):
        path = workdir / "result.json"
        if not path.exists():
            return None

        try:
            result = read_json(path)
            if not isinstance(result, dict):
                raise ValueError("Ожидался JSON-объект")
            return result
        except Exception as exc:
            return self._synthetic(
                "ERROR",
                f"Не удалось прочитать финальный result.json: {exc}",
            )

    def _monitor(self):
        with self.lock:
            current = dict(self.plan["current"])

        workdir = self._workdir(current)
        process = self.process

        if process is None:
            raise RuntimeError("Нет процесса для активной попытки")

        progress = quiet_json(workdir / "progress.json")

        if progress and progress.get("job_id") == current["id"]:
            with self.lock:
                self.live = progress
                self.peak = max(
                    self.peak,
                    integer(progress.get("peak_bytes")),
                )

            if (
                current["budget"] is not None
                and progress.get("solve_started") is not None
                and self.deadline is None
            ):
                # 600 секунд задаёт сам CP-SAT.
                # Дополнительные 20 секунд — запас на возврат результата.
                remaining = (
                    float(current["budget"])
                    + 20.0
                    - (finite(progress.get("solve_elapsed"), 0.0))
                )
                self.deadline = time.monotonic() + max(0.0, remaining)

        with contextlib.suppress(psutil.Error):
            rss, peak = process_memory(psutil.Process(process.pid))
            with self.lock:
                self.live["rss_bytes"] = rss
                self.peak = max(self.peak, peak)
                self.live["peak_bytes"] = self.peak

        result = self._read_result(workdir)

        if result is not None:
            # Не запускаем следующий тяжёлый процесс, пока предыдущий
            # не завершился. Готовый результат уже сохранён на диске.
            try:
                process.wait(timeout=3.0)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=3.0)

            if (
                self.runtime_reason == "timeout"
                and result.get("status") == "STOPPED"
            ):
                result["status"] = "UNKNOWN"
                result["error"] = (
                    "CP-SAT не вернул результат в пределах 600 секунд "
                    "и дополнительного запаса; поиск остановлен."
                )

            self._finish(result)
            return

        now = time.monotonic()

        with self.lock:
            current = dict(self.plan["current"])

        reason = current.get("cancel")

        if self.closing.is_set() and not reason:
            reason = "stop"
        if self.emergency_cancel and not reason:
            reason = "stop"
        if self.runtime_reason and not reason:
            reason = self.runtime_reason

        if not reason and self.deadline is not None and now >= self.deadline:
            reason = "timeout"
            self.runtime_reason = "timeout"

        # У безлимитных задач self.deadline всегда None.
        # Никакого таймаута построения модели и heartbeat-watchdog нет.

        if reason:
            if self.cancel_sent is None:
                atomic_json(
                    workdir / "cancel.json",
                    {"reason": reason, "time": time.time()},
                    durable=False,
                )
                self.cancel_sent = now

            if now - self.cancel_sent > 10.0 and process.poll() is None:
                process.kill()

        code = process.poll()

        if code is not None:
            # Закрываем гонку: файл мог появиться непосредственно
            # перед завершением процесса.
            result = self._read_result(workdir)

            if result is None:
                if reason == "timeout":
                    status = "UNKNOWN"
                    message = "Попытка остановлена по 600-секундному бюджету."
                elif reason in ("stop", "skip"):
                    status = "STOPPED"
                    message = "Попытка прервана по команде пользователя."
                else:
                    status = "ERROR"
                    message = (
                        "Вычислительный процесс завершился без результата. "
                        f"exitcode={code}, hex=0x{code & 0xffffffff:08X}. "
                        f"Подробности: {workdir / 'worker.log'}"
                    )

                result = self._synthetic(status, message)

            if (
                reason == "timeout"
                and result.get("status") == "STOPPED"
            ):
                result["status"] = "UNKNOWN"

            self._finish(result)

    def _finish(self, result):
        with self.lock:
            current = dict(self.plan["current"])

        valid = (
            result.get("job_id") == current["id"]
            and result.get("dataset") == self.dataset
            and result.get("file") == current["file"]
            and all(
                result.get(key) == current.get(key)
                for key in ("d", "s", "k")
            )
            and result.get("status") in RESULT_STATUSES
        )

        if not valid:
            result = self._synthetic(
                "ERROR",
                "Некорректный или несовместимый результат worker. "
                "Исходный result.json оставлен для диагностики.",
            )
        else:
            result = dict(result)

        result["elapsed"] = finite(result.get("elapsed"))
        result["wall"] = finite(result.get("wall"))
        result["peak_bytes"] = max(
            self.peak,
            max(0, integer(result.get("peak_bytes"))),
        )
        result["mode"] = current["mode"]
        result["limit_seconds"] = current["budget"]

        outcome_path = self._workdir(current) / "outcome.json"
        atomic_json(outcome_path, result)
        reference = outcome_path.relative_to(self.directory).as_posix()

        with self.lock:
            plan = copy.deepcopy(self.plan)
            current = plan["current"]
            action = current.get("cancel")

            if self.closing.is_set() and not action:
                action = "stop"

            name = result["status"]
            terminal = name in TERMINAL
            previous = self.rows.get(current["file"])
            row = copy.deepcopy(previous) if previous else None

            if row is not None:
                row["attempts"] = integer(row.get("attempts")) + 1
                row["attempts_new"] = integer(row.get("attempts_new")) + 1
                row["last_job_id"] = current["id"]
                row["last_model_version"] = result.get("model_version", "legacy")
                if row.get("resolved") not in TERMINAL:
                    row["legacy_result"] = (
                        row["last_model_version"] != REDUCED_VERSION
                    )
                row["last_status"] = name
                row["raw_status"] = name
                row["elapsed"] = result["elapsed"]
                row["wall"] = result["wall"]
                row["peak_bytes"] = result["peak_bytes"]
                row["last_result_file"] = reference
                row["error"] = str(result.get("error") or "")[:4000]

                old_terminal = row.get("resolved")

                if (
                    terminal
                    and old_terminal in TERMINAL
                    and old_terminal != name
                ):
                    row["status"] = "ERROR"
                    row["runnable"] = False
                    row["error"] = (
                        f"КОНФЛИКТ: ранее {old_terminal}, теперь {name}. "
                        "Оба результата сохранены. Нужна проверка."
                    )
                    plan["enabled"] = False
                elif terminal:
                    row["status"] = name
                    row["resolved"] = name
                    row["result_model_version"] = result.get("model_version", "legacy")
                    row["legacy_result"] = (
                        row["result_model_version"] != REDUCED_VERSION
                    )
                    row["solution_file"] = reference
                    row["note"] = (
                        "Новый результат REDUCED для всей конфигурации. "
                        "Без assumptions и splits; SAT проверяется симулятором."
                    )
                else:
                    # Незавершённая перепроверка не отменяет уже
                    # сохранённый SAT/UNSAT.
                    row["status"] = (
                        old_terminal if old_terminal in TERMINAL
                        else "ERROR" if name == "ERROR"
                        else "UNKNOWN"
                    )

                    if old_terminal in TERMINAL:
                        row["note"] = (
                            f"Последняя перепроверка: {name}. "
                            f"Прежний результат {old_terminal} сохранён."
                        )

                # Метки сложности — только по завершённым SAT/UNSAT.
                # Не по сумме попыток и не по времени нахождения в очереди.
                if terminal:
                    row["solved_peak_bytes"] = maximum_known(
                        row.get("solved_peak_bytes"),
                        result["peak_bytes"],
                    )
                    row["solved_elapsed"] = maximum_known(
                        row.get("solved_elapsed"),
                        result["elapsed"],
                    )
                    row["hard_memory"] = bool(
                        row.get("hard_memory")
                        or result["peak_bytes"] > HARD_MEMORY
                    )
                    row["hard_time"] = bool(
                        row.get("hard_time")
                        or (
                            result["elapsed"] is not None
                            and result["elapsed"] > HARD_SECONDS
                        )
                    )

            task = {
                key: current[key]
                for key in (
                    "file", "d", "s", "k", "click_d", "click_s"
                )
            }

            if action == "stop" and not terminal:
                if current["mode"] == "manual":
                    plan["queue"].insert(0, task)
                else:
                    plan["retry"] = {
                        "task": task,
                        "mode": current["mode"],
                        "budget": current["budget"],
                    }

            elif action == "skip":
                if current["file"] not in plan["deferred"]:
                    plan["deferred"].append(current["file"])

            else:
                if current["mode"] == "red":
                    if current["file"] not in plan["seen_red"]:
                        plan["seen_red"].append(current["file"])

                if current["mode"] == "orange":
                    if current["file"] not in plan["seen_orange"]:
                        plan["seen_orange"].append(current["file"])

            if result.get("fatal_input"):
                plan["enabled"] = False
                self.error = (
                    "Входные данные изменились. "
                    "Восстанови исходный data.csv и перезапусти сервер."
                )

            plan["current"] = None
            plan["message"] = (
                f"D={current['d']} S={current['s']} K={current['k']} "
                f"→ {name}. "
                + (
                    "Незавершённая задача сохранена для повторного запуска."
                    if action == "stop" and not terminal else ""
                )
            )

            # Результат конфигурации и продвижение очереди сохраняются
            # одним commit. Повторное восстановление не удваивает попытки.
            self._commit(plan, row)

            self.process = None
            self.runtime_start = None
            self.live = {}
            self.peak = 0
            self.deadline = None
            self.cancel_sent = None
            self.runtime_reason = None

        print(
            f"[{time.strftime('%H:%M:%S')}] "
            f"D={current['d']} S={current['s']} K={current['k']} "
            f"-> {name}",
            flush=True,
        )

    def _recover(self):
        with self.lock:
            current = copy.deepcopy(self.plan.get("current"))

        if current is None:
            return

        workdir = self._workdir(current)

        # Старый worker либо уже закончил, либо должен остановиться.
        atomic_json(
            workdir / "cancel.json",
            {"reason": "server_restart", "time": time.time()},
            durable=False,
        )

        progress = quiet_json(workdir / "progress.json") or {}
        pid = current.get("pid") or progress.get("pid")
        created = current.get("created") or progress.get("created")

        if pid:
            try:
                process = psutil.Process(int(pid))
                arguments = process.cmdline()

                same_creation = (
                    created is None
                    or abs(process.create_time() - float(created)) < 0.02
                )
                same_job = (
                    "--_worker" in arguments
                    and str(workdir) in arguments
                )

                # Не трогаем посторонний процесс при повторном
                # использовании PID операционной системой.
                if same_creation and same_job:
                    try:
                        process.wait(timeout=6.0)
                    except psutil.TimeoutExpired:
                        process.kill()
                        process.wait(timeout=4.0)

            except psutil.NoSuchProcess:
                pass
            except psutil.AccessDenied as exc:
                raise RuntimeError(
                    "Не удалось проверить старый вычислительный процесс. "
                    "Проверь его в Диспетчере задач."
                ) from exc

        self.live = progress
        self.peak = integer(progress.get("peak_bytes"))

        result = self._read_result(workdir)

        if result is None:
            result = self._synthetic(
                "STOPPED",
                "Попытка не завершилась до перезапуска сервера.",
            )

        with self.lock:
            plan = copy.deepcopy(self.plan)
            plan["enabled"] = False

            if (
                result.get("status") == "STOPPED"
                and not plan["current"].get("cancel")
            ):
                plan["current"]["cancel"] = "stop"

            self._commit(plan)

        self._finish(result)

    def _on_error(self, exc):
        traceback.print_exc()

        with self.lock:
            self.error = f"{type(exc).__name__}: {exc}"
            self.emergency_cancel = True

            plan = copy.deepcopy(self.plan)
            plan["enabled"] = False

            if plan.get("current") and not plan["current"].get("cancel"):
                plan["current"]["cancel"] = "stop"

            try:
                self._commit(plan)
            except Exception:
                # Даже при неисправном диске прекращаем запуск новых задач.
                # Сохранённая current и result/outcome позволят повторить
                # восстановление после устранения проблемы.
                self.plan = plan

    def _loop(self):
        try:
            saved_records = {
                filename: json.loads(value)
                for filename, value in self.db.execute(
                    "SELECT file,v FROM records"
                )
            }

            rows, warnings, files_total = load_catalog(
                self.directory,
                self.n,
                self.fingerprint,
                saved_records,
            )

            with self.lock:
                self.rows = rows
                self.positions = {
                    (row["d"], row["s"]): row["file"]
                    for row in rows.values()
                }
                self.warnings = warnings
                self.files_total = files_total

            self._recover()

            with self.lock:
                self.ready = True

        except Exception as exc:
            traceback.print_exc()
            with self.lock:
                self.error = f"Ошибка загрузки: {type(exc).__name__}: {exc}"
                self.ready = False
        finally:
            with self.lock:
                self.loading = False

        while not self.force_exit.is_set():
            with self.lock:
                ready = self.ready
                current = self.plan.get("current")
                enabled = self.plan["enabled"]

            if not ready:
                if self.closing.wait(0.25):
                    break
                continue

            if self.closing.is_set() and current is None:
                break

            try:
                if current is not None:
                    self._monitor()
                elif enabled and not self.closing.is_set():
                    self._launch()
            except Exception as exc:
                self._on_error(exc)

            self.wake.wait(0.25)
            self.wake.clear()

    def snapshot(self):
        with self.lock:
            rows = [copy.deepcopy(row) for row in self.rows.values()]
            plan = copy.deepcopy(self.plan)
            live = dict(self.live)

            current = plan.get("current")
            if current:
                for row in rows:
                    if row["file"] == current["file"]:
                        row["status"] = "RUNNING"
                        break

                if self.runtime_start is not None:
                    live["elapsed"] = max(
                        finite(live.get("elapsed"), 0.0),
                        time.monotonic() - self.runtime_start,
                    )

                live["peak_bytes"] = max(
                    integer(live.get("peak_bytes")),
                    self.peak,
                )

            return {
                "loading": self.loading,
                "ready": self.ready,
                "error": self.error,
                "folder": str(self.directory),
                "store": str(self.store),
                "n": self.n,
                "dataset": self.dataset,
                "workers": self.workers,
                "files": self.files_total,
                "rows": rows,
                "counts": dict(Counter(row["status"] for row in rows)),
                "plan": plan,
                "live": live,
                "warnings": self.warnings[:30],
                "refreshed": time.time(),
            }

    def result_path(self, filename, solution=False):
        with self.lock:
            row = self.rows.get(filename)
            if row is None:
                raise ValueError("Неизвестная конфигурация")

            reference = row.get(
                "solution_file" if solution else "last_result_file"
            )

        if not reference:
            raise ValueError("Файла результата пока нет")

        path = (self.directory / reference).resolve()

        if path != self.directory / "SAT.json":
            if not path.is_relative_to(self.store.resolve()):
                raise ValueError("Недопустимый путь результата")

        return path

    def close(self):
        self.closing.set()

        with self.lock:
            plan = copy.deepcopy(self.plan)
            plan["enabled"] = False

            if plan.get("current") and not plan["current"].get("cancel"):
                plan["current"]["cancel"] = "stop"

            try:
                self._commit(plan)
            except Exception:
                self.plan = plan

        self.wake.set()

        if self.thread.ident is not None:
            self.thread.join(timeout=20.0)

        if self.thread.is_alive():
            process = self.process
            if process is not None and process.poll() is None:
                with contextlib.suppress(Exception):
                    process.kill()
                    process.wait(timeout=3.0)

            self.force_exit.set()
            self.wake.set()
            self.thread.join(timeout=2.0)

        if not self.thread.is_alive():
            with self.lock:
                self.db.close()


# ----------------------------------------------------------------------
# Браузерный интерфейс. Все CSS/JS находятся в этом же Python-файле.
# ----------------------------------------------------------------------

HTML = r"""<!doctype html>
<html lang="ru">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Deck · D × S</title>
<style>
:root{color-scheme:dark}
*{box-sizing:border-box}
body{margin:0;height:100vh;overflow:hidden;display:flex;flex-direction:column;
background:#080f1c;color:#e2e8f0;font:14px system-ui,-apple-system,"Segoe UI",sans-serif}
header{padding:10px 14px;background:#111827;border-bottom:1px solid #334155}
h1{font-size:18px;margin:0 0 5px}
.badge{font-size:11px;color:#86efac;margin-left:12px}
#path,#live{font-size:12px;color:#94a3b8;overflow-wrap:anywhere}
#path{font-family:monospace}
#live{margin-top:5px}
.bad{color:#fca5a5!important}
.toolbar{display:flex;align-items:center;gap:7px;flex-wrap:wrap;margin-top:8px}
button,input{font:inherit;color:inherit;background:#1e293b;border:1px solid #475569;
border-radius:5px;padding:5px 8px}
button{cursor:pointer}
button:hover:not(:disabled){background:#334155}
button:disabled{opacity:.4;cursor:default}
button.primary{background:#14532d;border-color:#22c55e}
button.danger{border-color:#ef4444}
input[type=number]{width:64px}
input[type=checkbox]{vertical-align:middle}
form{display:flex;align-items:center;gap:5px;margin:0}
#zoom{font-size:12px;color:#94a3b8;min-width:75px}
#legend{display:flex;gap:7px 13px;flex-wrap:wrap;margin-top:8px;font-size:12px}
.chip{display:inline-flex;align-items:center;gap:5px}
.swatch{width:13px;height:13px;border-radius:3px;border:1px solid #ffffff30}
#layout{flex:1;min-height:0;display:grid;grid-template-columns:minmax(0,1fr) 350px}
#plot{position:relative;min-width:0;min-height:0;overflow:hidden}
canvas{position:absolute;inset:0;display:block;width:100%;height:100%;touch-action:none;cursor:grab}
aside{overflow:auto;padding:13px;border-left:1px solid #334155;background:#0f172a}
aside h2{font-size:14px;margin:15px 0 8px}
aside h2:first-child{margin-top:0}
pre{font:12px/1.5 ui-monospace,Consolas,monospace;white-space:pre-wrap;overflow-wrap:anywhere}
#details{font-size:12px;margin:0}
#raw,#runInfo{color:#cbd5e1}
.help,small{font-size:12px;color:#94a3b8;line-height:1.55}
#warnings{color:#fbbf24}
#draft{display:flex;flex-direction:column;gap:4px;max-height:280px;overflow:auto;margin-top:8px}
.qitem{display:flex;gap:3px;align-items:center;padding:4px;background:#182336;border-radius:4px}
.qitem span{flex:1;font:12px monospace;cursor:pointer}
.qitem button{padding:2px 6px}
details{margin-top:10px}
summary{cursor:pointer;color:#94a3b8}
a{color:#7dd3fc}
#tip{display:none;position:fixed;pointer-events:none;z-index:10;max-width:430px;
max-height:70vh;overflow:hidden;white-space:pre-wrap;padding:10px 12px;
border:1px solid #64748b;border-radius:7px;background:#020617f5;color:#f1f5f9;
box-shadow:0 8px 30px #0008;font:12px/1.5 ui-monospace,Consolas,monospace}
@media(max-width:850px){#layout{grid-template-columns:minmax(0,1fr) 275px}}
</style>
</head>
<body>
<header>
<h1>Deck · D × S
<span class="badge">REDUCED · целые конфигурации · управление</span></h1>
<div id="path"></div>
<div id="live">Подключение…</div>

<div class="toolbar">
<button id="fit">Вся сетка</button>
<button id="zout">−</button><button id="zin">+</button>
<span id="zoom"></span>
<button id="running" disabled>К текущему расчёту</button>
<label><input id="numbers" type="checkbox" checked> K</label>
<label><input id="marks" type="checkbox" checked> M/T</label>
<label><input id="queueMode" type="checkbox" checked> Клики → список</label>
<form id="go">
<label>D <input id="goD" type="number" min="0" value="0" required></label>
<label>S <input id="goS" type="number" min="0" value="1" required></label>
<button type="submit">Перейти</button>
</form>
</div>

<div class="toolbar">
<button id="start" class="primary" disabled>Запустить новый список</button>
<button id="resume" disabled>Продолжить</button>
<button id="pause" disabled>Пауза после текущей</button>
<button id="stop" class="danger" disabled>Прервать и сохранить очередь</button>
<button id="skip" disabled>Пропустить текущую</button>
</div>

<div id="legend"></div>
<div class="help" style="margin-top:5px">
<span style="color:#22d3ee">◢ M: &gt;8 GiB RSS</span> ·
<span style="color:#f472b6">◤ T: &gt;1 часа</span> ·
оба угла — оба условия. Метки относятся к завершённым SAT/UNSAT.
</div>
</header>

<div id="layout">
<div id="plot"><canvas id="canvas"></canvas></div>
<aside>
<h2>Выполняемый план</h2>
<pre id="runInfo">Ожидание данных…</pre>

<h2>Новый список: <span id="qcount">0</span></h2>
<div class="help">
Клики добавляют ячейки по порядку. Повторный клик убирает их.
Этот список не изменяет уже запущенный план.
</div>
<label class="help">
<input id="auto" type="checkbox" checked>
После ручного списка — автоматический поиск
</label>
<div id="draft"></div>
<div class="toolbar">
<button id="clearDraft">Очистить список</button>
<button id="addSelected" disabled>Добавить/убрать выбранную</button>
</div>

<h2 id="selectionTitle">Плитка</h2>
<pre id="details">Наведи курсор на ячейку.</pre>
<div class="toolbar">
<button id="mirror" disabled>К отражению</button>
<button id="unpin" disabled>Снять выбор</button>
</div>
<div class="toolbar">
<a id="lastResult" hidden target="_blank" rel="noopener">Последняя попытка JSON</a>
<a id="solution" hidden target="_blank" rel="noopener">Результат SAT/UNSAT</a>
</div>

<details>
<summary>Сводка сохранённой записи</summary>
<pre id="raw"></pre>
</details>

<div class="help" style="margin-top:14px">
<b>Строки — D, столбцы — S.</b><br>
Колёсико — масштаб к курсору. Перетаскивание — перемещение.<br>
Клик закрепляет ячейку; при включённом «Клики → список» также меняет список.
Shift+клик меняет список независимо от переключателя.<br><br>
Штриховка — отражение существующего state, а не отдельная задача.
Один представитель и его отражение не дублируются в очереди.<br><br>
Серый PENDING — существующий state без результата.
Тёмный MISSING — state отсутствует; автоматически он не создаётся.<br><br>
Ручной список и оранжевые задачи не имеют лимита времени.
Для серых и красных 600 секунд относятся к CP-SAT; построение модели
отдельным таймаутом не ограничивается.<br><br>
«Прервать» не сохраняет внутреннее дерево поиска CP-SAT:
незавершённая попытка потом начнётся заново.
«Пропустить» исключает ячейку из оставшейся части этого плана.<br><br>
Вручную можно выбрать и уже решённую ячейку для перепроверки.
Автоматически SAT/UNSAT не пересчитываются.<br><br>
Для старых результатов пик RAM обычно неизвестен:
отсутствие M не означает доказанное потребление меньше 8 GiB.
</div>
<pre id="warnings"></pre>
</aside>
</div>
<div id="tip"></div>

<script>
"use strict";
const TOKEN = __DECK_TOKEN__;
const $ = id => document.getElementById(id);
const canvas = $("canvas"), ctx = canvas.getContext("2d"), tip = $("tip");
const COLORS = {
 UNSAT:"#166534", UNKNOWN:"#a16207", ERROR:"#b91c1c",
 RUNNING:"#1d4ed8", SAT:"#7c3aed", PENDING:"#334155",
 MISSING:"#111827", EXCLUDED:"#080d16"
};
function reducedCellColor(status, legacy){
  const base=COLORS[status]||COLORS.UNKNOWN;
  if(!legacy||status==="RUNNING")return base;
  const value=parseInt(base.slice(1),16);
  const rgb=[(value>>16)&255,(value>>8)&255,value&255];
  return "rgb("+rgb.map(x=>Math.round(x*.75+112*.25)).join(",")+")";
}

const LABELS = {
 UNSAT:"UNSAT", UNKNOWN:"UNKNOWN", ERROR:"ERROR", RUNNING:"В процессе",
 SAT:"SAT", PENDING:"OPEN / нет результата", MISSING:"Нет state",
 EXCLUDED:"Нет K ≥ 1"
};
const MODES = {
 manual:"Ручной список", gray:"Ближайшая серая",
 red:"Повтор красной", orange:"Безлимитная оранжевая"
};
const L=48, T=32, GiB=1024**3;
let data=null, n=0, byId=new Map(), cells=[];
let W=1,H=1,ratio=1,z=12,ox=48,oy=32,fitted=false;
let selected=null,hover=null,lastPointer=null,drag=null,paintPending=false;
let draft=[],draftDataset=null,busy=false,online=false;

const idx=(d,s)=>d*n+s;
const reflect=(d,s)=>[(n-d)%n,(n-s)%n];
const bound=(d,s)=>{const q=((d-s)%n+n)%n;return Math.min(q,n-q)};
const getCell=p=>p?cells[idx(p.d,p.s)]:null;
const duration=v=>{
 if(v==null)return "—";
 let x=Math.max(0,Math.floor(v)),h=Math.floor(x/3600);
 let m=Math.floor(x%3600/60),s=x%60;
 return `${h}:${String(m).padStart(2,"0")}:${String(s).padStart(2,"0")}`;
};
const memory=v=>v==null?"не измерялось":(v/GiB).toFixed(3)+" GiB";

const hc=document.createElement("canvas");
hc.width=hc.height=8;
const hx=hc.getContext("2d");
hx.strokeStyle="rgba(255,255,255,.35)";
hx.beginPath();hx.moveTo(-2,8);hx.lineTo(8,-2);
hx.moveTo(6,10);hx.lineTo(10,6);hx.stroke();
const hatch=ctx.createPattern(hc,"repeat");

function saveDraft(){
 if(!draftDataset)return;
 try{localStorage.setItem("deck-draft-"+draftDataset,JSON.stringify(draft))}
 catch(e){}
}
function renderDraft(){
 $("qcount").textContent=draft.length;
 $("draft").replaceChildren();
 draft.forEach((p,i)=>{
  const c=getCell(p),box=document.createElement("div");
  box.className="qitem";
  const text=document.createElement("span");
  text.textContent=`${i+1}. D=${p.d} S=${p.s} K=${c?.row?.k??"?"}`;
  text.onclick=()=>jump(p.d,p.s);
  box.append(text);
  const button=(label,fn,disabled=false)=>{
   const b=document.createElement("button");
   b.textContent=label;b.disabled=disabled;b.onclick=fn;box.append(b);
  };
  const changed=()=>{saveDraft();renderDraft();repaint();updateButtons()};
  button("↑",()=>{[draft[i-1],draft[i]]=[draft[i],draft[i-1]];changed()},i===0);
  button("↓",()=>{[draft[i+1],draft[i]]=[draft[i],draft[i+1]];changed()},i===draft.length-1);
  button("×",()=>{draft.splice(i,1);changed()});
  $("draft").append(box);
 });
 updateButtons();
}
function toggleDraft(p){
 const c=getCell(p);
 if(!c?.row?.runnable){
  alert("Эта ячейка не запускается: нет корректного однозначного state.");
  return;
 }
 const i=draft.findIndex(x=>x.file===c.row.file);
 if(i>=0)draft.splice(i,1);
 else draft.push({d:p.d,s:p.s,file:c.row.file});
 saveDraft();renderDraft();repaint();
}
function describe(c,full=false){
 if(!c)return "Наведи курсор на ячейку.";
 const r=c.row,[rd,rs]=reflect(c.d,c.s);
 const lines=[
  `D=${c.d}  S=${c.s}`,
  `Статус: ${LABELS[c.status]||c.status}`,
  `K из state: ${r?.k??"нет"}`,
  `Граница INPUT_RULE: K ≤ ${c.limit}`,
  `Отражение: D=${rd}, S=${rs}`
 ];
 if(r?.legacy_result)lines.push("Результат предыдущей версии: сероватый оттенок.");
 if(c.kind==="reflection")
  lines.push(`ШТРИХОВКА: представитель D=${r.d}, S=${r.s}. Это та же задача.`);
 if(c.kind==="missing")lines.push("Нет собственного или отражённого state.");
 if(r){
  lines.push("Файл: "+r.file);
  const types=[];
  if(r.hard_memory)types.push("M — больше 8 GiB");
  if(r.hard_time)types.push("T — больше часа");
  if(types.length)lines.push("Сложность: "+types.join("; "));
  if(full){
   lines.push("Попыток: "+(r.attempts??0));
   if(r.last_status)lines.push("Последняя попытка: "+r.last_status);
   lines.push("Время последней попытки: "+duration(r.elapsed));
   lines.push("CP-SAT wall: "+(r.wall==null?"—":r.wall.toFixed(3)+" с"));
   lines.push("Пик RSS последней попытки: "+memory(r.peak_bytes));
   lines.push("Макс. время завершённых SAT/UNSAT: "+duration(r.solved_elapsed));
   lines.push("Макс. пик завершённых SAT/UNSAT: "+memory(r.solved_peak_bytes));
  }
  if(r.note)lines.push(r.note);
  if(r.error)lines.push(full?r.error:r.error.slice(0,350));
 }
 return lines.join("\n");
}
function updatePanel(){
 const c=getCell(selected||hover),r=c?.row;
 $("selectionTitle").textContent=selected?"Закреплённая плитка":"Плитка";
 $("details").textContent=describe(c,true);
 $("raw").textContent=r?JSON.stringify(r,null,2):"Нет записи.";
 $("mirror").disabled=!selected;
 $("unpin").disabled=!selected;
 $("addSelected").disabled=!selected||!getCell(selected)?.row?.runnable;
 for(const [id,field,kind] of [
  ["lastResult","last_result_file","last"],
  ["solution","solution_file","solution"]
 ]){
  $(id).hidden=!r?.[field];
  if(r?.[field])$(id).href="/api/result?file="+encodeURIComponent(r.file)+"&kind="+kind;
 }
}
function tooltip(c,p){
 if(!c||!p||drag){tip.style.display="none";return}
 tip.textContent=describe(c);
 tip.style.display="block";
 tip.style.left=Math.max(8,Math.min(p.cx+14,innerWidth-tip.offsetWidth-10))+"px";
 tip.style.top=Math.max(8,Math.min(p.cy+14,innerHeight-tip.offsetHeight-10))+"px";
}
function point(e){
 const r=canvas.getBoundingClientRect();
 return {x:e.clientX-r.left,y:e.clientY-r.top,cx:e.clientX,cy:e.clientY};
}
function hit(p){
 if(!data||data.loading||!p||p.x<L||p.y<T||p.x>=W||p.y>=H)return null;
 const s=Math.floor((p.x-ox)/z),d=Math.floor((p.y-oy)/z);
 return d>=0&&s>=0&&d<n&&s<n?{d,s}:null;
}
function refreshHover(){
 hover=drag?null:hit(lastPointer);
 tooltip(getCell(hover),lastPointer);
 updatePanel();
}
function repaint(){
 if(paintPending)return;
 paintPending=true;
 requestAnimationFrame(()=>{paintPending=false;draw()});
}
function fit(){
 if(!n||W<80||H<80)return;
 z=Math.max(.5,Math.min((W-L-16)/n,(H-T-16)/n,180));
 ox=L+(W-L-n*z)/2;oy=T+(H-T-n*z)/2;
 fitted=true;refreshHover();repaint();
}
function zoom(factor,x=(L+W)/2,y=(T+H)/2){
 if(!n)return;
 const next=Math.max(.5,Math.min(180,z*factor));
 ox=x-(x-ox)*next/z;oy=y-(y-oy)*next/z;z=next;
 refreshHover();repaint();
}
function jump(d,s){
 if(!Number.isInteger(d)||!Number.isInteger(s)||d<0||s<0||d>=n||s>=n)return;
 selected={d,s};z=Math.max(z,32);
 ox=(L+W)/2-(s+.5)*z;oy=(T+H)/2-(d+.5)*z;
 fitted=true;$("goD").value=d;$("goS").value=s;
 refreshHover();repaint();
}
function resize(){
 W=canvas.clientWidth;H=canvas.clientHeight;ratio=devicePixelRatio||1;
 canvas.width=Math.max(1,Math.round(W*ratio));
 canvas.height=Math.max(1,Math.round(H*ratio));
 if(data&&!data.loading&&!fitted)fit();
 repaint();
}
function outline(p,color,width,dashed=false){
 if(!p)return;
 ctx.strokeStyle=color;ctx.lineWidth=width;ctx.setLineDash(dashed?[5,3]:[]);
 ctx.strokeRect(ox+p.s*z+.5,oy+p.d*z+.5,Math.max(.2,z-1),Math.max(.2,z-1));
 ctx.setLineDash([]);
}
function draw(){
 ctx.setTransform(ratio,0,0,ratio,0,0);
 ctx.fillStyle="#080f1c";ctx.fillRect(0,0,W,H);
 if(!data||data.loading||!cells.length){
  ctx.fillStyle="#94a3b8";ctx.font="15px system-ui";ctx.textAlign="center";
  ctx.fillText(data?.error||"Первое чтение states…",W/2,H/2);
  return;
 }
 const d0=Math.max(0,Math.floor((T-oy)/z)),d1=Math.min(n-1,Math.floor((H-oy)/z));
 const s0=Math.max(0,Math.floor((L-ox)/z)),s1=Math.min(n-1,Math.floor((W-ox)/z));
 const gap=z>=8?1:0,showNumbers=$("numbers").checked&&z>=18;
 const draftNumbers=new Map(draft.map((p,i)=>[idx(p.d,p.s),i+1]));
 const anchors=new Set((data.plan.anchors||[]).map(p=>idx(p.d,p.s)));

 ctx.save();ctx.beginPath();ctx.rect(L,T,Math.max(0,W-L),Math.max(0,H-T));ctx.clip();
 ctx.textAlign="center";ctx.textBaseline="middle";

 for(let d=d0;d<=d1;d++)for(let s=s0;s<=s1;s++){
  const c=cells[idx(d,s)],r=c.row,x=ox+s*z,y=oy+d*z;
  ctx.fillStyle=reducedCellColor(c.status,r?.legacy_result);
  ctx.fillRect(x+gap/2,y+gap/2,z-gap,z-gap);
  if(c.kind==="reflection"){
   ctx.fillStyle=hatch;ctx.fillRect(x+gap/2,y+gap/2,z-gap,z-gap);
  }
  if($("marks").checked&&r){
   const a=Math.max(1.5,z*.30);
   if(r.hard_memory){
    ctx.fillStyle="#22d3ee";ctx.beginPath();
    ctx.moveTo(x,y);ctx.lineTo(x+a,y);ctx.lineTo(x,y+a);ctx.closePath();ctx.fill();
   }
   if(r.hard_time){
    ctx.fillStyle="#f472b6";ctx.beginPath();
    ctx.moveTo(x+z,y+z);ctx.lineTo(x+z-a,y+z);ctx.lineTo(x+z,y+z-a);
    ctx.closePath();ctx.fill();
   }
  }
  if(showNumbers){
   ctx.font=`${Math.max(8,Math.min(14,z*.36))}px ui-monospace,Consolas,monospace`;
   ctx.fillStyle=c.kind==="excluded"?"#475569":"#f8fafc";
   const text=r?.k!=null?String(r.k):c.kind==="excluded"?"—":c.kind==="missing"?"≤"+c.limit:"?";
   ctx.fillText(text,x+z/2,y+z/2);
  }
  const q=draftNumbers.get(idx(d,s));
  if(q){
   outline({d,s},"#fbbf24",Math.max(1,Math.min(2,z*.15)));
   if(z>=28){
    ctx.font="bold 10px monospace";ctx.fillStyle="#fef08a";
    ctx.textAlign="right";ctx.textBaseline="top";
    ctx.fillText("#"+q,x+z-2,y+2);
    ctx.textAlign="center";ctx.textBaseline="middle";
   }
  }else if(anchors.has(idx(d,s))){
   outline({d,s},"#fef08a",1,true);
  }
 }
 const focus=selected||hover;
 if(focus){
  const [d,s]=reflect(focus.d,focus.s);
  if(d!==focus.d||s!==focus.s)outline({d,s},"#e879f9",2,true);
 }
 outline(selected,"#fff",2.5);
 outline(hover,"#67e8f9",1.5);
 ctx.restore();

 ctx.fillStyle="#111827";ctx.fillRect(0,0,W,T);ctx.fillRect(0,T,L,Math.max(0,H-T));
 ctx.font="11px ui-monospace,Consolas,monospace";
 ctx.textAlign="center";ctx.textBaseline="middle";ctx.fillStyle="#94a3b8";
 const step=z>=24?1:z>=7?5:z>=3?10:20;
 for(let s=Math.ceil(s0/step)*step;s<=s1;s+=step){
  const x=ox+(s+.5)*z;if(x>=L&&x<W)ctx.fillText(String(s),x,T/2);
 }
 for(let d=Math.ceil(d0/step)*step;d<=d1;d+=step){
  const y=oy+(d+.5)*z;if(y>=T&&y<H)ctx.fillText(String(d),L/2,y);
 }
 ctx.fillStyle="#e2e8f0";ctx.font="10px monospace";ctx.fillText("D↓ S→",L/2,T/2);
 $("zoom").textContent=z.toFixed(1)+" px/яч.";
}
function updateLegend(){
 $("legend").replaceChildren();
 const chip=(text,color)=>{
  const box=document.createElement("span");box.className="chip";
  const square=document.createElement("i");square.className="swatch";
  square.style.background=color;
  const label=document.createElement("span");label.textContent=text;
  box.append(square,label);$("legend").append(box);
 };
 for(const status of ["UNSAT","UNKNOWN","ERROR","RUNNING","SAT","PENDING"])
  chip(`${LABELS[status]}: ${data.counts[status]||0}`,COLORS[status]);
 chip("MISSING: "+cells.filter(c=>c.kind==="missing").length,COLORS.MISSING);
 chip("Результаты прошлой версии: "+data.rows.filter(r=>r.legacy_result).length,"#7b8492");
 let m=0,t=0,both=0;
 for(const r of data.rows){
  if(r.hard_memory&&r.hard_time)both++;
  else if(r.hard_memory)m++;
  else if(r.hard_time)t++;
 }
 chip("Тип 1 M: "+m,"#22d3ee");
 chip("Тип 2 T: "+t,"#f472b6");
 chip("Тип 3 M+T: "+both,"linear-gradient(135deg,#22d3ee 50%,#f472b6 50%)");
}
function updateButtons(){
 const p=data?.plan,c=p?.current;
 const ok=online&&data?.ready&&!data?.loading&&!busy;
 $("start").disabled=!ok||!draft.length||!!c||!!p?.enabled;
 $("resume").disabled=!ok||!!p?.enabled||!!c?.cancel||
  !(p?.queue?.length||p?.retry||p?.anchors?.length);
 $("pause").disabled=!ok||!p?.enabled;
 $("stop").disabled=!ok||(!c&&!p?.enabled)||!!c?.cancel;
 $("skip").disabled=!ok||!c||!!c?.cancel;
 $("running").disabled=!c;
}
function updateRunInfo(){
 const p=data.plan,c=p.current,v=data.live||{};
 const lines=[
  p.enabled?"ПЛАН ЗАПУЩЕН":c?"ПАУЗА ПОСЛЕ ТЕКУЩЕЙ":"ПАУЗА",
  "Потоков CP-SAT: "+data.workers,
  "Ограничитель RAM: отключён",
  "Автопоиск после списка: "+(p.auto?"да":"нет"),
  "Исходных опорных ячеек: "+p.anchors.length
 ];
 if(c){
  lines.push(
   "",
   `${MODES[c.mode]||c.mode}: D=${c.d} S=${c.s} K=${c.k}`,
   "Этап: "+(v.phase||"Запуск"),
   "Бюджет CP-SAT: "+(c.budget==null?"БЕЗ ЛИМИТА":c.budget+" с"),
   "Прошло: "+duration(v.elapsed),
   "CP-SAT сейчас: "+duration(v.solve_elapsed),
   "RSS сейчас: "+memory(v.rss_bytes),
   "Пик RSS: "+memory(v.peak_bytes),
   "PID: "+(c.pid??v.pid??"—")
  );
  if(c.cancel)lines.push("ПРЕРЫВАНИЕ: "+c.cancel);
 }
 lines.push(
  "",
  "Осталось вручную: "+p.queue.length,
  "Отложена прерванная авто-задача: "+(p.retry?"да":"нет"),
  "Красных уже повторено: "+p.seen_red.length,
  "Оранжевых уже запущено: "+p.seen_orange.length,
  "Пропущено в этом плане: "+p.deferred.length,
  "",
  p.message||""
 );
 if(p.queue.length){
  lines.push("","Ожидают:");
  p.queue.slice(0,40).forEach((q,i)=>lines.push(`${i+1}. D=${q.d} S=${q.s} K=${q.k}`));
  if(p.queue.length>40)lines.push("… ещё "+(p.queue.length-40));
 }
 $("runInfo").textContent=lines.join("\n");
}
function applySnapshot(snapshot){
 if(data&&snapshot.refreshed<data.refreshed)return;
 const oldN=n;
 data=snapshot;n=data.n;online=true;
 $("path").textContent=data.folder;
 $("goD").max=$("goS").max=n-1;
 $("live").className=data.error?"bad":"";
 $("live").textContent=data.loading?"Чтение существующих states…":
  `N=${n} · файлов=${data.files} · `+
  (data.plan.enabled?"план запущен":"план на паузе")+
  ` · обновлено ${new Date(data.refreshed*1000).toLocaleTimeString("ru-RU")}`+
  (data.error?" · "+data.error:"");
 $("warnings").textContent=[
  ...(data.error?[data.error]:[]),...(data.warnings||[])
 ].join("\n\n");
 if(data.loading){updateButtons();repaint();return}

 byId=new Map(data.rows.map(r=>[idx(r.d,r.s),r]));
 cells=new Array(n*n);
 for(let d=0;d<n;d++)for(let s=0;s<n;s++){
  let row=byId.get(idx(d,s)),kind;
  if(row)kind="state";
  else if(d===s)kind="excluded";
  else{
   const [rd,rs]=reflect(d,s);row=byId.get(idx(rd,rs));
   kind=row?"reflection":"missing";
  }
  cells[idx(d,s)]={d,s,row,kind,limit:bound(d,s),
   status:row?row.status:kind==="excluded"?"EXCLUDED":"MISSING"};
 }
 if(draftDataset!==data.dataset){
  draftDataset=data.dataset;draft=[];
  try{
   const saved=JSON.parse(localStorage.getItem("deck-draft-"+draftDataset)||"[]");
   const seen=new Set();
   for(const p of saved){
    if(!Number.isInteger(p.d)||!Number.isInteger(p.s)||
       p.d<0||p.s<0||p.d>=n||p.s>=n)continue;
    const r=getCell(p)?.row;
    if(r?.runnable&&!seen.has(r.file)){
     seen.add(r.file);draft.push({d:p.d,s:p.s,file:r.file});
    }
   }
  }catch(e){}
  renderDraft();
 }
 if(oldN!==n){fitted=false;selected=null}
 if(!fitted)fit();
 updateLegend();updateRunInfo();updateButtons();refreshHover();repaint();
}
async function fetchState(){
 const controller=new AbortController();
 const timeout=setTimeout(()=>controller.abort(),10000);
 try{
  const response=await fetch("/api/state",{cache:"no-store",signal:controller.signal});
  if(!response.ok)throw new Error("HTTP "+response.status);
  applySnapshot(await response.json());
 }finally{clearTimeout(timeout)}
}
async function post(action,extra={}){
 if(busy)return;
 busy=true;updateButtons();
 try{
  const response=await fetch("/api/control",{
   method:"POST",headers:{"Content-Type":"application/json","X-Deck-Token":TOKEN},
   body:JSON.stringify({action,...extra})
  });
  const answer=await response.json();
  if(!response.ok||!answer.ok)throw new Error(answer.error||"Ошибка команды");
  await fetchState();
 }catch(e){alert(e.message)}
 finally{busy=false;updateButtons()}
}
async function poll(){
 try{await fetchState()}
 catch(e){
  online=false;$("live").className="bad";
  $("live").textContent="Нет связи с сервером. Показан последний снимок. "+e.message;
  updateButtons();
 }finally{setTimeout(poll,1000)}
}

canvas.addEventListener("wheel",e=>{
 e.preventDefault();const p=point(e);lastPointer=p;
 const delta=e.deltaY*(e.deltaMode===1?16:e.deltaMode===2?H:1);
 zoom(Math.exp(-Math.max(-500,Math.min(500,delta))*.0015),p.x,p.y);
},{passive:false});
canvas.addEventListener("pointerdown",e=>{
 if(e.button!==0&&e.button!==1)return;
 e.preventDefault();const p=point(e);lastPointer=p;
 drag={id:e.pointerId,x:p.x,y:p.y,ox,oy,moved:false,button:e.button};
 canvas.setPointerCapture(e.pointerId);canvas.style.cursor="grabbing";
 tip.style.display="none";
});
canvas.addEventListener("pointermove",e=>{
 const p=point(e);lastPointer=p;
 if(drag&&drag.id===e.pointerId){
  const dx=p.x-drag.x,dy=p.y-drag.y;
  if(Math.hypot(dx,dy)>3)drag.moved=true;
  if(drag.moved){ox=drag.ox+dx;oy=drag.oy+dy}
  hover=null;repaint();return;
 }
 refreshHover();repaint();
});
canvas.addEventListener("pointerup",e=>{
 if(!drag||drag.id!==e.pointerId)return;
 const click=!drag.moved&&drag.button===0,p=point(e);drag=null;lastPointer=p;
 if(canvas.hasPointerCapture(e.pointerId))canvas.releasePointerCapture(e.pointerId);
 canvas.style.cursor="grab";
 if(click){
  selected=hit(p);
  if(selected&&($("queueMode").checked||e.shiftKey))toggleDraft(selected);
 }
 refreshHover();repaint();
});
canvas.addEventListener("pointercancel",()=>{
 drag=null;hover=null;lastPointer=null;canvas.style.cursor="grab";
 tip.style.display="none";updatePanel();repaint();
});
canvas.addEventListener("pointerleave",()=>{
 if(!drag){hover=null;lastPointer=null;tip.style.display="none";updatePanel();repaint()}
});

$("fit").onclick=fit;
$("zin").onclick=()=>zoom(1.35);
$("zout").onclick=()=>zoom(1/1.35);
$("numbers").onchange=repaint;
$("marks").onchange=repaint;
$("unpin").onclick=()=>{selected=null;updatePanel();repaint()};
$("mirror").onclick=()=>{
 if(selected){const [d,s]=reflect(selected.d,selected.s);jump(d,s)}
};
$("running").onclick=()=>{
 const c=data?.plan?.current;if(c)jump(c.click_d??c.d,c.click_s??c.s);
};
$("go").onsubmit=e=>{
 e.preventDefault();jump(Number($("goD").value),Number($("goS").value));
};
$("clearDraft").onclick=()=>{
 draft=[];saveDraft();renderDraft();repaint();
};
$("addSelected").onclick=()=>{if(selected)toggleDraft(selected)};
$("start").onclick=()=>{
 if(!draft.length)return;
 const p=data?.plan;
 if((p?.queue?.length||p?.retry)&&
    !confirm("Новый список заменит остаток сохранённого плана. Продолжить?"))return;
 post("start",{cells:draft.map(p=>({d:p.d,s:p.s})),auto:$("auto").checked});
};
$("pause").onclick=()=>post("pause");
$("resume").onclick=()=>post("resume");
$("stop").onclick=()=>post("stop",{job_id:data?.plan?.current?.id??null});
$("skip").onclick=()=>{
 if(confirm("Прервать и пропустить эту конфигурацию до нового плана?"))
  post("skip",{job_id:data?.plan?.current?.id??null});
};
window.addEventListener("keydown",e=>{
 if(e.key==="Escape"){selected=null;updatePanel();repaint()}
});
new ResizeObserver(resize).observe($("plot"));
window.addEventListener("resize",resize);
resize();poll();
</script>
</body>
</html>
"""


# ----------------------------------------------------------------------
# HTTP: только localhost, без публикации произвольных файлов.
# ----------------------------------------------------------------------

class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass

    def allowed_request(self):
        host = self.headers.get("Host", "").lower()
        if host not in self.server.allowed_hosts:
            return False

        origin = self.headers.get("Origin")
        if origin:
            parsed = urlsplit(origin)
            if (
                parsed.scheme != "http"
                or parsed.netloc.lower() not in self.server.allowed_hosts
            ):
                return False

        return True

    def send_body(self, status, body, content_type, compressed=False):
        try:
            self.send_response(status)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.send_header("X-Frame-Options", "DENY")
            self.send_header("Referrer-Policy", "no-referrer")
            self.send_header(
                "Content-Security-Policy",
                "default-src 'none'; "
                "script-src 'unsafe-inline'; "
                "style-src 'unsafe-inline'; "
                "connect-src 'self'; "
                "img-src 'self' data:; "
                "frame-ancestors 'none'; "
                "base-uri 'none'; "
                "form-action 'self'",
            )

            if compressed:
                self.send_header("Content-Encoding", "gzip")
                self.send_header("Vary", "Accept-Encoding")

            self.end_headers()
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError, OSError):
            pass

    def send_json(self, status, obj, compress=False):
        body = json.dumps(
            obj,
            ensure_ascii=False,
            allow_nan=False,
            separators=(",", ":"),
        ).encode("utf-8")

        compressed = (
            compress
            and "gzip" in self.headers.get("Accept-Encoding", "")
        )

        if compressed:
            body = gzip.compress(body, compresslevel=1)

        self.send_body(
            status,
            body,
            "application/json; charset=utf-8",
            compressed=compressed,
        )

    def do_GET(self):
        if not self.allowed_request():
            self.send_json(403, {"error": "Недопустимый Host/Origin"})
            return

        parsed = urlsplit(self.path)

        try:
            if parsed.path == "/":
                body = HTML.replace(
                    "__DECK_TOKEN__", json.dumps(self.server.token)
                ).encode("utf-8")
                self.send_body(200, body, "text/html; charset=utf-8")

            elif parsed.path == "/api/state":
                self.send_json(
                    200,
                    self.server.controller.snapshot(),
                    compress=True,
                )

            elif parsed.path == "/api/result":
                query = parse_qs(parsed.query)
                filename = query.get("file", [""])[0]
                solution = query.get("kind", ["last"])[0] == "solution"

                path = self.server.controller.result_path(
                    filename, solution=solution
                )
                self.send_body(
                    200,
                    path.read_bytes(),
                    "application/json; charset=utf-8",
                )

            elif parsed.path == "/favicon.ico":
                self.send_body(204, b"", "image/x-icon")

            else:
                self.send_json(404, {"error": "Не найдено"})

        except (ValueError, FileNotFoundError) as exc:
            self.send_json(404, {"error": str(exc)})
        except Exception as exc:
            self.send_json(503, {"error": str(exc)})

    def do_POST(self):
        if not self.allowed_request():
            self.send_json(403, {"ok": False, "error": "Host/Origin"})
            return

        supplied_token = self.headers.get("X-Deck-Token", "")
        if not secrets.compare_digest(supplied_token, self.server.token):
            self.send_json(
                403, {"ok": False, "error": "Неверный токен управления"}
            )
            return

        if urlsplit(self.path).path != "/api/control":
            self.send_json(404, {"ok": False, "error": "Не найдено"})
            return

        if self.headers.get_content_type() != "application/json":
            self.send_json(
                400, {"ok": False, "error": "Ожидался application/json"}
            )
            return

        try:
            size = int(self.headers.get("Content-Length", "0"))
            if not 0 < size <= 1_000_000:
                raise ValueError("Некорректный размер команды")

            request = json.loads(self.rfile.read(size).decode("utf-8"))
            if not isinstance(request, dict):
                raise ValueError("Команда должна быть JSON-объектом")

            self.server.controller.command(request)
            self.send_json(200, {"ok": True})

        except ValueError as exc:
            self.send_json(400, {"ok": False, "error": str(exc)})
        except RuntimeError as exc:
            self.send_json(409, {"ok": False, "error": str(exc)})
        except Exception as exc:
            traceback.print_exc()
            self.send_json(500, {"ok": False, "error": str(exc)})


def main():
    parser = argparse.ArgumentParser(
        description=(
            "Единый Deck-сервер: сетка, ручная очередь, автопоиск "
            "и изолированный CP-SAT без RAM guard."
        )
    )
    parser.add_argument(
        "--run-dir", type=Path, default=DEFAULT_RUN_DIR
    )
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument(
        "--workers",
        type=int,
        default=8,
        choices=(8,),
        help="CUSTOM8 использует ровно 8 поисковых workers",
    )
    parser.add_argument(
        "--open", action="store_true", dest="open_browser"
    )
    parser.add_argument(
        "--_worker", type=Path, help=argparse.SUPPRESS
    )

    parser.add_argument("--selftest", action="store_true")
    parser.add_argument(
        "--copy-dir", type=Path, default=None,
        help="Куда один раз скопировать исходную рабочую папку"
    )

    args = parser.parse_args()

    if args.selftest:
        return _reduced_selftest()

    if args._worker is not None:
        return worker_main(args._worker)

    if sys.maxsize <= 2 ** 32:
        parser.error("Нужен 64-разрядный Python для работы с большой RAM")

    if args.workers < 1:
        parser.error("--workers должен быть положительным")

    if not 0 <= args.port <= 65535:
        parser.error("Некорректный порт")

    if importlib.util.find_spec("ortools") is None:
        parser.error(
            "Не установлен OR-Tools. "
            "Выполни: py -m pip install ortools psutil filelock"
        )

    # Проверяем версию до открытия базы и запуска планировщика.
    # Тяжёлый cp_model в родительский сервер здесь не импортируем.
    try:
        custom8_version = _deck8_check_version()
    except Exception as exc:
        parser.error(str(exc))

    print(
        f"CP-SAT profile: {DECK_CUSTOM8_PROFILE}; "
        f"OR-Tools: {custom8_version}",
        flush=True,
    )

    _reduced_startup_selftest()
    directory = _reduced_prepare_directory(
        args.run_dir, args.copy_dir
    )

    if not (directory / "states").is_dir():
        parser.error(f"Не найдена папка {directory / 'states'}")

    if not Path(__file__).resolve().with_name("data.csv").is_file():
        parser.error("Не найден data.csv рядом с новым скриптом")

    controller = None
    server = None

    try:
        with contextlib.ExitStack() as stack:
            # Совместимость с блокировками старого решателя:
            # новый и старый вычислители не должны работать одновременно.
            for name in (
                "half30_supervisor.lock",
                "run.lock",
                "deck_server.lock",
            ):
                stack.enter_context(
                    FileLock(str(directory / name), timeout=0)
                )

            controller = Controller(directory, args.workers)

            try:
                server = ThreadingHTTPServer(
                    ("127.0.0.1", args.port), Handler
                )
                server.daemon_threads = True
                server.controller = controller
                server.token = secrets.token_urlsafe(32)

                port = server.server_address[1]
                server.allowed_hosts = {
                    f"127.0.0.1:{port}",
                    f"localhost:{port}",
                }

                if port == 80:
                    server.allowed_hosts.update({"127.0.0.1", "localhost"})

                url = f"http://127.0.0.1:{port}/"

                controller.start()

                print(f"Папка задачи: {directory}", flush=True)
                print(f"Новые данные: {controller.store}", flush=True)
                print(f"Интерфейс: {url}", flush=True)
                print(
                    f"CP-SAT workers={args.workers}; RAM guard отключён.",
                    flush=True,
                )
                print(
                    "Закрытие браузера не останавливает вычисления.",
                    flush=True,
                )
                print(
                    "Ctrl+C останавливает сервер и текущую попытку; "
                    "очередь остаётся сохранённой.",
                    flush=True,
                )

                def interrupt(signum, frame):
                    raise KeyboardInterrupt()

                for name in ("SIGINT", "SIGTERM", "SIGBREAK"):
                    if hasattr(signal, name):
                        signal.signal(getattr(signal, name), interrupt)

                if args.open_browser:
                    with contextlib.suppress(Exception):
                        webbrowser.open(url)

                try:
                    server.serve_forever(poll_interval=0.25)
                except KeyboardInterrupt:
                    print("\nОстановка и сохранение очереди…", flush=True)

            finally:
                if server is not None:
                    server.server_close()
                if controller is not None:
                    controller.close()

    except LockTimeout:
        print(
            "Эта папка уже занята вычислителем или другим Deck-сервером.\n"
            "Сначала останови старый deck_half30.py / supervisor "
            "и дождись его завершения.",
            file=sys.stderr,
        )
        return 2

    except Exception:
        traceback.print_exc()
        return 2

    return 0


# BEGIN DECK_REDUCED_PATCH_V1

REDUCED_VERSION = 'deck-reduced/element-covered/v2'
REDUCED_COPY_MARKER = '.deck_covered_copy_v2.json'


def _reduced_require(condition, message):
    # В отличие от assert, работает и при python -O.
    if not condition:
        raise AssertionError(message)


def _reduced_impossible(n):
    from ortools.sat.python import cp_model

    model = cp_model.CpModel()

    # Сохраняем N начальных индексов: старый worker и его профиль
    # используют их и для определения N, и для dataset hash.
    initial = [
        model.new_int_var(0, n - 1, f"P_{card}")
        for card in range(n)
    ]
    model.add_bool_or([])
    return model, [v.index for v in initial], []


def _reduced_dataset_hash(n, messages):
    raw = json.dumps(
        {"n": int(n), "messages": messages},
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def _reduced_oracle(initial, messages, n, d, s, k):
    """Независимая симуляция полной колоды, без CP-SAT."""
    if n <= 0 or sorted(initial) != list(range(n)):
        return None

    d %= n
    s %= n
    delta = (d - s) % n
    if not 1 <= k <= n or min(delta, n - delta) < k:
        return None

    deck0 = [0] * n
    for card, position in enumerate(initial):
        deck0[position] = card

    outputs = []

    for sequence in messages:
        positions = list(initial)
        deck = list(deck0)
        row = []

        for t, card in enumerate(sequence):
            a = positions[card]

            if (a - t * s) % n >= k:
                return None

            row.append(a)
            b = (a + d) % n
            other = deck[b]

            deck[a], deck[b] = deck[b], deck[a]
            positions[card], positions[other] = b, a

        outputs.append(row)

    return outputs


def _reduced_validate_sat(result, messages, n, d, s, k):
    trace = _reduced_oracle(
        result["positions"], messages, n, d, s, k
    )
    if trace is None:
        raise RuntimeError(
            "SAT не прошёл независимую симуляцию полной колоды"
        )

    expected_inputs = [
        [(a - t * s) % n for t, a in enumerate(row)]
        for row in trace
    ]
    if expected_inputs != result["inputs"]:
        raise RuntimeError(
            "SAT: извлечённые inputs не совпадают с симулятором"
        )

    expected_deck = [0] * n
    for card, position in enumerate(result["positions"]):
        expected_deck[position] = card

    if expected_deck != result["deck"]:
        raise RuntimeError("SAT: неверно извлечена начальная колода")

    result["independently_verified"] = True


def _reduced_history_version(row):
    if row.get("resolved") in TERMINAL:
        return row.get("result_model_version")
    return row.get("last_model_version")


def _reduced_is_legacy(row):
    has_history = (
        row.get("resolved") in TERMINAL
        or row.get("status") not in (None, "", "PENDING")
        or integer(row.get("attempts")) > 0
    )
    return bool(
        has_history
        and _reduced_history_version(row) != REDUCED_VERSION
    )


_reduced_original_load_catalog = load_catalog


def load_catalog(directory, n, fingerprint, saved_records):
    rows, warnings, count = _reduced_original_load_catalog(
        directory, n, fingerprint, saved_records
    )
    for row in rows.values():
        row["legacy_result"] = _reduced_is_legacy(row)
    return rows, warnings, count


def _reduced_check_copy(directory, dataset):
    marker_path = directory / REDUCED_COPY_MARKER
    marker = read_json(marker_path)

    if not isinstance(marker, dict):
        raise RuntimeError(f"Повреждён маркер копии: {marker_path}")

    if marker.get("version") != REDUCED_VERSION:
        raise RuntimeError("Рабочая копия создана другой версией патча")

    if marker.get("dataset") != dataset:
        raise RuntimeError(
            "data.csv не соответствует результатам в рабочей копии. "
            "Не смешивайте разные задачи в одной папке."
        )

    if not (directory / "states").is_dir():
        raise RuntimeError(f"В рабочей копии нет states: {directory}")

    return marker


def _reduced_backup_database(source_db, target_db):
    # copytree уже скопировал основной файл; заменяем его
    # согласованным SQLite backup с учётом исходного WAL.
    target_db.unlink(missing_ok=True)
    for suffix in ("-wal", "-shm"):
        Path(str(target_db) + suffix).unlink(missing_ok=True)

    with contextlib.closing(
        sqlite3.connect(source_db.as_uri() + "?mode=ro", uri=True)
    ) as source_connection:
        with contextlib.closing(
            sqlite3.connect(str(target_db))
        ) as target_connection:
            source_connection.backup(target_connection)


def _reduced_reset_copied_plan(directory, dataset):
    db_path = directory / STORE_NAME / "control.sqlite3"
    if not db_path.is_file():
        return

    with contextlib.closing(sqlite3.connect(str(db_path))) as db:
        tables = {
            row[0]
            for row in db.execute(
                "SELECT name FROM sqlite_master WHERE type='table'"
            )
        }
        if "meta" not in tables:
            return

        row = db.execute(
            "SELECT v FROM meta WHERE k='dataset'"
        ).fetchone()
        if row is not None and json.loads(row[0]) != dataset:
            raise RuntimeError(
                "Скопированная SQLite содержит другой N/messages dataset"
            )

        old_plan = db.execute(
            "SELECT v FROM meta WHERE k='plan'"
        ).fetchone()

        with db:
            if old_plan is not None:
                db.execute(
                    "INSERT OR REPLACE INTO meta(k,v) VALUES(?,?)",
                    ("reduced_archived_previous_plan", old_plan[0]),
                )

            # Нельзя восстанавливать из копии старые PID/job:
            # они относятся к старому серверу и старой папке.
            db.execute(
                "INSERT OR REPLACE INTO meta(k,v) VALUES(?,?)",
                (
                    "plan",
                    json.dumps(
                        default_plan(),
                        ensure_ascii=False,
                        allow_nan=False,
                    ),
                ),
            )


def _reduced_prepare_directory(source, copy_directory=None):
    return _v2_prepare_directory(source, copy_directory)


def _reduced_proto(model):
    from google.protobuf import text_format
    from ortools.sat import cp_model_pb2

    proto = cp_model_pb2.CpModelProto()
    text_format.Parse(str(model.proto), proto)
    return proto


def _reduced_enumerate(builder, messages, n, d, s, k):
    from ortools.sat.python import cp_model

    model, initial_indices, output_indices = builder(
        messages, n, d, s, k, lambda: None
    )

    initial = [
        model.get_int_var_from_proto_index(i)
        for i in initial_indices
    ]
    outputs = [
        [model.get_int_var_from_proto_index(i) for i in row]
        for row in output_indices
    ]

    class Collector(cp_model.CpSolverSolutionCallback):
        def __init__(self):
            super().__init__()
            self.solutions = set()
            self.error = None

        def on_solution_callback(self):
            try:
                positions = tuple(int(self.value(v)) for v in initial)
                expected_trace = _reduced_oracle(
                    positions, messages, n, d, s, k
                )
                _reduced_require(
                    expected_trace is not None,
                    "Модель приняла перестановку, отвергнутую симулятором",
                )
                actual_trace = [
                    [int(self.value(v)) for v in row]
                    for row in outputs
                ]
                _reduced_require(
                    actual_trace == expected_trace,
                    "Выходные позиции модели не совпадают с симулятором",
                )
                self.solutions.add(positions)
            except Exception as exc:
                self.error = exc
                self.stop_search()

    collector = Collector()
    solver = cp_model.CpSolver()
    solver.parameters.num_workers = 1
    solver.parameters.enumerate_all_solutions = True
    solver.parameters.max_time_in_seconds = 10.0

    status = solver.solve(model, collector)

    if collector.error is not None:
        raise collector.error

    _reduced_require(
        status in (cp_model.OPTIMAL, cp_model.INFEASIBLE),
        f"Перебор модели не завершён: {status}",
    )

    return collector.solutions, _reduced_proto(model)


def _reduced_selftest():
    return _v2_selftest()


def _reduced_startup_selftest():
    # Отдельный процесс: CP-SAT и память тестов не остаются
    # в родительском сервере.
    subprocess.run(
        [
            sys.executable,
            "-u",
            str(Path(__file__).resolve()),
            "--selftest",
        ],
        check=True,
        timeout=180,
    )

# END DECK_REDUCED_PATCH_V1




# BEGIN DECK_ELEMENT_COVERED_V2

_V2_COPY_POINTER = Path(__file__).resolve().with_suffix(".workdir.json")


def _v2_clear_field(message, name):
    clear = getattr(message, "ClearField", None)
    if callable(clear):
        clear(name)
    else:
        getattr(message, "clear_" + name)()


def _v2_add_mux(model, hit, old, a, new):
    """new = old при hit=0, new = a при hit=1."""
    constraint = model.add_element(hit, [old, a], new)
    element = constraint.proto.element

    # У всех четырёх аргументов здесь простые переменные.
    # Компактный legacy-формат допустим в используемой версии 9.15.
    # Не смешиваем его с новым форматом линейных выражений.
    _v2_clear_field(element, "linear_index")
    _v2_clear_field(element, "linear_target")

    if callable(getattr(element, "ClearField", None)):
        element.ClearField("exprs")
        element.ClearField("vars")
    else:
        element.exprs.clear()
        element.vars.clear()

    element.index = int(hit.index)
    element.target = int(new.index)
    element.vars.extend([int(old.index), int(a.index)])


def _v2_cover_blocks(n, group_count=9):
    """Каждая пара индексов должна попасть хотя бы в один блок."""
    group_count = min(group_count, n)
    if group_count < 2:
        return [list(range(n))]

    groups = [list(range(g, n, group_count))
              for g in range(group_count)]

    return [
        groups[g] + groups[h]
        for g in range(group_count)
        for h in range(g + 1, group_count)
    ]


def _v2_add_distinct(model, initial, updates, d, check, mode):
    if mode not in ("auto", "global", "covered"):
        raise ValueError(f"Неизвестная кодировка distinct: {mode}")

    # При N=83 покрытие добавляет 35 ограничений и 581 вхождение
    # переменных. Замена E mux-блоков экономит E ограничений
    # и 2E вхождений. Поэтому достаточно E >= 291.
    covered = (
        mode == "covered"
        or (
            mode == "auto"
            and len(initial) == 83
            and d != 0
            and updates >= 291
        )
    )

    if not covered:
        model.add_all_different(initial)
        return "global"

    for block in _v2_cover_blocks(len(initial)):
        check()
        model.add_all_different([initial[i] for i in block])

    return "covered"


def _v2_build_model(messages, n, d, s, k, check, distinct_mode="auto"):
    from ortools.sat.python import cp_model

    if n <= 0:
        raise ValueError("N должен быть положительным")

    d %= n
    s %= n
    check()

    if not 1 <= k <= n or circular_distance(d - s, n) < k:
        return _reduced_impossible(n)

    model = cp_model.CpModel()
    initial = [
        model.new_int_var(0, n - 1, f"P_{card}")
        for card in range(n)
    ]
    initial_indices = [variable.index for variable in initial]

    # Начальную различность добавляем в конце.
    # При раннем противоречии не строим ненужное покрытие.
    windows = [
        cp_model.Domain.from_values(
            sorted({(t * s + u) % n for u in range(k)})
        )
        for t in range(n)
    ]

    def position():
        return model.new_int_var(0, n - 1, "")

    nonzero_difference = cp_model.Domain.from_intervals([
        [-(n - 1), -1],
        [1, n - 1],
    ])

    first_edges = {}
    outputs = []
    updates = 0

    for sequence in messages:
        check()

        if any(type(card) is not int or not 0 <= card < n
               for card in sequence):
            raise ValueError("Некорректный номер карты")

        remaining = Counter(sequence)
        pos = {
            card: initial[card]
            for card in sorted(remaining)
        }
        row = []

        for t, card in enumerate(sequence):
            check()

            a = pos[card]
            restricted = a.domain.intersection_with(windows[t % n])
            if restricted.is_empty():
                return _reduced_impossible(n)

            a.domain = restricted
            row.append(a.index)

            remaining[card] -= 1
            if remaining[card] == 0:
                del pos[card]

            if not pos or d == 0:
                continue

            b = position()
            model.add_modulo_equality(b, a + d, n)

            if remaining[card]:
                pos[card] = b

            for other in list(pos):
                check()
                if other == card:
                    continue

                old = pos[other]
                edge = (card, other)
                hit = first_edges.get(edge) if t == 0 else None

                if hit is None:
                    hit = model.new_bool_var("")

                    # ОБА направления определения hit сохраняются.
                    model.add(old == b).only_enforce_if(hit)
                    model.add_linear_expression_in_domain(
                        old - b, nonzero_difference
                    ).only_enforce_if(hit.Not())

                    if t == 0:
                        first_edges[edge] = hit

                new = position()
                _v2_add_mux(model, hit, old, a, new)
                pos[other] = new
                updates += 1

        outputs.append(row)

    encoding = _v2_add_distinct(
        model, initial, updates, d, check, distinct_mode
    )
    model.name = f"ELEMENT_COVERED_V2/{encoding}/E={updates}"

    return model, initial_indices, outputs


def _v2_stats(proto):
    """Структура входного protobuf, до presolve."""
    arities = []
    coefficients = []
    rhs_endpoints = 0

    for constraint in proto.constraints:
        refs = {
            int(lit) if lit >= 0 else -int(lit) - 1
            for lit in constraint.enforcement_literal
        }
        kind = constraint.WhichOneof("constraint")

        def expression(expr):
            refs.update(int(v) for v in expr.vars)
            coefficients.extend(int(c) for c in expr.coeffs)

        if kind == "linear":
            refs.update(int(v) for v in constraint.linear.vars)
            coefficients.extend(int(c) for c in constraint.linear.coeffs)
            rhs_endpoints += len(constraint.linear.domain)

        elif kind == "all_diff":
            for expr in constraint.all_diff.exprs:
                expression(expr)

        elif kind == "element":
            el = constraint.element
            if el.vars:
                refs.update([int(el.index), int(el.target)])
                refs.update(int(v) for v in el.vars)
            else:
                expression(el.linear_index)
                expression(el.linear_target)
                for expr in el.exprs:
                    expression(expr)

        elif kind == "int_mod":
            expression(constraint.int_mod.target)
            for expr in constraint.int_mod.exprs:
                expression(expr)

        elif kind == "bool_or":
            refs.update(
                int(lit) if lit >= 0 else -int(lit) - 1
                for lit in constraint.bool_or.literals
            )

        else:
            raise AssertionError(f"Неожиданный тип ограничения: {kind}")

        arities.append(len(refs))

    return {
        "variables": len(proto.variables),
        "constraints": len(proto.constraints),
        "total_arity": sum(arities),
        "max_arity": max(arities, default=0),
        "coefficient_entries": len(coefficients),
        "max_coefficient": max(map(abs, coefficients), default=0),
        "rhs_endpoints": rhs_endpoints,
    }


def _v2_check_copy(directory, dataset):
    directory = Path(directory).resolve()
    marker = read_json(directory / REDUCED_COPY_MARKER)

    if (
        not isinstance(marker, dict)
        or marker.get("version") != REDUCED_VERSION
        or marker.get("dataset") != dataset
        or not marker.get("source")
        or not (directory / "states").is_dir()
    ):
        raise RuntimeError(
            f"Некорректная или несовместимая рабочая копия: {directory}"
        )

    return marker


def _v2_copy_run_directory(source, destination, n, dataset):
    import shutil

    source = Path(source).expanduser().resolve()
    destination = Path(destination).expanduser().resolve()

    if (
        source == destination
        or destination.is_relative_to(source)
        or source.is_relative_to(destination)
    ):
        raise RuntimeError(
            "Источник и копия должны быть разными папками "
            "и не должны находиться одна внутри другой"
        )

    destination.parent.mkdir(parents=True, exist_ok=True)
    bootstrap_lock = destination.with_name(
        destination.name + ".bootstrap.lock"
    )

    with FileLock(str(bootstrap_lock), timeout=0):
        if destination.exists():
            marker = _v2_check_copy(destination, dataset)
            if marker["source"] != str(source):
                raise RuntimeError(
                    "Существующая копия создана из другой папки"
                )
            return destination

        if not (source / "states").is_dir():
            raise RuntimeError(f"Не найдена папка states: {source}")

        # Если копируем рабочую папку предыдущей reduced-версии,
        # проверяем её привязку к входным данным.
        old_marker_path = source / ".deck_reduced_copy_v1.json"
        if old_marker_path.is_file():
            old_marker = read_json(old_marker_path)
            if (
                not isinstance(old_marker, dict)
                or old_marker.get("dataset") != dataset
                or old_marker.get("n") != n
            ):
                raise RuntimeError(
                    "Прежняя рабочая папка относится к другому dataset"
                )

        temporary = destination.with_name(
            "." + destination.name + "." + uuid.uuid4().hex + ".tmp"
        )

        def ignore_transient(directory, names):
            return [
                name for name in names
                if name.endswith((".lock", "-wal", "-shm"))
            ]

        try:
            # Старый сервер должен быть остановлен.
            with contextlib.ExitStack() as stack:
                for name in (
                    "half30_supervisor.lock",
                    "run.lock",
                    "deck_server.lock",
                ):
                    stack.enter_context(
                        FileLock(str(source / name), timeout=0)
                    )

                print(
                    f"Первый запуск: копирование\n"
                    f"  из: {source}\n"
                    f"   в: {destination}",
                    flush=True,
                )

                shutil.copytree(
                    source,
                    temporary,
                    ignore=ignore_transient,
                )

                source_db = source / STORE_NAME / "control.sqlite3"
                if source_db.is_file():
                    # Согласованный backup включает данные исходного WAL.
                    _reduced_backup_database(
                        source_db,
                        temporary / STORE_NAME / "control.sqlite3",
                    )

                # Результаты сохраняются. Старые PID и текущий job
                # не восстанавливаются в новой папке.
                # Прежний план архивируется существующим helper.
                _reduced_reset_copied_plan(temporary, dataset)

                atomic_json(
                    temporary / REDUCED_COPY_MARKER,
                    {
                        "version": REDUCED_VERSION,
                        "source": str(source),
                        "dataset": dataset,
                        "n": n,
                        "created": time.time(),
                    },
                )

                os.rename(temporary, destination)

        except BaseException:
            if temporary.exists():
                shutil.rmtree(temporary, ignore_errors=True)
            raise

    return destination


def _v2_prepare_directory(source, copy_directory=None):
    # Входные сообщения берутся исключительно из соседнего CSV.
    _, n, _, dataset = read_data_csv()

    expected = _DECK_BENCH_WINNER.get("dataset")
    if expected is not None and dataset != expected:
        raise RuntimeError(
            "data.csv не соответствует dataset прежних результатов "
            "и встроенного поискового профиля"
        )

    explicit_source = any(
        arg == "--run-dir" or arg.startswith("--run-dir=")
        for arg in sys.argv[1:]
    )

    def remember(directory, source_path):
        atomic_json(
            _V2_COPY_POINTER,
            {
                "version": REDUCED_VERSION,
                "dataset": dataset,
                "source": str(source_path),
                "directory": str(directory),
            },
        )
        return directory

    # Повторный запуск не зависит от наличия прежней папки.
    if (
        not explicit_source
        and copy_directory is None
        and _V2_COPY_POINTER.is_file()
    ):
        pointer = read_json(_V2_COPY_POINTER)
        if (
            not isinstance(pointer, dict)
            or pointer.get("version") != REDUCED_VERSION
            or pointer.get("dataset") != dataset
        ):
            raise RuntimeError(
                f"Несовместимый указатель рабочей копии: {_V2_COPY_POINTER}"
            )

        directory = Path(pointer["directory"]).resolve()
        marker = _v2_check_copy(directory, dataset)
        if marker["source"] != pointer.get("source"):
            raise RuntimeError("Источник копии не совпадает с указателем")
        return directory

    source = Path(source).expanduser().resolve()

    if (source / REDUCED_COPY_MARKER).is_file():
        if copy_directory is not None:
            raise RuntimeError(
                "--run-dir уже указывает на копию v2; --copy-dir не нужен"
            )
        marker = _v2_check_copy(source, dataset)
        return remember(source, marker["source"])

    # Старый присланный скрипт по умолчанию работал не в
    # DEFAULT_RUN_DIR, а в созданной им папке *_reduced_v1.
    if (
        not explicit_source
        and not (source / ".deck_reduced_copy_v1.json").is_file()
    ):
        previous_copy = source.with_name(source.name + "_reduced_v1")
        if (previous_copy / ".deck_reduced_copy_v1.json").is_file():
            source = previous_copy

    destination = (
        Path(copy_directory).expanduser().resolve()
        if copy_directory is not None
        else source.with_name(source.name + "_covered_v2")
    )

    directory = _v2_copy_run_directory(source, destination, n, dataset)
    return remember(directory, source)


def _v2_solve_case(messages, n, d, s, k, expected_sat,
                   use_profile=False, pin_identity=False):
    from ortools.sat.python import cp_model

    model, initial_indices, output_indices = build_model(
        messages, n, d, s, k, lambda: None
    )
    error = model.validate()
    _reduced_require(not error, f"MODEL_INVALID: {error}")

    if pin_identity:
        for card, index in enumerate(initial_indices):
            model.add(
                model.get_int_var_from_proto_index(index) == card
            )

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 10.0
    solver.parameters.stop_after_first_solution = True
    solver.parameters.num_workers = 1

    saved_dataset = _DECK_BENCH_WINNER["dataset"]
    try:
        if use_profile:
            # Только для синтетического selftest.
            _DECK_BENCH_WINNER["dataset"] = _reduced_dataset_hash(
                n, messages
            )
            _deck_bench_apply(
                solver, model, initial_indices, messages
            )

        status = solver.solve(model)
    finally:
        _DECK_BENCH_WINNER["dataset"] = saved_dataset

    if not expected_sat:
        _reduced_require(
            status == cp_model.INFEASIBLE,
            f"Ожидался UNSAT, получен {status}",
        )
        return

    _reduced_require(
        status in (cp_model.FEASIBLE, cp_model.OPTIMAL),
        f"Ожидался SAT, получен {status}",
    )

    positions = [
        int(solver.value(model.get_int_var_from_proto_index(index)))
        for index in initial_indices
    ]
    deck = [0] * n
    for card, position in enumerate(positions):
        deck[position] = card

    inputs = [
        [
            (
                int(solver.value(
                    model.get_int_var_from_proto_index(index)
                )) - t * s
            ) % n
            for t, index in enumerate(row)
        ]
        for row in output_indices
    ]

    result = {
        "positions": positions,
        "deck": deck,
        "inputs": inputs,
    }
    _reduced_validate_sat(result, messages, n, d, s, k)
    _reduced_require(
        result.get("independently_verified"),
        "SAT не проверен независимым симулятором",
    )


def _v2_test_copy():
    import tempfile

    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        source = root / "previous"
        destination = root / "copy"

        (source / "states").mkdir(parents=True)
        (source / STORE_NAME).mkdir()

        atomic_json(
            source / "states" / "d1_s0.json",
            {"test": "previous state"},
        )
        (source / "notes.txt").write_text("previous", encoding="utf-8")

        dataset = _reduced_dataset_hash(3, [[0, 1]])
        record = {
            "file": "d1_s0.json",
            "d": 1,
            "s": 0,
            "k": 1,
            "status": "SAT",
            "resolved": "SAT",
            "result_model_version": "previous-version",
        }
        previous_plan = {
            "enabled": True,
            "current": {"id": "old-job", "pid": 12345},
        }

        source_db = source / STORE_NAME / "control.sqlite3"
        with contextlib.closing(sqlite3.connect(source_db)) as db:
            db.execute("CREATE TABLE meta(k TEXT PRIMARY KEY, v TEXT)")
            db.execute("CREATE TABLE records(file TEXT PRIMARY KEY, v TEXT)")
            db.execute(
                "INSERT INTO meta VALUES(?, ?)",
                ("dataset", json.dumps(dataset)),
            )
            db.execute(
                "INSERT INTO meta VALUES(?, ?)",
                ("plan", json.dumps(previous_plan)),
            )
            db.execute(
                "INSERT INTO records VALUES(?, ?)",
                (record["file"], json.dumps(record)),
            )
            db.commit()

        copied = _v2_copy_run_directory(
            source, destination, 3, dataset
        )
        _reduced_require(copied == destination, "Неверный путь копии")

        target_db = destination / STORE_NAME / "control.sqlite3"
        with contextlib.closing(sqlite3.connect(target_db)) as db:
            copied_record = json.loads(
                db.execute("SELECT v FROM records").fetchone()[0]
            )
            copied_plan = json.loads(
                db.execute(
                    "SELECT v FROM meta WHERE k='plan'"
                ).fetchone()[0]
            )

        _reduced_require(
            copied_record == record,
            "При копировании изменились старые результаты",
        )
        _reduced_require(
            not copied_plan["enabled"]
            and copied_plan["current"] is None,
            "В копии остались активный план или старый PID",
        )
        _reduced_require(
            _reduced_is_legacy(copied_record),
            "Скопированный результат не отмечен как прежний",
        )

        with contextlib.closing(sqlite3.connect(source_db)) as db:
            source_plan = json.loads(
                db.execute(
                    "SELECT v FROM meta WHERE k='plan'"
                ).fetchone()[0]
            )
        _reduced_require(
            source_plan == previous_plan,
            "Изменена база исходной папки",
        )

        # Повторный вызов не должен перезаписывать рабочую копию.
        (destination / "notes.txt").write_text("new", encoding="utf-8")
        _v2_copy_run_directory(source, destination, 3, dataset)
        _reduced_require(
            (destination / "notes.txt").read_text(encoding="utf-8") == "new",
            "Повторное копирование затёрло новые данные",
        )


def _v2_selftest():
    import itertools
    import random
    import tempfile

    _deck8_check_version()
    began = time.monotonic()

    cases = [
        (3, 1, 0, 1, [[0, 1, 0, 1]]),
        (3, 1, 0, 1, [[0, 1, 2]]),
        (5, 2, 0, 1, [[0, 1, 0, 1, 0, 1]]),
        (4, 0, 1, 1, [[0, 1, 2, 3]]),
        (4, 0, 1, 1, [[0], [1]]),
        (4, 0, 1, 1, [[0, 1, 0]]),
        (4, 1, 0, 1, [[0], [0], []]),
        (4, -3, -4, 1, [[0, 1]]),
        (4, 1, 1, 1, [[0, 1]]),
        (4, 1, 0, 0, [[0]]),
        (1, 0, 0, 1, [[0]]),
        (4, 1, 0, 1, [[0, 0]]),
        (4, 1, 0, 1, []),
    ]

    for n in (3, 4):
        for d in range(n):
            for s in range(n):
                for k in range(1, n // 2 + 1):
                    cases.append(
                        (n, d, s, k, [[0, 1, 0, 2], [0, 2, 1]])
                    )

    rng = random.Random(841731)
    for _ in range(24):
        n = rng.choice((3, 4, 5))
        d = rng.randrange(n)
        s = rng.choice([x for x in range(n) if x != d])
        delta = (d - s) % n
        k = rng.randint(1, min(delta, n - delta))
        messages = [
            [rng.randrange(n) for _ in range(rng.randint(0, 7))]
            for _ in range(rng.randint(1, 3))
        ]
        cases.append((n, d, s, k, messages))

    def forced_cover(messages, n, d, s, k, check):
        return _v2_build_model(
            messages, n, d, s, k, check, distinct_mode="covered"
        )

    builders = (
        ("previous", _v2_previous_build_model),
        ("v2-auto", build_model),
        ("v2-forced-cover", forced_cover),
    )

    sat_count = 0
    unsat_count = 0

    for number, (n, d, s, k, messages) in enumerate(cases, 1):
        expected = {
            permutation
            for permutation in itertools.permutations(range(n))
            if _reduced_oracle(
                permutation, messages, n, d, s, k
            ) is not None
        }

        for label, builder in builders:
            actual, _ = _reduced_enumerate(
                builder, messages, n, d, s, k
            )
            _reduced_require(
                actual == expected,
                f"{label}: множество решений отличается от перебора; "
                f"case={number}, N={n}, D={d}, S={s}, K={k}, "
                f"messages={messages!r}",
            )

        if expected:
            sat_count += 1
        else:
            unsat_count += 1

    _reduced_require(
        sat_count > 0 and unsat_count > 0,
        "Selftest должен включать SAT и UNSAT",
    )

    # Проверяем покрытие всех пар, включая пары внутри одной группы.
    blocks = _v2_cover_blocks(83)
    pairs = set()
    for block in blocks:
        pairs.update(
            tuple(sorted(pair))
            for pair in itertools.combinations(block, 2)
        )

    _reduced_require(
        len(blocks) == 36
        and max(map(len, blocks)) == 20
        and sum(map(len, blocks)) == 664
        and pairs == set(itertools.combinations(range(83), 2)),
        "Покрытие AllDifferent неполно или имеет неверные размеры",
    )

    # Полное построение динамической ветви N=83, E=300.
    messages83 = [[0, 1] for _ in range(300)]
    old_model, _, _ = _v2_previous_build_model(
        messages83, 83, 1, 0, 1, lambda: None
    )
    new_model, _, _ = build_model(
        messages83, 83, 1, 0, 1, lambda: None
    )
    _reduced_require(
        not new_model.validate(),
        "MODEL_INVALID в динамической ветви N=83",
    )

    old_proto = _reduced_proto(old_model)
    new_proto = _reduced_proto(new_model)
    old_stats = _v2_stats(old_proto)
    new_stats = _v2_stats(new_proto)

    _reduced_require(
        [list(v.domain) for v in old_proto.variables]
        == [list(v.domain) for v in new_proto.variables],
        "Изменились переменные или их домены",
    )

    elements = [
        c for c in new_proto.constraints if c.HasField("element")
    ]
    alldiffs = [
        c for c in new_proto.constraints if c.HasField("all_diff")
    ]

    _reduced_require(
        len(elements) == 300 and len(alldiffs) == 36,
        "Не использованы Element и покрытие из 36 AllDifferent",
    )
    _reduced_require(
        all(
            len(c.element.vars) == 2
            and not c.element.HasField("linear_index")
            and not c.element.HasField("linear_target")
            and not c.element.exprs
            for c in elements
        ),
        "Element записан не в компактном legacy-формате",
    )
    _reduced_require(
        new_stats["constraints"]
        == old_stats["constraints"] - 300 + 35,
        "Неверное изменение числа ограничений",
    )

    for metric in (
        "variables",
        "constraints",
        "total_arity",
        "coefficient_entries",
        "max_coefficient",
        "rhs_endpoints",
    ):
        _reduced_require(
            new_stats[metric] <= old_stats[metric],
            f"Увеличилась метрика {metric}: "
            f"{old_stats[metric]} -> {new_stats[metric]}",
        )
    _reduced_require(
        new_stats["max_arity"] <= 20,
        "Максимальная арность превышает 20",
    )

    # SAT с известной начальной перестановкой.
    _v2_solve_case(
        messages83, 83, 1, 0, 1, True, pin_identity=True
    )
    # UNSAT без фиксации перестановки: P_0 и P_2 обязаны быть равны 0.
    _v2_solve_case(
        messages83 + [[2]], 83, 1, 0, 1, False
    )

    # Проверяем тот же восьмипоточный профиль, что использует worker.
    for n, d, s, k, messages, expected_sat in (
        (3, 1, 0, 1, [[0, 1, 0, 1]], True),
        (3, 1, 0, 1, [[0, 1, 2]], False),
        (4, 0, 1, 1, [[0, 1, 2, 3]], True),
        (4, 0, 1, 1, [[0], [1]], False),
    ):
        _v2_solve_case(
            messages, n, d, s, k, expected_sat, use_profile=True
        )

    # CSV: нули сохраняются, удаляется только пустой хвост.
    with tempfile.TemporaryDirectory() as directory:
        csv_path = Path(directory) / "data.csv"
        csv_path.write_text(
            "#,Pos,1,2,3,4,5,6\n"
            "0,Test A,0,1,2,3,4,0,,\n"
            "1,Test B,4,3,2,,,,\n",
            encoding="utf-8",
        )
        metadata, n, messages, dataset = read_data_csv(csv_path)
        _reduced_require(
            n == 5
            and messages == [[0, 1, 2, 3, 4, 0], [4, 3, 2]]
            and metadata["names"] == ["Test A", "Test B"]
            and dataset == _reduced_dataset_hash(n, messages),
            "Ошибка чтения CSV",
        )

        csv_path.write_text(
            "#,Pos,1,2,3\n0,Bad,0,,1\n",
            encoding="utf-8",
        )
        try:
            read_data_csv(csv_path)
        except ValueError:
            pass
        else:
            raise AssertionError("Не отвергнута пустота внутри CSV")

    _v2_test_copy()

    _reduced_require(
        _reduced_is_legacy({
            "resolved": "UNSAT",
            "status": "UNSAT",
            "result_model_version": "previous-version",
        }),
        "Старый результат не отмечен",
    )
    _reduced_require(
        not _reduced_is_legacy({
            "resolved": "UNSAT",
            "status": "UNSAT",
            "result_model_version": REDUCED_VERSION,
        }),
        "Новый результат ошибочно отмечен старым",
    )

    print(
        f"SELFTEST V2 OK: {len(cases)} случаев; "
        f"SAT={sat_count}, UNSAT={unsat_count}; "
        "previous = v2-auto = v2-covered = oracle; "
        "N=83, профиль, CSV и копирование проверены; "
        f"{time.monotonic() - began:.3f} с",
        flush=True,
    )
    print("N=83 before:", old_stats, flush=True)
    print("N=83 after: ", new_stats, flush=True)
    return 0


HTML = HTML.replace(
    "REDUCED · целые конфигурации",
    "ELEMENT + COVERED v2 · целые конфигурации",
)

# END DECK_ELEMENT_COVERED_V2


if __name__ == "__main__":
    raise SystemExit(main())
