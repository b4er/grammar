"""markdown report of one benchmark for CI

    python3 report.py BENCH_DIR RESULTS_TSV [BASE_TSV]

BENCH_DIR/bench.json gives the title, the primary metric and optionally the
subject, the parser under test (default isabelle); the TSVs are `make bench`
results (CASE PARSER METRIC VALUE), each with the run's meta.json (sha, ref)
beside it (if there is one). In CI, GITHUB_SERVER_URL and GITHUB_REPOSITORY
turn the refs into links to their commits."""

import json
import os
import sys
from pathlib import Path
from statistics import geometric_mean

NOTE = 1.0
TOP  = 10


def load(path):
    rows, order, metrics = {}, [], []
    for line in Path(path).read_text().splitlines():
        f = line.split("\t")
        if line.startswith("#") or len(f) < 4:
            continue
        key = (f[0], f[1])
        if key not in rows:
            rows[key] = {}
            order.append(key)
        if f[2] not in metrics:
            metrics.append(f[2])
        rows[key][f[2]] = float(f[3])
    m = Path(path).with_name("meta.json")
    meta = json.loads(m.read_text()) if m.exists() else {}
    return rows, order, metrics, meta


def commit(meta, ref):
    """The run's ref, linked to its commit when the repository is known."""
    ref, sha = meta.get("ref", ref), meta.get("sha", "")
    repo = os.environ.get("GITHUB_REPOSITORY")
    if sha and repo:
        server = os.environ.get("GITHUB_SERVER_URL", "https://github.com")
        return f"[{ref}]({server}/{repo}/commit/{sha})"
    return f"{ref} `{sha[:10]}`" if sha else ref


def fmt(x):
    if x is None:
        return "missing"
    return f"{int(x):,}" if x == int(x) else f"{x:,.2f}"


def pct(r):
    """A ratio new/old as a change."""
    d = (r - 1) * 100
    return "±0" if abs(d) < 0.05 else f"{d:+.1f}%"


def delta(new, old, primary=False):
    if old is None or new is None or old == 0:
        return ""
    s = pct(new / old)
    return f"**{s}**" if primary and abs(new / old - 1) * 100 >= NOTE else s


def times(r):
    return f"{r:.2f}×" if r < 10 else f"{r:.1f}×"


def table(head, rows, right=None):
    right = right or set()
    out = ["| " + " | ".join(head) + " |",
           "|" + "".join("---:|" if i in right else "---|" for i in range(len(head)))]
    out += ["| " + " | ".join(r) + " |" for r in rows]
    return out


def main():
    bench = Path(sys.argv[1])
    spec = json.loads((bench / "bench.json").read_text())
    primary, subject = spec["primary"], spec.get("subject", "isabelle")
    cur, order, metrics, meta = load(sys.argv[2])
    base, bmeta = None, {}
    if len(sys.argv) > 3:
        base, _, _, bmeta = load(sys.argv[3])

    parsers = list(dict.fromkeys(p for _, p in order))
    cases = list(dict.fromkeys(c for c, _ in order))
    others = [m for m in metrics if m not in (primary, "tokens")]

    def val(rows, c, p, m):
        return rows.get((c, p), {}).get(m) if rows is not None else None

    def total(rows, p, m, among=None):
        vs = [val(rows, c, p, m) for c in (among or cases)]
        return None if not vs or None in vs else sum(vs)

    def common(p, m=primary):
        """The cases with metric m of parser p in both runs."""
        return [c for c in cases
                if val(cur, c, p, m) is not None and val(base, c, p, m)]

    # header
    out = [f"### {spec['title']}", ""]
    head = commit(meta, "This run")
    if base is not None:
        head += " against " + commit(bmeta, "base")
    else:
        head += ", no baseline on the base branch"
    tokens = total(cur, parsers[0], "tokens") if "tokens" in metrics else None
    head += f". {len(cases)} cases" + (f", {fmt(tokens)} tokens" if tokens else "")
    out += [head + ".", ""]

    # per parser
    hd = ["parser", f"**{primary}**"]
    if base is not None:
        hd += ["Δ total", "Δ geomean", "Δ range"]
    if tokens:
        hd += ["per token", "per token, range"]
    for m in others:
        hd += [f"*{m}*"] + (["*Δ*"] if base is not None else [])
    rows = []
    for p in parsers:
        t = total(cur, p, primary)
        r = [p if p != subject else f"**{p}**", fmt(t)]
        if base is not None:
            cs = common(p)
            rs = [val(cur, c, p, primary) / val(base, c, p, primary) for c in cs]
            if rs:
                r += [delta(total(cur, p, primary, cs), total(base, p, primary, cs), True),
                      pct(geometric_mean(rs)), f"{pct(min(rs))} … {pct(max(rs))}"]
            else:
                r += ["", "", ""]
        if tokens:
            per = [val(cur, c, p, primary) / val(cur, c, p, "tokens") for c in cases
                   if val(cur, c, p, primary) is not None and val(cur, c, p, "tokens")]
            r += [fmt(round(t / tokens)) if t else "",
                  f"{fmt(round(min(per)))} … {fmt(round(max(per)))}" if per else ""]
        for m in others:
            t = total(cur, p, m)
            r.append(fmt(t))
            if base is not None:
                cs = common(p, m)
                r.append(delta(total(cur, p, m, cs), total(base, p, m, cs)))
        rows.append(r)
    out += table(hd, rows, set(range(1, len(hd))))
    if base is not None:
        out += ["", "Δ total is over the cases of both runs; Δ geomean and Δ range "
                    "are over the per-case changes."]

    # the subject against the others
    if subject in parsers and len(parsers) > 1:
        out += ["", f"**{subject}** against the others, {primary} (above 1×: {subject} costs more):", ""]
        rows = []
        for q in parsers:
            if q == subject:
                continue
            cs = [c for c in cases if val(cur, c, subject, primary) and val(cur, c, q, primary)]
            rs = [val(cur, c, subject, primary) / val(cur, c, q, primary) for c in cs]
            if not rs:
                continue
            r = [q, times(geometric_mean(rs)), f"{times(min(rs))} … {times(max(rs))}"]
            if base is not None:
                bs = [val(base, c, subject, primary) / val(base, c, q, primary) for c in cs
                      if val(base, c, subject, primary) and val(base, c, q, primary)]
                r.append(times(geometric_mean(bs)) if bs else "")
            rows.append(r)
        hd = ["against", "geomean", "range"] + (["base geomean"] if base is not None else [])
        out += table(hd, rows, {1, 2, 3})

    # notable cases
    if base is not None:
        ch = [(val(cur, c, p, primary) / val(base, c, p, primary), c, p)
              for p in parsers for c in common(p)]
        moved = [x for x in ch if abs(x[0] - 1) * 100 >= NOTE]
        worse = sorted((x for x in moved if x[0] > 1), reverse=True)[:TOP]
        better = sorted(x for x in moved if x[0] < 1)[:TOP]
        out.append("")
        if not moved:
            out.append(f"No case's {primary} moved by {NOTE:g}% or more.")
        else:
            out.append(f"{len(moved)} of {len(ch)} cases moved by {NOTE:g}% or more "
                       f"({sum(x[0] > 1 for x in moved)} worse, {sum(x[0] < 1 for x in moved)} better)"
                       + (f"; the {TOP} largest each way" if len(worse) == TOP or len(better) == TOP else "")
                       + ":")
            out.append("")
            out += table(["case", "parser", "base", "now", "Δ"],
                         [[c, p, fmt(val(base, c, p, primary)), fmt(val(cur, c, p, primary)),
                           f"**{pct(r)}**"] for r, c, p in worse + better],
                         {2, 3, 4})
        gone = [k for k in base if k not in cur]
        new = [k for k in order if k not in base]
        if new:
            out += ["", "New cases: " + ", ".join(f"{c} ({p})" for c, p in new) + "."]
        if gone:
            out += ["", "Cases gone: " + ", ".join(f"{c} ({p})" for c, p in gone) + "."]

    # every case
    hd = ["case", "parser"]
    for m in metrics:
        name = f"**{m}**" if m == primary else m if m == "tokens" else f"*{m}*"
        hd += [name] + (["*Δ*" if m in others else "Δ"] if base is not None and m != "tokens" else [])
    rows = []
    for key in order:
        r = list(key)
        for m in metrics:
            v = cur[key].get(m)
            r.append(fmt(v))
            if base is not None and m != "tokens":
                r.append(delta(v, base.get(key, {}).get(m), m == primary))
        rows.append(r)
    out += ["", "<details><summary>Every case</summary>", ""]
    out += table(hd, rows, set(range(2, len(hd))))
    out += ["", "</details>"]
    print("\n".join(out))


if __name__ == "__main__":
    main()
