"""Checks `lake exe fixtures` output (stdin) for `make fixtures`.

1. No line says FAIL.
2. Every `date <text> <ms>` line agrees with Python's datetime: the same instant in
   milliseconds since the epoch (the fraction truncated to milliseconds), or both refuse.
3. Every other line matches fixtures/expected.txt, the golden summary of what the decoders read
   (`make fixtures-update` rewrites it).
"""
import datetime
import re
import sys

RFC3339 = re.compile(
    r"^(\d{4})-(\d{2})-(\d{2})[Tt](\d{2}):(\d{2}):(\d{2})(?:\.(\d+))?(?:([Zz])|([+-])(\d{2}):(\d{2}))$")


def python_ms(text):
    """The instant with Python's calendar arithmetic, independent of the Lean parser."""
    m = RFC3339.match(text)
    if not m:
        return None
    y, mo, d, h, mi, s = (int(g) for g in m.groups()[:6])
    frac = m.group(7) or ""
    if h > 23 or mi > 59 or s > 60:
        return None
    try:
        day = datetime.date(y, mo, d)
    except ValueError:
        return None
    if m.group(8):
        off = 0
    else:
        oh, om = int(m.group(10)), int(m.group(11))
        if oh > 23 or om > 59:
            return None
        off = (oh * 60 + om) * (1 if m.group(9) == "+" else -1)
    days = (day - datetime.date(1970, 1, 1)).days
    secs = days * 86400 + h * 3600 + mi * 60 + s - off * 60
    return secs * 1000 + int((frac + "000")[:3])


def main():
    update = len(sys.argv) > 2 and sys.argv[2] == "--update"
    golden_path = sys.argv[1]
    rest, dates, bad = [], 0, 0
    for line in sys.stdin.read().splitlines():
        if line.startswith("FAIL"):
            print(line)
            bad += 1
        elif line.startswith("date "):
            _, text, ms = line.split(" ")
            want = python_ms(text)
            got = None if ms == "-" else int(ms)
            if want != got:
                print(f"date mismatch: {text}: Lean {got}, Python {want}")
                bad += 1
            dates += 1
        else:
            rest.append(line)
    if update:
        open(golden_path, "w").write("\n".join(rest) + "\n")
    elif open(golden_path).read().splitlines() != rest:
        print(f"fixtures: the decoders' summary differs from {golden_path} (make fixtures-update)")
        bad += 1
    print(f"fixtures: {len(rest)} summary lines, {dates} dates checked against Python, {bad} problems")
    sys.exit(1 if bad else 0)


main()
