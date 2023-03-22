import sys
import time
import multiprocessing
import json
import getopt
import importlib
from collections import defaultdict
from itertools import product
from typing import Iterable
from sage.all import GF, PolynomialRing
from bf import bf
from gb import gb, gb_lex
from sp import sp_gb, sp_el

modes_avail = ['bf', 'spel', 'gb', 'gblex']


def check_solution(R, P: Iterable, A: dict):
    return all(R(p).subs(A).is_zero() for p in P)


def run(name: str, R, P, rslt):
    ret = None
    start = time.process_time_ns()
    if name == 'bf':
        ret = bf(R, P)
    elif name == 'gb':
        ret = gb(R, P)
    elif name == 'gblex':
        ret = gb_lex(R, P)
    elif name == 'spgb':
        ret = sp_gb(R, P)
    elif name == 'spel':
        ret = sp_el(R, P)
    else:
        assert False
    end = time.process_time_ns()
    if type(ret) == dict and not check_solution(R, P, ret):
        rslt.value = -2
    else:
        rslt.value = (end - start) // 1_000_000


def create_process(method, R, data, name):
    rslt = multiprocessing.Value('l', -1)
    proc = multiprocessing.Process(target=run, name=name, args=(method, R, data, rslt))
    return proc, rslt


if __name__ == '__main__':
    try:
        opts, args = getopt.getopt(sys.argv[1:], "t:j:m:", [])
    except getopt.GetoptError as err:
        print(err)
        sys.exit(2)

    if len(args) != 1:
        print("too few/many arguments")
        sys.exit(3)

    # Config
    name = args[0]
    timeout = 5*60  # sec
    core_count = 16
    modes = set()
    for o, a in opts:
        if o == "-t":
            timeout = int(a)
        elif o == "-j":
            core_count = int(a)
        elif o == "-m":
            m = a.lower()
            if m not in modes_avail:
                print(f"invalid mode: {a}")
                sys.exit(3)
            modes.add(m)
    modes = list(modes) if modes else ['gb', 'spel', 'gblex']

    t = importlib.import_module("testdata." + name)

    # Setup
    fs, vc = t.setting()
    FF = GF(fs)
    # R = PolynomialRing(FF, 'x', vc, order='lex')
    R = PolynomialRing(FF, 'x', vc)
    testdata = t.data(R)
    testdata_cnt = len(testdata)
    print(name)

    scheduled = list(product(modes, range(testdata_cnt)))
    running = list()
    result = defaultdict(dict)
    rstat = {}
    try:
        while True:
            if scheduled and len(running) < core_count:
                method, tid = scheduled.pop()
                proc, rslt = create_process(method, R, testdata[tid], f"run_{method}_{tid}")
                to = time.perf_counter() + timeout
                running.append((to, method, tid, proc, rslt))
                proc.start()
                continue

            now = time.perf_counter()
            i = next((i for i, config in enumerate(running) if config[0] < now or not config[3].is_alive()), None)
            if i is not None:
                to, method, tid, proc, rslt = running.pop(i)
                if proc.is_alive():
                    proc.kill()
                result[method][tid] = rslt.value
                proc.join(1)
                continue

            rstat = {k: f"{sum(1 for c in v.values() if c >= 0)}/{len(v)}" for k, v in result.items()}
            stat = f"running {len(running)}/{core_count}, " \
                   f"pending {len(scheduled)}/{testdata_cnt * len(modes)}, " \
                   f"{rstat}"
            print('\r', stat + "       ", file=sys.stderr, end='')
            if not running:
                break
            time.sleep(1)
    except KeyboardInterrupt:
        proc = list(p for _, _, _, p, _ in running)
        for p in proc:
            p.terminate()
        for p in proc:
            p.join(1)

    print(rstat)
    print('\n', json.dumps(result, indent=4))
