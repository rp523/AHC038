from pathlib import Path
from subprocess import getoutput
import os, shutil
import time

DEBUG = False
def main():
    exe_path = Path("scan.exe")
    if exe_path.exists():
        os.remove(exe_path)
    cmd_ini = "cargo fmt && cargo build"
    dir_name = "debug"
    if not DEBUG:
        cmd_ini += " -r"
        dir_name = "release"
    print(getoutput(cmd_ini))
    shutil.copy(r"target\{}\atcoder.exe".format(dir_name), exe_path)
    assert(exe_path.exists())
    max_score = 0
    max_score_i = 0
    max_time = 0
    max_time_i = 0
    with open("score1.csv", "w") as f:
        for i in range(1000):
            cmd = ""
            cmd += str(exe_path)
            cmd += r" < tools\in\{0:04d}.txt".format(i)
            cmd += r" > tools\out\{0:04d}.txt".format(i)
            t0 = time.time()
            ret = getoutput(cmd)
            t1 = time.time()
            dt = int(1000 * (t1 - t0))
            score = int(ret)
            if max_score < score:
                max_score = score
                max_score_i = i
            if max_time < dt:
                max_time = dt
                max_time_i = i
            print(i, score, "{}ms MaxScore:({} at {}), MaxTime:({} at {})".format(dt, max_score, max_score_i, max_time, max_time_i))
            f.write("{}\n".format(score))
if __name__ == "__main__":
    main()