from pathlib import Path
from subprocess import getoutput
import os, shutil
import time
def main():
    exe_path = Path("scan.exe")
    if exe_path.exists():
        os.remove(exe_path)
    cmd_ini = "cargo fmt && cargo build -r"
    print(getoutput(cmd_ini))
    shutil.copy(r"target\release\atcoder.exe", exe_path)
    assert(exe_path.exists())
    with open("score1.csv", "w") as f:
        for i in range(1000):
            cmd = ""
            cmd += str(exe_path)
            cmd += r" < tools\in\{0:04d}.txt".format(i)
            cmd += r" > tools\out\{0:04d}.txt".format(i)
            t0 = time.time()
            ret = getoutput(cmd)
            t1 = time.time()
            dt = t1 - t0
            score = int(ret)
            print(i, score, "{}ms".format(int(1000 * dt)))
            f.write("{}\n".format(score))
if __name__ == "__main__":
    main()