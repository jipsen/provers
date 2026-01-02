# From Gavin St. John
# ---------------------------------------------------------------------------
# 1. Download and unpack precompiled prover9 + libladr (if not already done)
# ---------------------------------------------------------------------------
import os, subprocess, sys
BIN_DIR = "/content/p9root/usr/bin"
LIB_DIR = "/content/p9root/usr/lib/x86_64-linux-gnu"

if not os.path.exists(BIN_DIR):
    print("Downloading and unpacking prover9 / libladr .debs ...")
    os.chdir("/content")

    # Grab the library and the prover9/mace4 binaries
    os.system("wget -q https://reflection.grit.ucsb.edu/debian/ubuntu/pool/universe/l/ladr/libladr4_0.0.200911a-2.1build1_amd64.deb")
    os.system("wget -q https://reflection.grit.ucsb.edu/debian/ubuntu/pool/universe/l/ladr/prover9_0.0.200911a-2.1build1_amd64.deb")

    os.system("rm -rf p9root")
    os.system("mkdir -p p9root")

    # Unpack both into /content/p9root
    os.system("dpkg -x libladr4_0.0.200911a-2.1build1_amd64.deb p9root")
    os.system("dpkg -x prover9_0.0.200911a-2.1build1_amd64.deb p9root")

# Refresh paths in case they were just created
BIN_DIR = "/content/p9root/usr/bin"
LIB_DIR = "/content/p9root/usr/lib/x86_64-linux-gnu"

# ---------------------------------------------------------------------------
# 2. Environment: PATH + LD_LIBRARY_PATH so binaries see libladr.so
# ---------------------------------------------------------------------------

os.environ["PATH"] = BIN_DIR + ":" + os.environ.get("PATH", "")
os.environ["LD_LIBRARY_PATH"] = LIB_DIR + ":" + os.environ.get("LD_LIBRARY_PATH", "")

os.environ["PROVER9"]   = os.path.join(BIN_DIR, "prover9")
os.environ["MACE4"]     = os.path.join(BIN_DIR, "mace4")
os.environ["ISOFILTER"] = os.path.join(BIN_DIR, "isofilter")  # will be ignored if missing

# Quick sanity check
print("prover9 binary:", subprocess.run(["which", "prover9"], text=True,
                                        capture_output=True).stdout.strip())
print("mace4   binary:", subprocess.run(["which", "mace4"], text=True,
                                        capture_output=True).stdout.strip())

print(subprocess.run(["prover9", "-version"], text=True,
                     capture_output=True).stdout.splitlines()[0])

# ---------------------------------------------------------------------------
# 3. Clone Maróti's "provers" and import it directly (NO pip install)
# ---------------------------------------------------------------------------

os.chdir("/content")
if os.path.exists("provers"):
    os.system("rm -rf provers")
os.system("git clone -q https://github.com/mmaroti/provers.git")

# Make the local package importable
if "/content/provers" not in sys.path:
    sys.path.insert(0, "/content/provers")

import provers
from provers import *

# ---------------------------------------------------------------------------
# 4. Clone Peter Jipsen's Prover9 helpers and exec Prover9.py
# ---------------------------------------------------------------------------

if os.path.exists("Prover9"):
    os.system("rm -rf Prover9")
os.system("git clone -q https://github.com/jipsen/Prover9.git")

with open("/content/Prover9/Prover9.py") as f:
    code = compile(f.read(), "/content/Prover9/Prover9.py", "exec")
    exec(code, globals())

# ---------------------------------------------------------------------------
# 5. Bind the prover9 function name that Peter's p9 expects
# ---------------------------------------------------------------------------

from provers.prover9 import prover9 as _prover9
globals()["prover9"] = _prover9
