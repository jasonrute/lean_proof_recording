import json
import os
from pathlib import Path
import shutil
import subprocess


def _main():
    """
    Refreshes the Lean setup:

    - Deletes the target directory.
    - Refresh Lean and Mathlib according to what's in leanpkg.toml.
    - Copy base lean files from elan to `_target/deps/lean/library/`
    - Change leanpkg.path to point to the local lean files.
    """
    # delete _target
    print()
    print("==========================")
    print("Remove `_target` directory")
    print("==========================")
    _target = Path("_target")
    if _target.is_dir():
        print("_target directory found.")
        shutil.rmtree(_target)
        print("_target directory removed.")
    else:
        print("No _target directory.")

    # build lean according to leanpkg.toml
    print()
    print("================================")
    print("Configure and build lean project")
    print("================================")
    os.system("leanproject build")

    # copy lean files
    print()
    print("===================================================")
    print("Copy base lean library to _target/deps/lean/library")
    print("===================================================")
    #   get path from lean
    print("Getting lean paths.")
    with subprocess.Popen(
        ["lean", "--path"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT
    ) as out:
        stdout, stderr = out.communicate()
    assert stderr is None, stderr
    s = stdout.decode("utf-8")
    path_data = json.loads(s)
    lean_library = None
    for p in path_data["path"]:
        if p.endswith("lean/library"):
            lean_library = Path(p)
            break
    assert lean_library is not None
    print("Found lean library path: ", lean_library)
    print("Copying lean libary to _target/deps/lean/library ...")
    (_target / "deps" / "lean").mkdir()
    shutil.copytree(lean_library, _target / "deps" / "lean" / "library")

    # change leanpkg.path
    print("")
    print("=============================================")
    print("Change lean path to _target/deps/lean/library")
    print("=============================================")
    path_file = Path("leanpkg.path")
    lines = []
    with open(path_file, "r") as f:
        for line in f:
            lines.append(line.replace("builtin_path", "path _target/deps/lean/library"))
    with open(path_file, "w") as f:
        f.writelines(lines)
    print("Path changed")


if __name__ == "__main__":
    _main()
