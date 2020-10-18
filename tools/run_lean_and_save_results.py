import sys
import json
import subprocess
from pprint import pprint
import shutil
import os
from pathlib import Path

def save_leanpkg_info(out_directory):
    shutil.copy2('leanpkg.toml', out_directory+'leanpkg.toml')

def run_command(command):
    with subprocess.Popen(command, 
           stdout=subprocess.PIPE, 
           stderr=subprocess.STDOUT) as out:
        return out.communicate()

def get_lean_paths():
    print("getting lean paths...")
    stdout, stderr = run_command(['lean', '--path'])
    assert stderr is None, stderr
    s = stdout.decode("utf-8")
    d = json.loads(s)
    paths = [p.replace("/./", "/").replace("/bin/../", "/") 
            for p in d['path']]
    return paths

def rename_paths(paths):
    # just use last two directories in path
    path_map = {}
    for p in paths:
        dirs = p.split("/")
        path_map[p] = dirs[-2] + "/" + dirs[-1]
    return path_map

def save_path_map(path_map, out_directory):
    with open(out_directory+"path_map.json", 'w') as f:
        s = json.dumps(path_map)
        f.write(s)

def get_lean_files(paths):
    file_paths = []
    for p in paths:
        for root, dirs, files in os.walk(p):
            for file_name in files:
                if file_name.endswith(".lean"):
                    file_paths.append(os.path.join(root, file_name))
    return file_paths

def save_lean_files(path_map, lean_files, out_directory):
    for file_path in lean_files:
        for p in path_map:
            if file_path.startswith(p):
                file_suffix = file_path[len(p):]
                new_file_path = out_directory+"lean_files/"+path_map[p]+file_suffix
                os.makedirs(os.path.dirname(new_file_path), exist_ok=True)
                shutil.copy2(file_path, new_file_path)
                break

def delete_oleans(lean_files):
    for file_path in lean_files:
        olean = Path(file_path.replace(".lean", ".olean"))
        if olean.exists():
            olean.unlink()  # deletes olean file

def run_lean_make(filename, out_directory):
    print("running lean on", filename, "...")
    with open(out_directory+"lean_stdout.log", "w+b") as stdout_file:
        with open(out_directory+"lean_stderr.log", "w+b") as stderr_file:
            print("piping stdout to", stdout_file.name, "...")
            print("piping stderr to", stderr_file.name, "...")
            out = subprocess.Popen(
                ['lean', '--make', '--json', '-D pp.colors=true', filename], 
                stdout=stdout_file, 
                stderr=stderr_file
            )
            out.communicate()
            stderr = stderr_file.readlines()
            assert not stderr, "".join(stderr)

def parse_stdout(stdout):
    print("parsing output")
    info_blocks = []
    for line in stdout:
        if line:
            s = line.decode("utf-8")
            d = json.loads(s)
            if d['severity'] == 'information' and d['caption'] == "trace output":
                info_blocks.append(d)
            else:
                print("Unexpected output:")
                pprint(d)

    return info_blocks

def save_traced_data(info_blocks, out_directory):
    print("saving traced data")
    with open(out_directory+"output.json", 'w') as f:
        for info in info_blocks:
            s = json.dumps(info) + "\n"
            f.write(s)

def run_lean_file_and_save_output(lean_file, out_directory):
    assert lean_file.endswith(".lean")
    assert out_directory.endswith("/")

    # save version information
    save_leanpkg_info(out_directory)

    # save path information
    paths = get_lean_paths()
    path_map = rename_paths(paths)
    save_path_map(path_map, out_directory)

    # save and touch lean files 
    # (touching them forces the proof recording on all 
    # dependencies since it invalidates the .olean files)
    file_paths = get_lean_files(paths)
    save_lean_files(path_map, file_paths, out_directory)
    delete_oleans(file_paths)

    # the big step.  Run lean --make --json and pipe output to file
    stdout = run_lean_make(lean_file, out_directory)

    # TODO: Move these steps to another script.
    #info_blocks = parse_stdout(stdout)
    #save_traced_data(info_blocks, out_directory)
    #save_lean_files_old(path_map, info_blocks, out_directory)

def main():
    assert len(sys.argv) == 3
    lean_file = sys.argv[1]
    out_directory = sys.argv[2]
    run_lean_file_and_save_output(lean_file, out_directory)

if __name__ == "__main__":
    main()
