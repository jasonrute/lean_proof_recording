import sys
import json
import subprocess
from pprint import pprint
import shutil
import os

def run_command(command):
    out = subprocess.Popen(command, 
           stdout=subprocess.PIPE, 
           stderr=subprocess.STDOUT)
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

def run_file(filename):
    print("running file...")
    stdout, stderr = run_command(['lean', '--json', '-D pp.colors=true', filename])
    assert stderr is None, stderr
    return stdout

def parse_stdout(stdout):
    print("parsing output")
    info_blocks = []
    for line in stdout.split(b'\n'):
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

def save_lean_files(path_map, info_blocks, out_directory):
    print("saving lean files")
    files = set()
    for info in info_blocks:
        filename = info['file_name'] 
        files.add(filename)
    
    for filename in files:
        for p in path_map:
            if filename.startswith(p):
                file_suffix = filename[len(p):]
                new_filename = out_directory+path_map[p]+file_suffix
                os.makedirs(os.path.dirname(new_filename), exist_ok=True)
                shutil.copy2(filename, new_filename)
                break

def run_lean_file_and_save_output(lean_file, out_directory):
    assert lean_file.endswith(".lean")
    assert out_directory.endswith("/")

    paths = get_lean_paths()
    path_map = rename_paths(paths)
    save_path_map(path_map, out_directory)

    stdout = run_file(lean_file)
    info_blocks = parse_stdout(stdout)
    save_traced_data(info_blocks, out_directory)
    
    save_lean_files(path_map, info_blocks, out_directory)

def main():
    assert len(sys.argv) == 3
    lean_file = sys.argv[1]
    out_directory = sys.argv[2]
    run_lean_file_and_save_output(lean_file, out_directory)

if __name__ == "__main__":
    main()
