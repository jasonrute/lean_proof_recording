import os
import argparse
from tqdm import tqdm

def _parse_main():
    parser = argparse.ArgumentParser()
    parser.add_argument("path", help="names file to be deduplicated")
    parser.add_argument("dest", help="destination for deduplicated names")

def _main(path: str, dest: str):
    name_dict = dict()
    with open(path, "r") as f:
        for l, line_count in enumerate(f):
            names = l.split()
            decl_nm = names[0]
            namespaces = names[1:]
            if decl_nm in name_dict:
                continue
            else:
                name_dict[decl_nm] = namespaces
    print(f"[deduplicate_names] READ {line_count} LINES, GOT {len(name_dict)} UNIQUE DECLARATIONS")

    with open(dest, "w") as f:
        for k, v in tqdm(name_dict.items(), total=len(name_dict)):
            f.write(" ".join([k] + v) + "\n")

if __name__ == "__main__":
    _main(**vars(_parse_main()))
