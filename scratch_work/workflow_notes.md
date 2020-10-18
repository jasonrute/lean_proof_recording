initialize lean and mathlib to a particular version using leanproject as normal
git clone lean 
- find github location and version in the leanpkg.toml file
- git clone https://github.com/leanprover-community/lean.git _lean
- cd _lean
- git checkout v3.20.0
- 
modify lean so that I can change files
change lean files
- automatic changes
- optional manual changes
create all.lean
begin proof recording at all.lean (but customizable to other files)
- run lean
- save traces to file(s) to data directory
- save lean files being traced to data directory
- record version numbers
extract data from data directory (no dependence on lean/mathlib after this)


requirements.txt
_lean*
_target*
data
 raw_data*
 extracted_data
tools
  setup.py
  modify_lean.py
  run_lean_and_save_results.py
  tokenize_lean_files.py
  extract_tactic_commands.py
  extract_tactic_arguments.py
  extract_tactic_commands.py
  extract_rewrite_commands.py
examples
  proof_recording_examples.lean
  ...
README.md
process_data.ipynb