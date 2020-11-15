python3 tools/refresh.py
python3 tools/insert_proof_recording_code.py
lean --make src/empty.lean
bash _target/deps/mathlib/scripts/mk_all.sh
mkdir ./data
python3 tools/run_lean_and_save_results.py _target/deps/mathlib/src/all.lean ./data
python3 tools/extract_trace_data.py ./data
python3 tools/extract_proof_data.py ./data
python3 tools/extract_training_testing_data.py ./data