#!/bin/bash

DATA_DIR=$1

if [ -z "$DATA_DIR" ]
then
    echo "[run_all] Must specify DATA_DIR. Exiting."
    exit 1
fi

echo "Running full pipeline targeting $DATA_DIR"

python3 tools/refresh.py
python3 tools/insert_proof_recording_code.py
lean --make src/empty.lean
bash _target/deps/mathlib/scripts/mk_all.sh
mkdir "$DATA_DIR"
# python tools/run_lean_and_save_results.py _target/deps/mathlib/src/category_theory/currying.lean "$DATA_DIR"
# python3 tools/run_lean_and_save_results.py src/empty.lean "$DATA_DIR"
python3 tools/run_lean_and_save_results.py _target/deps/mathlib/src/all.lean "$DATA_DIR"
python3 tools/extract_trace_data.py "$DATA_DIR"
python3 tools/extract_proof_data.py "$DATA_DIR"
python3 tools/extract_training_testing_data.py "$DATA_DIR"
