#!/bin/bash

DATA_DIR=$1

if [ -z "$DATA_DIR" ]
then
    echo "[run_all] Must specify DATA_DIR. Exiting."
    exit 1
fi

echo "Running full pipeline targeting $DATA_DIR"

python3 -m lean_proof_recording.pipeline.refresh
python3 -m lean_proof_recording.pipeline.insert_proof_recording_code

lean --make src/empty.lean
bash _target/deps/mathlib/scripts/mk_all.sh
mkdir "$DATA_DIR"

# python3 -m lean_proof_recording.pipeline.run_lean_and_save_results _target/deps/mathlib/src/category_theory/currying.lean "$DATA_DIR"
# python3 -m lean_proof_recording.pipeline.run_lean_and_save_results src/empty.lean "$DATA_DIR"
python3 -m lean_proof_recording.pipeline.run_lean_and_save_results _target/deps/mathlib/src/all.lean "$DATA_DIR"

python3 -m lean_proof_recording.pipeline.extract_trace_data "$DATA_DIR"
python3 -m lean_proof_recording.pipeline.extract_proof_data "$DATA_DIR"
python3 -m lean_proof_recording.pipeline.extract_training_testing_data "$DATA_DIR"
