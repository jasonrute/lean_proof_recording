# Proof recording in Lean 3

This is proof recording code for Lean 3 associated with the paper
[Proof Artifact Co-training for
Theorem Proving with Language Models](https://arxiv.org/abs/2102.06203).

## Prerequesites

Have `elan` and `leanproject` installed. The scripts require Python 3.7+.

## Recommended setup

```bash
python3 -m venv venv  # new virtual env
source ./venv/bin/activate
pip install .  # or  pip install -e .  for editable mode
```

## TLDR Workflow

Only tested on mac and linux.

- Make an empty directory to store the data.
- Run `bash ./scripts/run_all.sh $DATA_DIR`.

This will take from many minutes to many hours based on the available
parallelization.  The data needed to train a language model can be found in
`$DATA_DIR/cleaned_training_data`.

## Extended Workflow

This will go through the steps of the master script and describe the various
types of recorded data, which may be of interest to various researchers.
Only tested on mac and linux.

### Nonstandard Lean Setup

This tool works by modifying lean code so that it traces proof step information. It does this with
a combination of python scripts and some lean hacks. No files outside of this directory are
modified, so you don't have to worry about messing up your lean install.

Run this command to build lean, and populate `_target` with both `mathlib` and `lean/library` code.
It also makes some unstable modifications to `leanpkg.path`.

```bash
python3 -m lean_proof_recording.pipeline.refresh
```

Run this command to modify the lean and mathlib files. (Note, the modifications are only to files in
`_target` and can be undone with the refresh command above. Use the flag `--dryrun` to see what will
be modified without modifying it.)

```bash
python3 -m lean_proof_recording.pipeline.insert_proof_recording_code
```

(Optional) It's helpful to compile the base lean to make sure the modifications worked. No trace
code will show since certain options are not set.

```bash
lean --make src/empty.lean
```

Build `all.lean` for mathlib.

```bash
bash _target/deps/mathlib/scripts/mk_all.sh
```

### Tracing

This command generates data. This is very time consuming (many hours). The data directory must exist
and is encouraged to be empty. Replace `src/empty.lean` with `_target/deps/mathlib/src/all.lean` to
trace all of mathlib.

```bash
python3 -m lean_proof_recording.pipeline.run_lean_and_save_results src/empty.lean <path/to/data/directory>
```

After this completes, the data directory (which you supplied above) will have the following
structure.

* `lean_files` A copy of all the (modified) lean files. These will be used to extract other
  information in the next steps.
* `leanpkg.toml` A copy of this file which records the version of lean and mathlib for
  reproducibility.
* `path_map.json` Information connecting the paths which are in the trace data to the new paths in
  this dataset.
* `lean_stdout.log` The traced results of the run. Since `lean` was run with `--json` all lean
  outputs are in json form. Later steps will parse this data.
* `lean_stderr.log` Any errors (but not regular lean compile errors.) Check to make sure this file
  is empty.

### Extract data

Run this command to extract the traced data into a series of tables.

```bash
python3 -m lean_proof_recording.pipeline.extract_trace_data <path/to/data/directory>
```

This will add the following to the data directory:

* `lean_errors.jsonl` This includes all Lean messages from the run which are not informational
  traces. This includes any Lean compiliation errors. Check that there are no messages.
* `raw_traced_data` This is a collection of relational tables containing the traced data (along with
  the filename and position of the trace). You can load the files into a `pandas` dataframe as
  follows:

```python
pd.read_json("path/to/file.jsonl", orient="records", lines=True)
````

(Further cleaning may be neccessary to properly handle missing values.) Each row (within a table) is
uniquely keyed by the "filename" and "key" columns.

Run this command to parse the Lean code proofs. This will use the traced data to guide a custom (and
ad-hoc) Lean code parser to parse all tactic proofs into their respective tactics. It will also
parse the tactic arguments.

```bash
python3 -m lean_proof_recording.pipeline.extract_proof_data <path/to/data/directory>
```

This script will add a directory `extacted_proof_data` to the data directory. It contains the
following `jsonl` files:

* `proof_trees.jsonl` This includes JSON ASTs for every proof. (Note, this doesn't include term
  proofs, and for various reasons a Lean theorem can be have multiple associated proofs. Roughly
  speaking, but with some exceptions, a tactic proof is one which is started by the `by` or `begin`
  keywords.)
* `proof.jsonl` A 2D table of data for each proof. Use the `key` column to relate to the other data
  structures.
* `tactic.jsonl` A 2D table of data for each tactic command. Use the `key` column to relate to the
  other data structures.
* `args.jsonl` A 2D table of data for each tactic command argument. Use the `key` column to relate
  to the other data structures.

### Extract training data

This file step is to condense the currently extracted data into training data suitable for training
a language model.

```bash
python3 -m lean_proof_recording.pipeline.extract_training_testing_data <path/to/data/directory>
```

This will filter and clean the data slighlty as well as split the data into training (92%),
validation (4%), and testing (4%).  The split is deterministic based on a hash of the declaration
name, allowing intercompatibility with other sources of lean data and other lean environments.

## Putting it all together

For ease of understanding the data, an [example notebook](data_examples.ipynb) is included.

## Customizations and Improvements

### Set the version of Lean and Mathlib

Edit the `leanpkg.toml` file to change the version of lean and mathlib. This
is really important to maintain exact compatability with other projects. (Double
check after running the `refresh.py` script above that the versions are the
same as you set them.)

### Add new tracing code

The information traced by these tools may not be the information that another user needs.

For that reason, these tools make it easy to add custom tracing code. The tracing code is stored in
`lean_modifications`. Feel free to add additional traces (following the examples there). The best
places to add new code are where it is labeled "BEGIN/END CUSTOMIZABLE CODE".

Some additional ideas for tracing:

* Trace goal, hypothesis, or parameter expressions into another form, e.g. as s-expressions (or
  other abstract syntax tree) or using the pp.all=true form
* Trace type information about expressions or their parts. For example, knowing is an expression is
  of type Prop or not
* Trace simp lemmas available in the environment

All of these are fairly easy to add, but may slow down the time to trace all of mathlib.
