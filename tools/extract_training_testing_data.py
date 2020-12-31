from pathlib import Path
import sys
import pandas as pd 
import numpy as np

RAW_TRACED_DATA_DIR = "raw_traced_data"
EXTRACTED_PROOF_DATA_DIR = "extracted_proof_data"
CLEANED_TRAINING_DATA_DIR = "cleaned_training_data"

def gather_data_for_model(
    tactic_state_goal: pd.DataFrame,
    tactic_state: pd.DataFrame,
    tactics: pd.DataFrame
):
    # take first goal in each tactic state
    df = tactic_state_goal.copy()
    df = df[df['ix'] == 0]
    df['tactic_state_key'] = df['filename'] + ":" + df['tactic_state']
    df = df[['tactic_state_key', 'goal_pp']]
    df = df.set_index('tactic_state_key')

    # only use the tactic states which happen before the tactic is applied
    df2 = tactic_state.copy()
    df2 = df2[df2['before_after'] == 'before']
    df2['tactic_state_key'] = df2['filename'] + ":" + df2['key']
    df2['tactic_instance_key'] = df2['filename'] + ":" + df2['tactic_instance']
    df2['tactic_key'] = df2['tactic_instance_key'].apply(lambda k: ":".join(k.split(":")[:-1]))
    df2 = df2[['tactic_state_key', 'tactic_instance_key', 'tactic_key', 'decl_name', 'open_namespaces']]
    df2['decl_name'] = df2['decl_name'].str.replace("`", "")
    df2['open_namespaces'] = df2['open_namespaces'].str.replace("`", "")
    df2['open_namespaces'] = df2['open_namespaces'].str.replace(r"\[anonymous\] ?", "")
    df2 = df2.set_index('tactic_state_key')

    df = df.join(df2, how='inner')
    df = df.set_index('tactic_key')

    # join with the tactic commands
    df3 = tactics.copy()
    df3['tactic_key'] = df3['filename'] + ":" + df3['trace_key']
    df3 = df3[['tactic_key', 'filename', 'line', 'column', 'proof_key', 'code_string', 'class']]
    df3 = df3.rename(columns={'class': 'tactic_class', 'code_string': 'human_tactic_code'})
    df3 = df3.set_index('tactic_key')
    df = df.join(df3, how='inner')
    df = df.reset_index()
    df = df.drop(['tactic_key', 'tactic_instance_key'], axis='columns') 

    # remove solve1 tactics
    df = df[df['tactic_class'] != 'solve1']
    
    # clean input
    df['cleaned_goal'] = (
        df['goal_pp']
        # remove tags
        .str.replace(r"^[^:⊢]*\n", "")
        # remove pp indenting (including extra line wraps)
        .str.replace(r"\n +", " ") 
        # replace new lines with tabs
        .str.replace(r"\n", "\t")
    )

    # train-test-validate split based on proof_key
    proof_keys = df['proof_key'].unique()
    rng = np.random.default_rng(seed=0)
    tvt = rng.choice(['train', 'valid', 'test'], p=[0.8, 0.1, 0.1], size=len(proof_keys))
    tvt_split = pd.Series(tvt, index=proof_keys)
    tvt_split
    df['split'] = df['proof_key'].map(tvt_split) 

    return df

def main():
    assert len(sys.argv) == 2
    data_dir = Path(sys.argv[1])
    assert data_dir.exists(), data_dir
    assert data_dir.is_dir(), data_dir

    # load previously extracted data
    tactic_state_goal = pd.read_json(data_dir / RAW_TRACED_DATA_DIR / 'tactic_state_goal.json', orient='records')
    tactic_state = pd.read_json(data_dir / RAW_TRACED_DATA_DIR / 'tactic_state.json', orient='records')
    tactics = pd.read_json(data_dir / EXTRACTED_PROOF_DATA_DIR / 'tactics.json', orient='records')

    # process
    full_data = gather_data_for_model(tactic_state_goal, tactic_state, tactics)

    # save to files
    cleaned_data_dir = data_dir / CLEANED_TRAINING_DATA_DIR 
    cleaned_data_dir.mkdir(exist_ok=True)

    full_data.to_csv(cleaned_data_dir / "data_and_metadata.csv")
    for split in ['train', 'valid', 'test']:
        data_split = full_data[full_data['split'] == split]
        for src_tgt in ['src', 'tgt', 'names']:
            path = cleaned_data_dir / f"{split}.{src_tgt}"
            if src_tgt == "src":
                data = data_split['cleaned_goal']
            elif src_tgt == "tgt":
                data = data_split['human_tactic_code']
            elif src_tgt == "names":
                data = data_split['decl_name'] + " " + data_split['open_namespaces']
            else:
                raise Exception("Unreachable code reached")
            path.touch()
            path.write_text("\n".join(data))

if __name__ == "__main__":
    main()
