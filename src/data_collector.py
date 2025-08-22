#!/usr/bin/env python3
import sys
import os
import json

def main():
    if len(sys.argv) != 2:
        print(f"Usage: python {sys.argv[0]} res/<model-approach>")
        sys.exit(1)

    folder = sys.argv[1]
    if not os.path.isdir(folder):
        print(f"Error: {folder} is not a valid directory")
        sys.exit(1)

    files = [f for f in os.listdir(folder) if f.endswith(".json")]
    files.sort(key=lambda x: int(os.path.splitext(x)[0]))

    for fname in files:
        n_value = os.path.splitext(fname)[0]
        print(f"--- N = {n_value} ---")
        fpath = os.path.join(folder, fname)
        with open(fpath, "r") as f:
            data = json.load(f)

        # Calcoliamo le larghezze massime per formattazione
        model_names = list(data.keys())
        max_model_len = max(len(m) for m in model_names)
        max_time_len = max(len(str(data[m].get("time", ""))) for m in model_names)
        max_opt_len = max(len(str(data[m].get("optimal", ""))) for m in model_names)
        max_obj_len = max(len(str(data[m].get("obj", ""))) for m in model_names)

        # Stampa allineata
        for model, results in data.items():
            time = results.get("time", "")
            optimal = results.get("optimal", "")
            obj = results.get("obj", "")
            print(
                f"{model.ljust(max_model_len)}  "
                f"{str(time).ljust(max_time_len)}  "
                f"{str(optimal).ljust(max_opt_len)}  "
                f"{str(obj).ljust(max_obj_len)}"
            )
        print()

if __name__ == "__main__":
    main()
