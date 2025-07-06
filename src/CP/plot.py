import os
import json
import matplotlib.pyplot as plt
import pandas as pd

# === CONFIGURAZIONE ===
cartella_json = "../../res/CP"  # o "." se i file sono nella cartella corrente
metriche = ["time", "obj"]  # puoi aggiungere anche 'optimal' se ti interessa
modelli = set()

# === Raccolta dati ===
dati = {}

for nome_file in os.listdir(cartella_json):
    if nome_file.endswith(".json"):
        n = int(nome_file.replace(".json", ""))
        with open(os.path.join(cartella_json, nome_file)) as f:
            contenuto = json.load(f)

        dati[n] = {}
        for modello, risultati in contenuto.items():
            modelli.add(modello)
            dati[n][modello] = {metrica: risultati.get(metrica, None) for metrica in metriche}

# === Organizzazione in DataFrame ===
modelli = sorted(modelli)
records = []

for n in sorted(dati.keys()):
    for modello in modelli:
        info = dati[n].get(modello, {})
        record = {"n": n, "model": modello}
        record.update(info)
        records.append(record)

df = pd.DataFrame.from_records(records)

# === Plot: tempo e obj ===
def plot_metric(metrica, ylabel=None):
    plt.figure(figsize=(10, 5))
    for modello in df["model"].unique():
        df_mod = df[df["model"] == modello]
        plt.plot(df_mod["n"], df_mod[metrica], marker='o', label=modello)
    plt.xlabel("n")
    plt.ylabel(ylabel or metrica)
    plt.title(f"{metrica} per istanza")
    plt.legend()
    plt.grid(True)
    plt.tight_layout()
    plt.show()

def plot_time_logscale():
    plt.figure(figsize=(10, 5))
    epsilon = 1e-3  # piccolo valore positivo per sostituire gli 0 (evita problemi su scala log)
    
    for modello in df["model"].unique():
        df_mod = df[df["model"] == modello].copy()
        df_mod["time"] = df_mod["time"].replace(0, epsilon)
        plt.plot(df_mod["n"], df_mod["time"], marker='o', label=modello)

    plt.xlabel("n")
    plt.ylabel("Tempo (s) [log scale]")
    plt.yscale("log")
    plt.title("Tempo per istanza (scala logaritmica)")
    plt.legend()
    plt.grid(True, which="both", linestyle="--", linewidth=0.5)
    plt.tight_layout()
    plt.show()



plot_metric("time", "Tempo (s)")
plot_time_logscale()
plot_metric("obj", "Valore funzione obiettivo")

# (Opzionale) plot per 'optimal'
if "optimal" in metriche:
    plt.figure(figsize=(10, 5))
    for modello in df["model"].unique():
        df_mod = df[df["model"] == modello]
        y = [1 if val is True else 0 for val in df_mod["optimal"]]
        plt.plot(df_mod["n"], y, marker='o', label=modello)
    plt.xlabel("n")
    plt.ylabel("Optimal (1 = True)")
    plt.title("Raggiungimento dell'ottimo")
    plt.legend()
    plt.grid(True)
    plt.tight_layout()
    plt.show()