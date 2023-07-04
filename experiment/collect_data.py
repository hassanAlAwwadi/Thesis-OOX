import numpy as np
import pandas as pd

def main():
    file = 'benchmark'
    df = pd.read_csv(f"./results/{file}", delimiter=',')

    print(f"{len(df['name'].unique())} mutations checked")
    df = df[df['result'] != 'VALID']
    df = df.filter(items=['name', 'heuristic', 'time', 'result'])

    # Group on name and heuristic, average the execution time
    df = df.groupby(['name', 'heuristic'], as_index=False).agg("mean")



    df = df.sort_values(by=['name', 'heuristic'])
    df = df.filter(items=['heuristic', 'time'])

    print(df)


    # Pivot the table into one like this, with each row a mutation's execution time
    #     |DFS |M2DU|RandomPath|RoundRobin|
    # time| .. | .. | ..       | ..       |
    df = df.assign(idx=df.groupby('heuristic').cumcount())
    df = df.pivot(index='idx', columns='heuristic', values='time')

    print(f"{len(df)} invalid mutations found")

    df.columns = ['DFS', 'MD2U', 'RandomPath', 'RoundRobin']
    
    ax = df.plot.box()
    ax.set_ylabel('time (s)')

    ax.figure.savefig(f'./intermediate_results/{file}')

main()