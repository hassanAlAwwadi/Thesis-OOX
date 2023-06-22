import numpy as np
import pandas as pd

def f():
    df = pd.read_csv("./benchmark_experiment2_1", delimiter=',')

    df = df[df['result'] != 'VALID']
    df = df.filter(items=['name', 'heuristic', 'time', 'result'])

    # Group on name and heuristic, average the execution time
    df = df.groupby(['name', 'heuristic'], as_index=False).agg(lambda x: sum(x) / 3)


    df = df.sort_values(by=['name', 'heuristic'])
    df = df.filter(items=['heuristic', 'time'])
    


    # Pivot the table into one like this, with each row a mutation's execution time
    #     |DFS |M2DU|RandomPath|RoundRobin|
    # time| .. | .. | ..       | ..       |
    df = df.assign(idx=df.groupby('heuristic').cumcount())
    df = df.pivot(index='idx', columns='heuristic', values='time')


    df.columns = ['DFS', 'MD2U', 'RandomPath', 'RoundRobin']
    
    ax = df.plot.box()

    ax.figure.savefig('experiment')

f()