import os
files = os.listdir("./benchmark_programs/experiment2/LinkedList/mutations")

files = sorted(files)

files.remove('.gitignore')


print(len(files))

def main(files, sample_amount_percentage: int):
    import random
    files = random.sample(files, int((len(files) * sample_amount_percentage) / 100))
    # print(files)
    for file in files:
        print(file)
        k = 90
        heuristics = ['depth-first-search', 'random-path', 'min-dist2-uncovered', 'round-robin-md2u-random-path']
        

        for h in heuristics:
            command = f'cargo run --release -- verify ./benchmark_programs/experiment2/LinkedList/mutations/{file} -f Main.test -k {k} --time-budget 30 -s 5 --heuristic {h} --run-as-benchmark -q'

            result = os.system(command)

main(files, 100)

