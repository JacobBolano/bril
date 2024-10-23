import pandas as pd

# Load the CSV file into a DataFrame
df = pd.read_csv('total_benchmarks.csv', header=None, names=['benchmark_name', 'optimization_name', 'number_instructions'])

# Initialize dictionaries to store percentage decreases and counts for each optimization
optimization_stats = {}

# Loop through each unique benchmark
for benchmark in df['benchmark_name'].unique():
    # Filter the DataFrame for the current benchmark
    benchmark_df = df[df['benchmark_name'] == benchmark]

    # Get the baseline instruction count
    baseline_instructions = benchmark_df[benchmark_df['optimization_name'] == 'actual_baseline']['number_instructions'].values[0]

    # Calculate the percentage decrease for each optimization (other than baseline)
    for _, row in benchmark_df.iterrows():
        if row['optimization_name'] != 'actual_baseline':
            percentage_decrease = ((baseline_instructions - row['number_instructions']) / baseline_instructions) * 100
            optimization_name = row['optimization_name']
            
            # Update the dictionary with percentage decreases for each optimization
            if optimization_name not in optimization_stats:
                optimization_stats[optimization_name] = []
            optimization_stats[optimization_name].append(percentage_decrease)

# Calculate the average percentage decrease for each optimization and write to a file
with open('analysis.txt', 'w') as file:
    # Write the individual percentage decreases for each benchmark
    for benchmark in df['benchmark_name'].unique():
        benchmark_df = df[df['benchmark_name'] == benchmark]
        baseline_instructions = benchmark_df[benchmark_df['optimization_name'] == 'actual_baseline']['number_instructions'].values[0]
        for _, row in benchmark_df.iterrows():
            if row['optimization_name'] != 'actual_baseline':
                percentage_decrease = ((baseline_instructions - row['number_instructions']) / baseline_instructions) * 100
                file.write(f"Benchmark: {row['benchmark_name']}, Optimization: {row['optimization_name']}, Percentage Decrease: {percentage_decrease:.2f}%\n")

    file.write("\nAverage percentage decrease per optimization:\n")
    
    # Write the average percentage decrease per optimization
    for optimization_name, decreases in optimization_stats.items():
        average_decrease = sum(decreases) / len(decreases)
        file.write(f"Optimization: {optimization_name}, Average Percentage Decrease: {average_decrease:.2f}%\n")

print("Analysis and average percentage decreases written to 'analysis.txt'")
