from m2_functions import *
from itertools import combinations
import re
import os
from itertools import combinations
from itertools import combinations
from concurrent.futures import ProcessPoolExecutor, TimeoutError

TIMEOUT_SECONDS = 60  # Measured in seconds

def read_problem(file_path):
    """
    Reads a physics problem from a structured TXT file and returns a dictionary with:
    - variables (list)
    - equations (list)
    - measured_vars (list) 
    - target (str)
    """
    with open(file_path, 'r') as f:
        content = f.read().strip()
    
    data = {
        'variables': [],
        'equations': [],
        'measured_vars': [],
        'non_measured_vars': [],
        'target': ''
    }
    
    # Extract variables
    vars_match = re.search(r'Variables:\s*\[(.*?)\]', content)
    if vars_match:
        vars_str = vars_match.group(1)
        # Handle both " and ' quotes and remove whitespace
        data['variables'] = [v.strip().strip('"').strip("'") for v in vars_str.split(',')]
    
    # Extract equations
    eqs_match = re.search(r'Equations?:\s*(.*?)(?=\n\nMeasured)', content, re.DOTALL)
    if eqs_match:
        eqs_str = eqs_match.group(1).strip()
        data['equations'] = [eq.strip() for eq in eqs_str.split('\n') if eq.strip()]
    
    # Extract measured variables
    measured_match = re.search(r'Measured Variables:\s*\[(.*?)\]', content)
    if measured_match:
        measured_str = measured_match.group(1)
        data['measured_vars'] = [v.strip().strip('"').strip("'") for v in measured_str.split(',')]
        data['non_measured_vars'] = list(set(data['variables']) - set(data['measured_vars']))
    
    # Extract target polynomial
    target_match = re.search(r'Target Polynomial:\s*(.*?)$', content, re.DOTALL)
    if target_match:
        data['target'] = target_match.group(1).strip()
    
    return data

def run_abduction_with_timeout(args):
    vars, measured_vars, non_measured_vars, remaining_axioms, target, filename, removed_axioms = args
    try:
        abductive_inference(vars, measured_vars, non_measured_vars, remaining_axioms, target, filename, removed_axioms)
        return "completed"
    except Exception as e:
        return f"error: {e}"

def run_dimensionality_check_with_timeout(args):
    vars, axioms, target, removed_axioms, filename = args
    try:
        return check_axiom_dimensions(vars, axioms, target, removed_axioms, filename)
    except Exception as e:
        return f"error: {e}"

def main():
    problems_list = [
        #'kepler', 
        #'einstein', 
        #'light', 
        #'decay', 
        #'escape_velocity', 
        #'hagen', 
        #'hall', 
        #'inelastic_collision', 
        #'kepler_2', 
        #'photoHall', 
        #'photoHall_2', 
        #'waves', 
        #'compton', 
        'light_2',
        #"test",
        #'kepler_4'
        ]

    for problem_name in problems_list:
        filepath = f"systems_and_phenomena/real/{problem_name}/system.txt"
        problem_data = read_problem(filepath)

        vars = problem_data['variables']
        axioms = problem_data['equations']
        measured_vars = problem_data['measured_vars']
        non_measured_vars = problem_data['non_measured_vars']
        target = problem_data['target']
        
        print(f"Problem: {problem_name}")
        output_dir = f'results/real/{problem_name}/'
        os.makedirs(output_dir, exist_ok=True)

        with open(f'{output_dir}/data.txt', 'w') as f:
            f.write(f"Variables: {vars}\n")
            f.write(f"Measured Variables: {measured_vars}\n")
            f.write(f"Non-Measured Variables: {non_measured_vars}\n")
            f.write(f"Axioms: {axioms}\n")
            f.write(f"Target: {target}\n")

        ##### Projection #####
        print("Running Projection")
        filename = os.path.join(output_dir,f'projection.txt')
        projection(vars, axioms, measured_vars, non_measured_vars, filename)

        ##### Abductive Inference with Timeout #####
        with ProcessPoolExecutor() as executor:
            for n in range(1, len(axioms) + 1):
                indices = list(range(len(axioms)))
                for combo_indices in combinations(indices, n):
                    removed_axioms = [axioms[i] for i in combo_indices]
                    remaining_axioms = [axioms[i] for i in indices if i not in combo_indices]

                    combo_str = '_'.join(str(i + 1) for i in combo_indices)
                    output_dir_inference = f'{output_dir}/{n}_axiom(s)_removed'
                    os.makedirs(output_dir_inference, exist_ok=True)
                    filename = os.path.join(output_dir_inference, f'abduction_{combo_str}.txt')

                    print(f"Running abductive inference by removing axioms {combo_indices}")
                    future = executor.submit(run_abduction_with_timeout, (vars, measured_vars, non_measured_vars, remaining_axioms, target, filename, removed_axioms))
                    try:
                        result = future.result(timeout=TIMEOUT_SECONDS)
                        if result != "completed":
                            with open(filename, 'w') as f:
                                f.write(f"Abduction skipped due to error: {result}\n")
                    except TimeoutError:
                        with open(filename, 'w') as f:
                            f.write(f"Abduction skipped due to timeout after {TIMEOUT_SECONDS} seconds\n")
                        print(f"Timed out: {filename}")

        ##### Dimensionality Checks with Timeout #####
        dim_check_dir = f'{output_dir}/dimensionality_check'
        os.makedirs(dim_check_dir, exist_ok=True)
        all_aggregate_results = {}

        with ProcessPoolExecutor() as executor:
            for n in range(1, len(axioms) + 1):
                n_dir = os.path.join(dim_check_dir, f"{n}_axioms_removed/")
                os.makedirs(n_dir, exist_ok=True)

                n_results = {
                    'total_subsets': 0,
                    'dimension_counts': {},
                    'equal_dimension': 0,
                }

                all_combos = list(combinations(axioms, n))
                for count, subset in enumerate(all_combos, 1):
                    removed_axioms = list(subset)
                    filename = os.path.join(n_dir, f"subset_{count}_dimcheck.txt")
                    print(f"Running dimension check {count}/{len(all_combos)} for n={n}")

                    future = executor.submit(run_dimensionality_check_with_timeout,
                                             (vars, axioms, target, removed_axioms, filename))
                    try:
                        result = future.result(timeout=TIMEOUT_SECONDS)
                        if isinstance(result, dict):
                            n_results['total_subsets'] += 1
                            dim = result['discovered_dimension']
                            n_results['dimension_counts'][dim] = n_results['dimension_counts'].get(dim, 0) + 1
                            if result['dimensions_equal']:
                                n_results['equal_dimension'] += 1
                        else:
                            with open(filename, 'w') as f:
                                f.write(f"Check skipped due to error: {result}\n")
                    except TimeoutError:
                        with open(filename, 'w') as f:
                            f.write(f"Check skipped due to timeout after {TIMEOUT_SECONDS} seconds\n")
                        print(f"Timed out: {filename}")

                # Save per-n results
                with open(os.path.join(n_dir, "aggregate_results.txt"), 'w') as f:
                    f.write(f"=== Results for removing {n} axioms ===\n")
                    f.write(f"Total subsets tested: {n_results['total_subsets']}\n")
                    f.write("Dimension distribution:\n")
                    for dim, count in sorted(n_results['dimension_counts'].items()):
                        f.write(f"  Dimension {dim}: {count} cases\n")
                    f.write(f"Cases with equal dimension: {n_results['equal_dimension']}\n")

                all_aggregate_results[n] = n_results

            # Cross-n summary
            total_subsets = sum(r['total_subsets'] for r in all_aggregate_results.values())
            total_equal = sum(r['equal_dimension'] for r in all_aggregate_results.values())
            combined_dim_counts = {}
            for r in all_aggregate_results.values():
                for dim, count in r['dimension_counts'].items():
                    combined_dim_counts[dim] = combined_dim_counts.get(dim, 0) + count

            with open(os.path.join(dim_check_dir, "cross_n_aggregate.txt"), 'w') as f:
                f.write("=== Aggregate Results Across All Subset Sizes ===\n")
                for n, r in all_aggregate_results.items():
                    f.write(f"\nFor {n}-axiom removals:\n")
                    f.write(f"  Total subsets: {r['total_subsets']}\n")
                    f.write(f"  Equal dimensions: {r['equal_dimension']} ({r['equal_dimension']/r['total_subsets']:.1%})\n")
                    f.write("  Dimension distribution:\n")
                    for dim, count in sorted(r['dimension_counts'].items()):
                        f.write(f"    {dim}: {count}\n")
                f.write("\n=== Grand Totals Across All Subset Sizes ===\n")
                f.write(f"Total subsets tested: {total_subsets}\n")
                f.write(f"Total cases with equal dimensions: {total_equal}\n")
                f.write(f"Percentage with equal dimensions: {total_equal/total_subsets:.1%}\n")
                f.write("Combined dimension distribution:\n")
                for dim, count in sorted(combined_dim_counts.items()):
                    f.write(f"  Dimension {dim}: {count} cases\n")


if __name__ == '__main__':
    main()
