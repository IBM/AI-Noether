#!/usr/bin/env python3
"""
AI-Noether: Plot Coefficient Error vs Noise Level with Recovery Rates

Standalone script to visualize noisy recovery results.
Generates three types of graphs:
1. Bar graph of coefficient error with completion rates (original)
2. Bar graph filtered to only include cases with correct component count
3. Heatmap of component recovery rates across problems/noise/axioms removed

Usage:
    python plot_noise_results.py --results-dir results
"""

import os
import re
import argparse
import glob
from typing import Dict, List, Optional, Tuple, Any
from collections import defaultdict
from dataclasses import dataclass, field

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import matplotlib.colors as mcolors
from matplotlib.colors import LinearSegmentedColormap
from matplotlib.lines import Line2D
import numpy as np


# Subtle, professional color palette
COLORS = {
    '1e-2': '#6B8E9B',   # Muted teal
    '1e-5': '#9B8E6B',   # Muted gold
    '1e-8': '#8E6B9B',   # Muted purple
}

FALLBACK_COLORS = ['#7BA3B0', '#B0A37B', '#A37BB0', '#7BB0A3', '#B07B7B']

# Colors for axiom removal indicators
AXIOM_COLORS = {
    1: '#2ECC71',  # Green for 1 axiom
    2: '#3498DB',  # Blue for 2 axioms
    3: '#E74C3C',  # Red for 3 axioms
}

# Problems to analyze
DEFAULT_PROBLEMS = [
    'kepler', 'decay', 'compton', 'hall', 'escape_velocity',
    'inelastic_collision', 'light', 'pendulum', 'photoHall', 'time_dilation'
]

# Display names for problems (cleaner formatting)
PROBLEM_DISPLAY_NAMES = {
    'kepler': 'Kepler',
    'decay': 'Decay',
    'compton': 'Compton',
    'hall': 'Hall',
    'escape_velocity': 'Escape Vel.',
    'inelastic_collision': 'Inelastic',
    'light': 'Light',
    'pendulum': 'Pendulum',
    'photoHall': 'Photo-Hall',
    'time_dilation': 'Time Dil.',
    'bode': 'Bode',
}


@dataclass
class ComboResult:
    """Results for a single combo (axiom removal combination)."""
    num_removed: int
    combo_index: int
    coefficient_error: Optional[float] = None
    noisy_num_components: Optional[int] = None
    noiseless_num_components: Optional[int] = None
    timed_out: bool = False
    
    @property
    def completed(self) -> bool:
        return self.coefficient_error is not None and not self.timed_out
    
    @property
    def correct_components(self) -> bool:
        if self.noisy_num_components is None or self.noiseless_num_components is None:
            return False
        return self.noisy_num_components == self.noiseless_num_components


@dataclass
class ProblemResults:
    """All results for a single problem."""
    # Results organized by noise_level -> num_removed -> list of ComboResults
    results: Dict[str, Dict[int, List[ComboResult]]] = field(default_factory=lambda: defaultdict(lambda: defaultdict(list)))


def parse_num_components_from_summary(filepath: str, debug: bool = False) -> Optional[int]:
    """Parse number of components from a summary.txt file."""
    if not os.path.exists(filepath):
        if debug:
            print(f"  DEBUG: File does not exist: {filepath}")
        return None
    
    try:
        with open(filepath, 'r') as f:
            content = f.read()
        
        # Look for component count in summary files
        patterns = [
            r'Number of components:\s*(\d+)',
            r'Number of witness set components:\s*(\d+)',
            r'Num components:\s*(\d+)',
        ]
        
        for pattern in patterns:
            match = re.search(pattern, content, re.IGNORECASE)
            if match:
                count = int(match.group(1))
                if debug:
                    print(f"  DEBUG: Found {count} components in {filepath} (pattern: {pattern})")
                return count
        
        if debug:
            print(f"  DEBUG: No component count found in {filepath}")
            # Print first 500 chars of file for debugging
            print(f"  DEBUG: File content preview: {content[:500]}")
        return None
    except Exception as e:
        if debug:
            print(f"  DEBUG: Error reading {filepath}: {e}")
        return None


def find_component_count_in_combo(combo_dir: str, debug: bool = False) -> Optional[int]:
    """Find component count from summary.txt in a combo directory."""
    if debug:
        print(f"  DEBUG: Looking for components in combo_dir: {combo_dir}")
    
    # Check summary.txt directly in combo directory
    summary_path = os.path.join(combo_dir, 'summary.txt')
    count = parse_num_components_from_summary(summary_path, debug=debug)
    if count is not None:
        return count
    
    # Also check subdirectories for summary files
    for root, dirs, files in os.walk(combo_dir):
        for fname in files:
            if 'summary' in fname.lower() and fname.endswith('.txt'):
                filepath = os.path.join(root, fname)
                if filepath != summary_path:  # Don't re-check
                    count = parse_num_components_from_summary(filepath, debug=debug)
                    if count is not None:
                        return count
    
    if debug:
        print(f"  DEBUG: No summary file found in {combo_dir}")
    return None


def parse_coefficient_error(filepath: str) -> Optional[float]:
    """Parse coefficient L2 error from a file."""
    if not os.path.exists(filepath):
        return None
    
    try:
        with open(filepath, 'r') as f:
            content = f.read()
        
        patterns = [
            r'[Cc]oefficient[_ ]L2[_ ]error:\s*([\d.eE+-]+)',
            r'coefficient_l2_error:\s*([\d.eE+-]+)',
            r'Coefficient distance:\s*([\d.eE+-]+)',
        ]
        
        for pattern in patterns:
            match = re.search(pattern, content)
            if match:
                return float(match.group(1))
        
        return None
    except Exception:
        return None


def find_best_error_in_combo(combo_dir: str) -> Optional[float]:
    """Find the best coefficient error in a combo directory."""
    best_error = None
    
    for root, dirs, files in os.walk(combo_dir):
        for fname in files:
            if fname.endswith('.txt'):
                filepath = os.path.join(root, fname)
                error = parse_coefficient_error(filepath)
                if error is not None:
                    if best_error is None or error < best_error:
                        best_error = error
    
    return best_error


def collect_all_results(
    results_dir: str,
    problems: List[str],
    noise_levels: List[str],
    num_axioms_removed: List[int] = [1, 2, 3],
    debug: bool = False
) -> Dict[str, ProblemResults]:
    """Collect comprehensive results for all problems."""
    all_results = {}
    
    if debug:
        print("\n" + "="*80)
        print("DEBUG: Starting result collection")
        print("="*80)
    
    for problem in problems:
        problem_results = ProblemResults()
        problem_dir = os.path.join(results_dir, problem)
        
        if not os.path.isdir(problem_dir):
            print(f"Warning: Problem directory not found: {problem_dir}")
            all_results[problem] = problem_results
            continue
        
        if debug:
            print(f"\nDEBUG: Processing problem: {problem}")
            print(f"DEBUG: Problem dir: {problem_dir}")
        
        for noise_level in noise_levels:
            # Find noisy results directory
            noise_dirs = [
                os.path.join(problem_dir, 'abduction', 'noisy', f'noise_{noise_level}'),
                os.path.join(problem_dir, 'noisy', f'noise_{noise_level}'),
            ]
            
            noise_dir = None
            for nd in noise_dirs:
                if os.path.isdir(nd):
                    noise_dir = nd
                    break
            
            if noise_dir is None:
                if debug:
                    print(f"DEBUG: No noise dir found for {noise_level}, tried: {noise_dirs}")
                continue
            
            if debug:
                print(f"\nDEBUG: Noise level {noise_level}, noise_dir: {noise_dir}")
            
            for num_removed in num_axioms_removed:
                # Find combo directories for this num_removed
                n_dirs = [
                    os.path.join(noise_dir, f'{num_removed}_axiom(s)_removed'),
                    os.path.join(noise_dir, f'{num_removed}_axioms_removed'),
                    os.path.join(noise_dir, f'remove_{num_removed}'),
                ]
                
                n_dir = None
                for nd in n_dirs:
                    if os.path.isdir(nd):
                        n_dir = nd
                        break
                
                if n_dir is None:
                    if debug:
                        print(f"DEBUG: No n_dir found for {num_removed} axioms removed, tried: {n_dirs}")
                    continue
                
                # Find all combo directories
                combo_dirs = sorted(glob.glob(os.path.join(n_dir, 'combo_*')))
                
                if debug:
                    print(f"DEBUG: Found {len(combo_dirs)} combo dirs in {n_dir}")
                
                for combo_dir in combo_dirs:
                    # Extract combo identifier (e.g., "1" or "1_2" or "1_2_3")
                    combo_basename = os.path.basename(combo_dir)
                    # Extract everything after "combo_"
                    combo_id_match = re.search(r'combo_(.+)$', combo_basename)
                    combo_id = combo_id_match.group(1) if combo_id_match else "0"
                    
                    result = ComboResult(
                        num_removed=num_removed,
                        combo_index=0  # Not used anymore, we use combo_id for matching
                    )
                    
                    # Get coefficient error
                    result.coefficient_error = find_best_error_in_combo(combo_dir)
                    
                    # Get noisy component count from summary.txt in combo directory
                    if debug:
                        print(f"\nDEBUG: Combo {combo_id}, num_removed={num_removed}")
                        print(f"DEBUG: Noisy combo_dir: {combo_dir}")
                    result.noisy_num_components = find_component_count_in_combo(combo_dir, debug=debug)
                    
                    # Get noiseless component count from noiseless abduction
                    # Directory structure: results/<problem>/abduction/noiseless/<n>_axiom(s)_removed/combo_<id>/summary.txt
                    noiseless_combo_dirs = [
                        os.path.join(problem_dir, 'abduction', 'noiseless', f'{num_removed}_axiom(s)_removed', f'combo_{combo_id}'),
                        os.path.join(problem_dir, 'abduction', 'algebraic', f'{num_removed}_axiom(s)_removed', f'combo_{combo_id}'),
                        os.path.join(problem_dir, 'noiseless', f'{num_removed}_axiom(s)_removed', f'combo_{combo_id}'),
                    ]
                    
                    if debug:
                        print(f"DEBUG: Looking for noiseless in: {noiseless_combo_dirs}")
                    
                    for noiseless_combo_dir in noiseless_combo_dirs:
                        if os.path.isdir(noiseless_combo_dir):
                            if debug:
                                print(f"DEBUG: Found noiseless dir: {noiseless_combo_dir}")
                            result.noiseless_num_components = find_component_count_in_combo(noiseless_combo_dir, debug=debug)
                            if result.noiseless_num_components is not None:
                                break
                    
                    if debug:
                        print(f"DEBUG: noisy_components={result.noisy_num_components}, noiseless_components={result.noiseless_num_components}")
                        print(f"DEBUG: correct_components={result.correct_components}")
                    
                    # Determine if timed out (no error and directory exists = likely timeout)
                    result.timed_out = (result.coefficient_error is None and os.path.isdir(combo_dir))
                    
                    problem_results.results[noise_level][num_removed].append(result)
        
        all_results[problem] = problem_results
    
    return all_results


def compute_statistics(
    all_results: Dict[str, ProblemResults],
    noise_levels: List[str],
    num_axioms_removed: List[int]
) -> Dict:
    """Compute various statistics from results."""
    from math import comb
    
    stats = {
        'best_errors': {},  # problem -> noise_level -> best error
        'best_errors_filtered': {},  # same but only correct components
        'completion_rates': {},  # problem -> noise_level -> num_removed -> (completed, expected_total)
        'component_match_rates': {},  # problem -> noise_level -> num_removed -> (matched, expected_total)
        'num_axioms': {},  # problem -> inferred number of axioms
    }
    
    for problem, prob_results in all_results.items():
        stats['best_errors'][problem] = {}
        stats['best_errors_filtered'][problem] = {}
        stats['completion_rates'][problem] = {}
        stats['component_match_rates'][problem] = {}
        
        # Infer number of axioms from the 1-axiom removal case
        # The number of combos when removing 1 axiom = number of axioms
        num_axioms = None
        for noise_level in noise_levels:
            if 1 in prob_results.results[noise_level]:
                combos_1ax = prob_results.results[noise_level][1]
                if len(combos_1ax) > 0:
                    num_axioms = len(combos_1ax)
                    break
        
        # If we couldn't find it from results, try to infer from any available data
        if num_axioms is None:
            for noise_level in noise_levels:
                for num_rem in num_axioms_removed:
                    combos = prob_results.results[noise_level][num_rem]
                    if len(combos) > 0:
                        # C(n, k) = len(combos), solve for n
                        # For k=2: n*(n-1)/2 = len, so n ≈ sqrt(2*len)
                        # For k=3: n*(n-1)*(n-2)/6 = len
                        if num_rem == 1:
                            num_axioms = len(combos)
                            break
                        elif num_rem == 2:
                            # Solve n*(n-1)/2 = len for n
                            import math
                            approx_n = int(math.ceil((1 + math.sqrt(1 + 8 * len(combos))) / 2))
                            if comb(approx_n, 2) == len(combos):
                                num_axioms = approx_n
                                break
                        elif num_rem == 3:
                            # Try different values of n
                            for n in range(3, 20):
                                if comb(n, 3) == len(combos):
                                    num_axioms = n
                                    break
                if num_axioms is not None:
                    break
        
        stats['num_axioms'][problem] = num_axioms
        
        for noise_level in noise_levels:
            all_errors = []
            filtered_errors = []
            stats['completion_rates'][problem][noise_level] = {}
            stats['component_match_rates'][problem][noise_level] = {}
            
            for num_removed in num_axioms_removed:
                combos = prob_results.results[noise_level][num_removed]
                
                # Calculate expected total using combinatorics
                if num_axioms is not None and num_removed <= num_axioms:
                    expected_total = comb(num_axioms, num_removed)
                else:
                    # Fallback to actual count if we can't compute expected
                    expected_total = len(combos) if len(combos) > 0 else 0
                
                completed = sum(1 for c in combos if c.completed)
                stats['completion_rates'][problem][noise_level][num_removed] = (completed, expected_total)
                
                matched = sum(1 for c in combos if c.correct_components)
                stats['component_match_rates'][problem][noise_level][num_removed] = (matched, expected_total)
                
                for combo in combos:
                    if combo.coefficient_error is not None:
                        all_errors.append(combo.coefficient_error)
                        if combo.correct_components:
                            filtered_errors.append(combo.coefficient_error)
            
            stats['best_errors'][problem][noise_level] = min(all_errors) if all_errors else None
            stats['best_errors_filtered'][problem][noise_level] = min(filtered_errors) if filtered_errors else None
    
    return stats


def get_display_name(problem: str) -> str:
    """Get display name for a problem."""
    return PROBLEM_DISPLAY_NAMES.get(problem, problem.replace('_', ' ').title())


def plot_bar_graph(
    stats: Dict,
    problems: List[str],
    noise_levels: List[str],
    num_axioms_removed: List[int],
    filtered: bool = False,
    output_file: Optional[str] = None,
    title: str = "Coefficient Error vs Noise Level"
):
    """
    Create bar graph of coefficient errors with cleaner recovery rate visualization.
    
    Uses a two-panel layout:
    - Top panel: Bar graph of coefficient errors
    - Bottom panel: Recovery rate indicators as rectangular cells in a grid
    """
    error_key = 'best_errors_filtered' if filtered else 'best_errors'
    rate_key = 'component_match_rates' if filtered else 'completion_rates'
    
    n_problems = len(problems)
    n_noise_levels = len(noise_levels)
    n_axiom_levels = len(num_axioms_removed)
    
    if n_problems == 0:
        print("No problems to plot.")
        return
    
    # Figure setup - wider for many problems
    fig_width = max(14, 1.8 * n_problems)
    fig_height = 8
    
    # Create figure with GridSpec for better control
    fig = plt.figure(figsize=(fig_width, fig_height))
    gs = fig.add_gridspec(2, 1, height_ratios=[3, 1.2], hspace=0.15)
    
    ax_bars = fig.add_subplot(gs[0])
    ax_recovery = fig.add_subplot(gs[1], sharex=ax_bars)
    
    x = np.arange(n_problems)
    bar_width = 0.8 / n_noise_levels
    
    colors = [COLORS.get(nl, FALLBACK_COLORS[i % len(FALLBACK_COLORS)]) 
              for i, nl in enumerate(noise_levels)]
    
    # ===== TOP PANEL: Bar graph =====
    for i, noise_level in enumerate(noise_levels):
        errors = []
        for problem in problems:
            err = stats[error_key].get(problem, {}).get(noise_level)
            errors.append(err if err is not None else 0)
        
        mask = [stats[error_key].get(problem, {}).get(noise_level) is not None 
                for problem in problems]
        
        offset = (i - n_noise_levels / 2 + 0.5) * bar_width
        bars = ax_bars.bar(
            x + offset,
            errors,
            bar_width * 0.9,
            label=f'σ = {noise_level}',
            color=colors[i],
            edgecolor='white',
            linewidth=0.5,
            alpha=0.85
        )
        
        for j, (bar, present) in enumerate(zip(bars, mask)):
            if not present:
                bar.set_alpha(0.1)
                bar.set_hatch('///')
    
    # Configure top panel
    ax_bars.set_ylabel('Coefficient L2 Error', fontsize=12, fontweight='bold')
    ax_bars.set_title(title, fontsize=14, fontweight='bold', pad=15)
    
    # Auto log scale if needed
    all_errors = [e for p in stats[error_key].values() for e in p.values() if e is not None and e > 0]
    if all_errors:
        error_range = max(all_errors) / min(all_errors) if min(all_errors) > 0 else 1
        if error_range > 100:
            ax_bars.set_yscale('log')
            ax_bars.set_ylabel('Coefficient L2 Error (log scale)', fontsize=12, fontweight='bold')
    
    # Legend for noise levels - positioned at upper left to avoid covering bars
    ax_bars.legend(loc='upper left', framealpha=0.95, fontsize=11, title='Noise Level', 
                   title_fontsize=11)
    
    ax_bars.yaxis.grid(True, linestyle='--', alpha=0.3)
    ax_bars.set_axisbelow(True)
    
    for spine in ['top', 'right']:
        ax_bars.spines[spine].set_visible(False)
    for spine in ['bottom', 'left']:
        ax_bars.spines[spine].set_color('#CCCCCC')
    
    # Hide x-axis labels on top panel
    ax_bars.tick_params(axis='x', which='both', bottom=False, labelbottom=False)
    
    # ===== BOTTOM PANEL: Recovery rate table =====
    # Create a table-like visualization with rectangular cells
    
    ax_recovery.set_xlim(-0.5, n_problems - 0.5)
    ax_recovery.set_ylim(-0.5, n_axiom_levels - 0.5)
    
    # Cell dimensions
    cell_width = 0.8 / n_noise_levels
    cell_height = 0.7
    
    # Draw cells for each problem/noise/axiom combination
    for prob_idx, problem in enumerate(problems):
        # Get expected totals for this problem
        num_axioms = stats.get('num_axioms', {}).get(problem)
        
        for noise_idx, noise_level in enumerate(noise_levels):
            x_center = prob_idx + (noise_idx - n_noise_levels / 2 + 0.5) * cell_width
            
            for ax_idx, num_rem in enumerate(num_axioms_removed):
                rate_data = stats[rate_key].get(problem, {}).get(noise_level, {}).get(num_rem)
                
                y_center = ax_idx
                
                # Calculate expected total from combinatorics if not in rate_data
                if rate_data:
                    completed, expected_total = rate_data
                elif num_axioms is not None and num_rem <= num_axioms:
                    from math import comb
                    completed = 0
                    expected_total = comb(num_axioms, num_rem)
                else:
                    completed = 0
                    expected_total = 0
                
                if expected_total > 0:
                    fill_ratio = completed / expected_total
                    
                    # Draw background rectangle (gray)
                    rect_bg = plt.Rectangle(
                        (x_center - cell_width * 0.45, y_center - cell_height / 2),
                        cell_width * 0.9,
                        cell_height,
                        facecolor='#E8E8E8',
                        edgecolor='#CCCCCC',
                        linewidth=0.5,
                        zorder=1
                    )
                    ax_recovery.add_patch(rect_bg)
                    
                    # Draw filled portion (colored)
                    if fill_ratio > 0:
                        rect_fill = plt.Rectangle(
                            (x_center - cell_width * 0.45, y_center - cell_height / 2),
                            cell_width * 0.9 * fill_ratio,
                            cell_height,
                            facecolor=colors[noise_idx],
                            edgecolor='none',
                            alpha=0.85,
                            zorder=2
                        )
                        ax_recovery.add_patch(rect_fill)
                    
                    # Add text showing fraction
                    text_color = 'white' if fill_ratio > 0.5 else '#333333'
                    ax_recovery.text(
                        x_center, y_center,
                        f'{completed}/{expected_total}',
                        ha='center', va='center',
                        fontsize=8, fontweight='bold',
                        color=text_color,
                        zorder=3
                    )
                else:
                    # No expected data - draw empty cell with dash
                    rect_empty = plt.Rectangle(
                        (x_center - cell_width * 0.45, y_center - cell_height / 2),
                        cell_width * 0.9,
                        cell_height,
                        facecolor='#F5F5F5',
                        edgecolor='#DDDDDD',
                        linewidth=0.5,
                        zorder=1
                    )
                    ax_recovery.add_patch(rect_empty)
                    ax_recovery.text(
                        x_center, y_center, '-',
                        ha='center', va='center',
                        fontsize=8, color='#AAAAAA',
                        zorder=3
                    )
    
    # Configure bottom panel
    ax_recovery.set_yticks(range(n_axiom_levels))
    ax_recovery.set_yticklabels([f'{n} ax.' for n in num_axioms_removed], fontsize=10, fontweight='bold')
    ax_recovery.set_ylabel('Axioms\nRemoved', fontsize=10, fontweight='bold', rotation=0, 
                           ha='right', va='center', labelpad=15)
    
    ax_recovery.set_xticks(x)
    display_names = [get_display_name(p) for p in problems]
    ax_recovery.set_xticklabels(display_names, rotation=45, ha='right', fontsize=12, fontweight='bold')
    
    ax_recovery.set_facecolor('white')
    ax_recovery.tick_params(axis='both', which='both', length=0)
    
    for spine in ax_recovery.spines.values():
        spine.set_visible(False)
    
    # Add separator lines between axiom rows
    for i in range(1, n_axiom_levels):
        ax_recovery.axhline(y=i - 0.5, color='#EEEEEE', linewidth=1, zorder=0)
    
    # Adjust layout manually to avoid tight_layout issues
    fig.subplots_adjust(left=0.08, right=0.95, top=0.92, bottom=0.15, hspace=0.15)
    
    if output_file:
        plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Plot saved to: {output_file}")
    else:
        plt.show()
    
    plt.close()


def plot_bar_graph_compact(
    stats: Dict,
    problems: List[str],
    noise_levels: List[str],
    num_axioms_removed: List[int],
    filtered: bool = False,
    output_file: Optional[str] = None,
    title: str = "Coefficient Error vs Noise Level"
):
    """
    Create a more compact bar graph without the recovery indicator panel.
    """
    error_key = 'best_errors_filtered' if filtered else 'best_errors'
    
    n_problems = len(problems)
    n_noise_levels = len(noise_levels)
    
    if n_problems == 0:
        print("No problems to plot.")
        return
    
    fig_width = max(14, 1.6 * n_problems)
    fig_height = 5
    fig, ax = plt.subplots(figsize=(fig_width, fig_height))
    
    x = np.arange(n_problems)
    bar_width = 0.8 / n_noise_levels
    
    colors = [COLORS.get(nl, FALLBACK_COLORS[i % len(FALLBACK_COLORS)]) 
              for i, nl in enumerate(noise_levels)]
    
    # Draw bars
    for i, noise_level in enumerate(noise_levels):
        errors = []
        for problem in problems:
            err = stats[error_key].get(problem, {}).get(noise_level)
            errors.append(err if err is not None else 0)
        
        mask = [stats[error_key].get(problem, {}).get(noise_level) is not None 
                for problem in problems]
        
        offset = (i - n_noise_levels / 2 + 0.5) * bar_width
        bars = ax.bar(
            x + offset,
            errors,
            bar_width * 0.9,
            label=f'σ = {noise_level}',
            color=colors[i],
            edgecolor='white',
            linewidth=0.5,
            alpha=0.85
        )
        
        for j, (bar, present) in enumerate(zip(bars, mask)):
            if not present:
                bar.set_alpha(0.1)
                bar.set_hatch('///')
    
    # Configure axes
    ax.set_ylabel('Coefficient L2 Error', fontsize=12, fontweight='bold')
    ax.set_title(title, fontsize=14, fontweight='bold', pad=15)
    
    ax.set_xticks(x)
    display_names = [get_display_name(p) for p in problems]
    ax.set_xticklabels(display_names, rotation=45, ha='right', fontsize=12, fontweight='bold')
    
    # Auto log scale if needed
    all_errors = [e for p in stats[error_key].values() for e in p.values() if e is not None and e > 0]
    if all_errors:
        error_range = max(all_errors) / min(all_errors) if min(all_errors) > 0 else 1
        if error_range > 100:
            ax.set_yscale('log')
            ax.set_ylabel('Coefficient L2 Error (log scale)', fontsize=12, fontweight='bold')
    
    # Create custom legend
    legend_elements = [
        mpatches.Patch(facecolor=colors[i], edgecolor='white', label=f'σ = {nl}', alpha=0.85)
        for i, nl in enumerate(noise_levels)
    ]
    
    ax.legend(handles=legend_elements, loc='upper left', framealpha=0.95, fontsize=11, 
              title='Noise Level', title_fontsize=11)
    
    ax.yaxis.grid(True, linestyle='--', alpha=0.3)
    ax.set_axisbelow(True)
    
    for spine in ['top', 'right']:
        ax.spines[spine].set_visible(False)
    for spine in ['bottom', 'left']:
        ax.spines[spine].set_color('#CCCCCC')
    
    plt.tight_layout()
    
    if output_file:
        plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Plot saved to: {output_file}")
    else:
        plt.show()
    
    plt.close()


def plot_component_recovery_heatmap(
    stats: Dict,
    problems: List[str],
    noise_levels: List[str],
    num_axioms_removed: List[int],
    output_file: Optional[str] = None
):
    """
    Create heatmap showing component recovery rates.
    Three subplots (one per num_removed), problems on y-axis, noise levels on x-axis.
    """
    n_removed_count = len(num_axioms_removed)
    n_problems = len(problems)
    n_noise = len(noise_levels)
    
    # Create figure with subplots
    fig, axes = plt.subplots(1, n_removed_count, figsize=(4 * n_removed_count + 1, max(6, 0.5 * n_problems)))
    
    if n_removed_count == 1:
        axes = [axes]
    
    # Custom colormap: white -> light blue -> deep blue
    cmap = LinearSegmentedColormap.from_list('recovery', ['#FFFFFF', '#B8D4E8', '#2E86AB'])
    
    for idx, num_removed in enumerate(num_axioms_removed):
        ax = axes[idx]
        
        # Build data matrix
        data = np.zeros((n_problems, n_noise))
        annotations = [['' for _ in range(n_noise)] for _ in range(n_problems)]
        
        for i, problem in enumerate(problems):
            for j, noise_level in enumerate(noise_levels):
                rate_data = stats['component_match_rates'].get(problem, {}).get(noise_level, {}).get(num_removed)
                if rate_data:
                    matched, total = rate_data
                    if total > 0:
                        data[i, j] = matched / total * 100
                        annotations[i][j] = f'{matched}/{total}'
                    else:
                        data[i, j] = np.nan
                        annotations[i][j] = '-'
                else:
                    data[i, j] = np.nan
                    annotations[i][j] = '-'
        
        # Plot heatmap
        im = ax.imshow(data, cmap=cmap, aspect='auto', vmin=0, vmax=100)
        
        # Add text annotations
        for i in range(n_problems):
            for j in range(n_noise):
                text = annotations[i][j]
                # Choose text color based on background
                val = data[i, j]
                text_color = 'white' if not np.isnan(val) and val > 60 else '#333333'
                ax.text(j, i, text, ha='center', va='center', fontsize=9, color=text_color, fontweight='bold')
        
        ax.set_xticks(np.arange(n_noise))
        ax.set_xticklabels(noise_levels, fontsize=10)
        ax.set_yticks(np.arange(n_problems))
        
        # Use display names with bold font
        display_names = [get_display_name(p) for p in problems]
        ax.set_yticklabels(display_names if idx == 0 else [], fontsize=11, fontweight='bold')
        
        ax.set_xlabel('Noise Level', fontsize=11, fontweight='bold')
        if idx == 0:
            ax.set_ylabel('Problem', fontsize=11, fontweight='bold')
        
        ax.set_title(f'{num_removed} Axiom{"s" if num_removed > 1 else ""} Removed', 
                    fontsize=12, fontweight='bold', pad=10)
        
        # Add grid
        ax.set_xticks(np.arange(n_noise + 1) - 0.5, minor=True)
        ax.set_yticks(np.arange(n_problems + 1) - 0.5, minor=True)
        ax.grid(which='minor', color='white', linewidth=2)
        ax.tick_params(which='minor', size=0)
    
    # Add colorbar
    cbar = fig.colorbar(im, ax=axes, shrink=0.6, aspect=30, pad=0.02)
    cbar.set_label('Component Match Rate (%)', fontsize=11, fontweight='bold')
    
    fig.suptitle('Correct Component Recovery Rate by Problem, Noise Level, and Axioms Removed',
                fontsize=13, fontweight='bold', y=1.02)
    
    # Use subplots_adjust instead of tight_layout to avoid warnings with colorbar
    fig.subplots_adjust(left=0.12, right=0.88, top=0.90, bottom=0.08, wspace=0.1)
    
    if output_file:
        plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Heatmap saved to: {output_file}")
    else:
        plt.show()
    
    plt.close()


def print_summary(
    stats: Dict,
    problems: List[str],
    noise_levels: List[str],
    num_axioms_removed: List[int]
):
    """Print summary tables to stdout."""
    print("\n" + "=" * 90)
    print("RECOVERY SUMMARY")
    print("=" * 90)
    
    for problem in problems:
        num_axioms = stats.get('num_axioms', {}).get(problem)
        axiom_info = f" (n={num_axioms} axioms)" if num_axioms else ""
        print(f"\n{problem}{axiom_info}:")
        print("-" * 50)
        
        for noise_level in noise_levels:
            err = stats['best_errors'].get(problem, {}).get(noise_level)
            err_filt = stats['best_errors_filtered'].get(problem, {}).get(noise_level)
            err_str = f"{err:.2e}" if err is not None else "N/A"
            err_filt_str = f"{err_filt:.2e}" if err_filt is not None else "N/A"
            
            completion_parts = []
            component_parts = []
            for num_rem in num_axioms_removed:
                comp_data = stats['completion_rates'].get(problem, {}).get(noise_level, {}).get(num_rem)
                match_data = stats['component_match_rates'].get(problem, {}).get(noise_level, {}).get(num_rem)
                
                if comp_data:
                    completion_parts.append(f"{num_rem}ax:{comp_data[0]}/{comp_data[1]}")
                if match_data:
                    component_parts.append(f"{num_rem}ax:{match_data[0]}/{match_data[1]}")
            
            completion_str = ", ".join(completion_parts) if completion_parts else "no data"
            component_str = ", ".join(component_parts) if component_parts else "no data"
            
            print(f"  {noise_level}:")
            print(f"    Best error (all):      {err_str}")
            print(f"    Best error (filtered): {err_filt_str}")
            print(f"    Completed: [{completion_str}]")
            print(f"    Correct components: [{component_str}]")


def main():
    parser = argparse.ArgumentParser(
        description='Plot coefficient error vs noise level with completion and component rates'
    )
    parser.add_argument(
        '--problems', '-p',
        nargs='+',
        default=DEFAULT_PROBLEMS,
        help=f'List of problem names (default: {DEFAULT_PROBLEMS})'
    )
    parser.add_argument(
        '--results-dir', '-r',
        type=str,
        default='results',
        help='Path to results directory (default: results)'
    )
    parser.add_argument(
        '--noise-levels', '-n',
        nargs='+',
        default=['1e-2', '1e-5', '1e-8'],
        help='Noise levels to plot (default: 1e-2 1e-5 1e-8)'
    )
    parser.add_argument(
        '--num-removed', '-k',
        nargs='+',
        type=int,
        default=[1, 2, 3],
        help='Numbers of axioms removed to track (default: 1 2 3)'
    )
    parser.add_argument(
        '--output-dir', '-o',
        type=str,
        default='.',
        help='Output directory for plots (default: current directory)'
    )
    parser.add_argument(
        '--prefix',
        type=str,
        default='noisy_results',
        help='Prefix for output files (default: noisy_results)'
    )
    parser.add_argument(
        '--debug', '-d',
        action='store_true',
        help='Enable debug output to diagnose component counting issues'
    )
    parser.add_argument(
        '--debug-log',
        type=str,
        default=None,
        help='Save debug output to this file (implies --debug)'
    )
    parser.add_argument(
        '--compact',
        action='store_true',
        help='Use compact bar graph style (no recovery indicator panel)'
    )
    
    args = parser.parse_args()
    
    # Handle debug log file
    debug_file = None
    if args.debug_log:
        args.debug = True
        debug_file = open(args.debug_log, 'w')
        # Redirect print to both stdout and file
        import sys
        class Tee:
            def __init__(self, *files):
                self.files = files
            def write(self, obj):
                for f in self.files:
                    f.write(obj)
                    f.flush()
            def flush(self):
                for f in self.files:
                    f.flush()
        sys.stdout = Tee(sys.stdout, debug_file)
    
    print(f"Collecting results from: {args.results_dir}")
    print(f"Problems: {', '.join(args.problems)}")
    print(f"Noise levels: {', '.join(args.noise_levels)}")
    print(f"Axioms removed: {args.num_removed}")
    
    # Collect all results
    all_results = collect_all_results(
        args.results_dir,
        args.problems,
        args.noise_levels,
        args.num_removed,
        debug=args.debug
    )
    
    # Compute statistics
    stats = compute_statistics(all_results, args.noise_levels, args.num_removed)
    
    # Print summary
    print_summary(stats, args.problems, args.noise_levels, args.num_removed)
    
    # Check if we have data
    has_data = any(
        err is not None 
        for p in stats['best_errors'].values() 
        for err in p.values()
    )
    
    if not has_data:
        print("\nNo data found to plot.")
        return
    
    os.makedirs(args.output_dir, exist_ok=True)
    
    # Choose bar graph style
    bar_graph_func = plot_bar_graph_compact if args.compact else plot_bar_graph
    
    # Plot 1: Original bar graph (all completed)
    bar_graph_func(
        stats,
        args.problems,
        args.noise_levels,
        args.num_removed,
        filtered=False,
        output_file=os.path.join(args.output_dir, f'{args.prefix}_all.png'),
        title='Coefficient Recovery Error vs Noise Level'
    )
    
    # Plot 2: Filtered bar graph (correct components only)
    bar_graph_func(
        stats,
        args.problems,
        args.noise_levels,
        args.num_removed,
        filtered=True,
        output_file=os.path.join(args.output_dir, f'{args.prefix}_filtered.png'),
        title='Coefficient Recovery Error vs Noise Level (Correct Components Only)'
    )
    
    # Plot 3: Component recovery heatmap
    plot_component_recovery_heatmap(
        stats,
        args.problems,
        args.noise_levels,
        args.num_removed,
        output_file=os.path.join(args.output_dir, f'{args.prefix}_component_heatmap.png')
    )
    
    print(f"\nAll plots saved to: {args.output_dir}/")
    
    # Cleanup debug log file
    if args.debug_log and debug_file:
        debug_file.close()
        print(f"Debug log saved to: {args.debug_log}")


if __name__ == '__main__':
    main()
