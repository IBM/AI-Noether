#!/bin/bash
# Run noise results plotting for AI-Noether

# Activate conda environment
source ~/miniconda3/etc/profile.d/conda.sh
conda activate ai_noether_env

# Run plotting script with default problems
python plot_noise_results.py \
    --results-dir results \
    --output-dir figures \
    --prefix noisy_experiment \
    --problems hagen kepler time_dilation escape_velocity light decay simple_harmonic_oscillator photoHall relativistic_laws hall inelastic_relativistic_collision compton\
    --compact

# Optionally run compact version (no recovery panel)
# python plot_noise_results.py \
#     --results-dir results \
#     --output-dir figures \
#     --prefix noisy_experiment_compact \
#     --compact
