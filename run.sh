#!/bin/bash
#
# AI-Noether: Run script
# 
# Usage:
#   ./run.sh [config_file]
#
# If no config file is specified, uses config.yaml in the current directory.
#

set -e

# Activate conda environment if available (adjust path if needed)
if [ -f ~/miniconda3/etc/profile.d/conda.sh ]; then
    source ~/miniconda3/etc/profile.d/conda.sh
    conda activate ai_noether_env 2>/dev/null || true
elif [ -f ~/anaconda3/etc/profile.d/conda.sh ]; then
    source ~/anaconda3/etc/profile.d/conda.sh
    conda activate ai_noether_env 2>/dev/null || true
fi

# Get the directory where this script is located
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Default config file
CONFIG_FILE="${1:-config.yaml}"

# Check if config file exists
if [[ ! -f "$CONFIG_FILE" ]]; then
    echo "ERROR: Config file not found: $CONFIG_FILE"
    echo ""
    echo "Usage: $0 [config_file]"
    echo ""
    echo "If no config file is specified, 'config.yaml' is used."
    echo ""
    echo "To get started:"
    echo "  1. Copy the template:  cp ${SCRIPT_DIR}/config_template.yaml config.yaml"
    echo "  2. Edit config.yaml with your paths (especially paths.macaulay2)"
    echo "  3. Run again:          ./run.sh"
    exit 1
fi

echo "AI-Noether: Abductive Inference for Scientific Discovery"
echo "========================================================="
echo ""
echo "Config file: $CONFIG_FILE"
echo ""

# Set PYTHONPATH to include the script directory so 'src' module can be found
export PYTHONPATH="${SCRIPT_DIR}:${PYTHONPATH}"

# Run the main script
python -m src.main --config "$CONFIG_FILE"

echo ""
echo "Done!"
