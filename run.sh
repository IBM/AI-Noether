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

source ~/miniconda3/etc/profile.d/conda.sh
conda activate ai_noether_env

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
    echo "Copy config_template.yaml to config.yaml and customize it:"
    echo "  cp ${SCRIPT_DIR}/config_template.yaml config.yaml"
    exit 1
fi

echo "AI-Noether: Abductive Inference for Scientific Discovery"
echo "========================================================="
echo ""
echo "Config file: $CONFIG_FILE"
echo ""

# Run the main script
python -m src.main --config "$CONFIG_FILE"

echo ""
echo "Done!"
