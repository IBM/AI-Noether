"""
AI-Noether: Logging utilities
"""

import logging
import sys
from typing import Optional


_logger: Optional[logging.Logger] = None


def setup_logger(log_level: str = "INFO", verbose: bool = False, log_file: Optional[str] = None) -> logging.Logger:
    """
    Setup and configure the logger.
    
    Args:
        log_level: Logging level (DEBUG, INFO, WARNING, ERROR)
        verbose: If True, also print to stdout
        log_file: Optional file path to write logs to
    
    Returns:
        Configured logger instance
    """
    global _logger
    
    _logger = logging.getLogger("ai_noether")
    _logger.setLevel(getattr(logging, log_level.upper(), logging.INFO))
    _logger.handlers = []  # Clear existing handlers
    
    # Create formatter
    formatter = logging.Formatter(
        '%(asctime)s | %(levelname)-8s | %(message)s',
        datefmt='%Y-%m-%d %H:%M:%S'
    )
    
    # File handler if specified
    if log_file:
        file_handler = logging.FileHandler(log_file)
        file_handler.setLevel(logging.DEBUG)  # Log everything to file
        file_handler.setFormatter(formatter)
        _logger.addHandler(file_handler)
    
    # Console handler if verbose
    if verbose:
        console_handler = logging.StreamHandler(sys.stdout)
        console_handler.setLevel(getattr(logging, log_level.upper(), logging.INFO))
        console_handler.setFormatter(formatter)
        _logger.addHandler(console_handler)
    
    # Always add a null handler to prevent "No handler found" warnings
    if not _logger.handlers:
        _logger.addHandler(logging.NullHandler())
    
    return _logger


def get_logger() -> logging.Logger:
    """Get the global logger instance."""
    global _logger
    if _logger is None:
        _logger = setup_logger()
    return _logger


def log_subprocess_result(cmd: str, returncode: int, stdout: str, stderr: str, context: str = ""):
    """Log the result of a subprocess call."""
    logger = get_logger()
    
    if context:
        logger.debug(f"[{context}] Command: {cmd}")
    else:
        logger.debug(f"Command: {cmd}")
    
    logger.debug(f"Return code: {returncode}")
    
    if stdout and stdout.strip():
        for line in stdout.strip().split('\n')[:50]:  # Limit output
            logger.debug(f"STDOUT: {line}")
        if len(stdout.strip().split('\n')) > 50:
            logger.debug("STDOUT: ... (truncated)")
    
    if stderr and stderr.strip():
        for line in stderr.strip().split('\n')[:50]:
            if returncode != 0:
                logger.warning(f"STDERR: {line}")
            else:
                logger.debug(f"STDERR: {line}")
        if len(stderr.strip().split('\n')) > 50:
            logger.debug("STDERR: ... (truncated)")
    
    if returncode != 0:
        logger.error(f"Command failed with return code {returncode}")
