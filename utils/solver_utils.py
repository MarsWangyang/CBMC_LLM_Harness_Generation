import os
import logging
from subprocess import run
import sys

_global_sat_solver = None 
SOLVERS_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "solvers")

logger = logging.getLogger("solver_utils")


def setup_sat_solver(solver = None):
    global _global_sat_solver

    if _global_sat_solver is not None:
        logger.debug(f"Using {_global_sat_solver} as SAT solver")
        return _global_sat_solver

    if solver == "minisat":
        logger.info("Set minisat as SAT solver")
        _global_sat_solver = "minisat"
        return _global_sat_solver

    os.makedirs(SOLVERS_DIR, exist_ok=True)  # Make sure solvers directory exists

    if solver == "kissat":
        path = os.path.join(SOLVERS_DIR, "kissat")

        if os.path.exists(path):
            logger.info("Kissat already installed. Skipping setup.")
            _global_sat_solver = "kissat"
            return _global_sat_solver

        if not os.path.exists(path):
            logger.info("Cloning and building Kissat...")
            run("git clone https://github.com/arminbiere/kissat {}".format(path), shell=True, check=True)
            run("./configure", shell=True, cwd=path, check=True)
            run("make -j$(nproc)", shell=True, cwd=path, check=True)
        else:
            logger.info("Kissat already installed.")
        _global_sat_solver = "kissat"
        return _global_sat_solver

    if solver == "cadical":
        path = os.path.join(SOLVERS_DIR, "cadical")

        if os.path.exists(path):
            logger.info("CaDiCaL already installed. Skipping setup.")
            _global_sat_solver = "cadical"
            return _global_sat_solver

        if not os.path.exists(path):
            logger.info("Cloning and building CaDiCaL...")
            run("git clone https://github.com/arminbiere/cadical {}".format(path), shell=True, check=True)
            run("./configure", shell=True, cwd=path, check=True)
            run("make -j$(nproc)", shell=True, cwd=path, check=True)
        else:
            logger.info("CaDiCaL already installed.")
        _global_sat_solver = "cadical"
        return _global_sat_solver

    logger.error(f"Invalid SAT solver: {solver}")
    sys.exit(1)
    
    