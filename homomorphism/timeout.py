from concurrent.futures import ThreadPoolExecutor, TimeoutError
from time import sleep
from sacred.utils import TimeoutInterrupt

# task is the long running task -- say the experiment
def task():
    sleep(5)
    return "Task done"


with ThreadPoolExecutor(2) as excecutor:
    future = excecutor.submit(task)

    try:
        print(future.result(timeout=0.1))
    except TimeoutError:
        raise TimeoutInterrupt()

    
