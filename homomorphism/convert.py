import json
from pathlib import Path

from sacred.observers import MongoObserver

observer_dir = Path('path/to/file/storage/observer')


# Optionally iterate over runs
for run_dir in observer_dir.glob('*'):
    # Create a mongo observer to report to mongodb
    mongo_observer = MongoObserver(...)

    with (run_dir / 'config.json').open() as f:
        config = json.load(f)

    with (run_dir / 'cout.txt').open() as f:
        cout = json.load(f)

    with (run_dir / 'metrics.json').open() as f:
        metrics = json.load(f)

    with (run_dir / 'run.json').open() as f:
        run = json.load(f)

    run.update(
        config=config,
        captured_out=cout,
        metrics=metrics,    # Not sure if this results in the correct format

    )

    mongo_observer.run_entry.update(
        {
            "_id": run_dir.stem,
            "experiment": run['experiment'],
            "format": mongo_observer.VERSION,
            "command": run['command'],
            "host": run['host'],
            "start_time": run['start_time'],
            "stop_time": run['stop_time'],
            "config": config,
            "meta": run['meta'],
            "status": run['status'],
            "resources": run['resources'],
            "artifacts": run['artifacts'],
            "captured_out": cout,
            "info": run.get('info', None),
            "heartbeat": run['heartbeat'],
            "fail_trace": run.get('fail_trace', None),
            "result": run.get('result', None),
        }
    )

    # Save 
    mongo_observer.insert()
    
