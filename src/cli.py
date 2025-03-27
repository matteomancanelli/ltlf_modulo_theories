import subprocess

def launch(command, cwd=None, capture_output=False):
    """Launch a command."""

    if capture_output:
        # Run command and capture output
        result = subprocess.run(command, shell=True, cwd=cwd, text=True, capture_output=True)
        return result.stdout.strip()
    else:
        # Run command without capturing output
        subprocess.run(command, shell=True, cwd=cwd)
        return None