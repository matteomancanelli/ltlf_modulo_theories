import os
import ctypes

project_root = os.path.join(os.getcwd(), "submodules", "black")
build_dir = os.path.join(project_root, "build")
setup_path = os.path.join(build_dir, "python", "setup.py")

lib_include = os.path.join(project_root, "src", "lib", "include")
python_include = os.path.join(project_root, "python", "include")
py_src = os.path.join(project_root, "python", "src")
lib_dir = os.path.join(build_dir, "src", "lib")

# This may need to be adjusted depending on where pybind11 is installed
pybind11_include = "/usr/include/pybind11"
python_include_dir = "/usr/include/python3.11"  # or appropriate version

os.makedirs(os.path.dirname(setup_path), exist_ok=True)

with open(setup_path, "w") as f:
    f.write(f"""
from setuptools import setup, Extension

black_module = Extension(
    'black_sat',
    sources=['{py_src}/bindings.cpp', '{py_src}/hierarchy.cpp'],
    include_dirs=['{lib_include}', '{python_include}', '{pybind11_include}', '{python_include_dir}'],
    library_dirs=['{lib_dir}'],
    libraries=['black'],
    extra_compile_args=['-std=c++20']
)

setup(
    name='black_sat',
    version='0.1.0',
    description='Python bindings for BLACK',
    ext_modules=[black_module]
)
""")

print("✅ setup.py written")


# Define paths
default_path = "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
black_lib_path = os.path.join(build_dir, "src", "lib")

# Set environment variables for the current process
os.environ["PATH"] = default_path  # You can append to this if needed
os.environ["LD_LIBRARY_PATH"] = f"/usr/local/lib:/usr/lib:{black_lib_path}"

# Load the shared library so Python bindings can find it
try:
    ctypes.CDLL(os.path.join(black_lib_path, "libblack.so"))
    print("✅ Environment set and libblack.so loaded.")
except OSError as e:
    print(f"❌ Failed to load libblack.so: {e}")