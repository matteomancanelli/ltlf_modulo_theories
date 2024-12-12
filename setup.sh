#!/bin/bash

set -e  # Exit on any error

# Constants
BUILD_DIR="submodules/black/build"
LIB_PATH="$BUILD_DIR/src/lib"
PYTHON_PACKAGE="black_sat"
REQUIREMENTS_FILE="requirements.txt"

echo "Starting setup..."

# Step 0: Check for required tools
echo "Checking dependencies..."
for tool in cmake make python pip; do
  command -v $tool >/dev/null 2>&1 || { echo >&2 "$tool is required but not installed. Aborting."; exit 1; }
done

# Step 1: Install dependencies
if [ -f "$REQUIREMENTS_FILE" ]; then
  echo "Installing dependencies..."
  pip install -r "$REQUIREMENTS_FILE"
fi

# Step 2: Build Black
echo "Building Black..."
if [ -d "$BUILD_DIR" ]; then
  echo "Build directory exists. Removing..."
  rm -rf "$BUILD_DIR"
fi
mkdir -p "$BUILD_DIR"
cd submodules/black
mkdir -p build
cd build
cmake -DBLACK_ENABLE_PYTHON_BINDINGS=ON ..
make

# Step 3: Install Black Python Bindings
echo "Installing Black Python bindings..."
cd python
python setup.py build
python setup.py install

# Step 4: Configure LD_LIBRARY_PATH
echo "Configuring library paths..."
export LD_LIBRARY_PATH=$LIB_PATH:$LD_LIBRARY_PATH
if ! grep -q "export LD_LIBRARY_PATH=$LIB_PATH" ~/.bashrc; then
  echo "export LD_LIBRARY_PATH=$LIB_PATH:\$LD_LIBRARY_PATH" >> ~/.bashrc
fi

# Step 5: Verify Installation
echo "Verifying installation..."
if python -c "import $PYTHON_PACKAGE" &> /dev/null; then
  echo "Black Python bindings installed successfully!"
else
  echo "Error: Black Python bindings could not be imported" >&2
  exit 1
fi

source ~/.bashrc
echo "Setup completed successfully!"
