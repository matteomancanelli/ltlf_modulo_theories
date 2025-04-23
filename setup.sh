#!/bin/bash

set -e  # Exit on any error

echo "🔧 Updating and installing dependencies..."
sudo apt-get update
sudo apt-get install -y \
    build-essential flex bison \
    libz3-dev libcryptominisat5-dev libz-dev libgmp-dev \
    libfmt-dev libtsl-hopscotch-map-dev nlohmann-json3-dev \
    pybind11-dev

# Some distros split z3 out, make sure it's included
sudo apt install -y z3

# Python packages
echo "🐍 Installing Python dependencies..."
pip install --upgrade pip
pip install \
    spot --no-binary spot \
    lark-parser==0.9.0 \
    click==7.1.2 \
    hoa-utils==0.1.0 \
    pybind11==2.11.1

# Pull in submodules
echo "📦 Initializing git submodules..."
git submodule update --init --recursive

# Build BLACK with Python bindings
echo "⚙️ Building BLACK..."
cd submodules/black
rm -rf build && mkdir build && cd build
cmake -DBLACK_ENABLE_PYTHON_BINDINGS=ON ..
make -j$(nproc)

cd ../../../

# Patch and load Python bindings
echo "🔧 Generating Python setup.py and loading libblack..."
python script.py

# Build and install the Python binding
echo "📦 Building and installing Python binding..."
cd submodules/black/build/python
python setup.py build
python setup.py install

# Set up runtime linker config
BLACK_LIB_PATH="$(pwd)/../src/lib"
echo "🔒 Making libblack.so visible to the dynamic linker..."
echo "$BLACK_LIB_PATH" | sudo tee /etc/ld.so.conf.d/black.conf
sudo ldconfig

echo "✅ Setup complete!"
