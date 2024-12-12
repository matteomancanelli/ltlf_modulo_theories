# **LTLf Modulo Theories**

## **Overview**
A tool for processing Linear Temporal Logic Modulo Theories (LTLMT). This repository builds upon the work of Marco Faella and Gennaro Parlato, whose original implementation can be found at [this repository](https://bitbucket.org/mfaella/ltlf-modulo-theories/src/master/).

Formula parsing in this project is powered by [BLACK](https://github.com/black-sat/black), an advanced satisfiability checker for temporal logics.

---

## **Cloning the Repository**

To clone this repository with all its submodules:
```bash
git clone --recurse-submodules https://github.com/mancanelli/ltlf_modulo_theories
cd ltlf_modulo_theories
git submodule update --init --recursive
```

---

## **Dependencies**

### **Z3 Solver**
LTLMT requires the Z3 solver. To install Z3:
```bash
sudo apt update
sudo apt install z3
```

### **SPOT Library**
The project also relies on the [SPOT library](https://spot.lre.epita.fr/) for automata-based operations. To install SPOT, follow the detailed instructions provided on their [installation page](https://spot.lre.epita.fr/install.html).

---

## **Building Submodules**

Before running the project, you must build and configure its submodules.

1. **Install Required Python Packages**  
   Ensure `pybind11` and `hoa-utils` are installed as part of the setup process.

2. **Build the `black` Submodule**  
   The `black` logic engine submodule is built automatically through the setup script.

To initialize and build the submodules, run:
```bash
chmod +x setup.sh
./setup.sh
```

---

## **Running LTLMT**

To run an example, execute:
```bash
./run.sh LIA1.ltlmt 10
```
Here:
- `LIA1.ltlmt` is the input formula file.
- `10` is the parameter `N` passed to the script.