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

## **Installing Dependencies and Building Submodules**

To install the dependencies and build the submodules, run:
```bash
chmod +x setup.sh
./setup.sh
```

---

## **Usage**

To run the tool:

```bash
python ./src/run.py --file <path_to_formula> --method <automata|symbolic>
```

For example:

```bash
python ./src/run.py --file ./input/LIA1-10.ltlmt --method symbolic
```