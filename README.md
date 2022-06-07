Coq Serapy - Python Bindings for Coq Serapi
==================

This code was originally developed as part of the
[Proverbot9001](https://github.com/UCSD-PL/proverbot9001) project. If
you use this library as part of published research, some sort of
acknowledgement would be nice, but is not required.

```
@inproceedings{proverbot2020,
  author    = {Sanchez-Stern, Alex and Alhessi, Yousef and Saul, Lawrence and Lerner, Sorin},
  title     = {Generating Correctness Proofs with Neural Networks},
  booktitle = {Machine Learning in Programming Languages},
  month     = {June},
  year      = {2020},
  publisher = {ACM SIGPLAN},
}
```

Dependencies
------------

To use this project, you need:

Opam 2.0 or later
Installed through Opam:
* Coq 8.9-8.12 (versions past 8.12 may also work, but have not been tested)
* coq-serapi

Installed through pip (you can install these with `pip install -r requirements.txt`):
* tqdm
* sexpdata
* pampy

Usage
-----

See example.py for usage.
