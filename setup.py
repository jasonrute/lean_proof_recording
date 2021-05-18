#!/usr/bin/env python3
from setuptools import find_packages, setup

setup(
    name="lean_proof_recording",
    version="0.0.1",
    packages=find_packages(),
    package_data={},
    install_requires=[
        "mpmath",
        "pandas",
        "jsonlines",
        "tqdm",
    ],
)
