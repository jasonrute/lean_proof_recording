from mpmath import mp, mpf, fmod
import hashlib
import math

mp.dps = 50

def hash_string_to_int(arg):
    return int(hashlib.sha256(arg.encode("utf-8")).hexdigest(), 16) % 10**30

def hash_string_to_float(arg):
    x = mpf(hash_string_to_int(arg))
    return fmod(x * mp.pi, mpf(1.))

def get_split(arg):
    float_hash = hash_string_to_float(arg)
    if float_hash < 0.8: return "train"
    elif float_hash < 0.9: return "valid"
    else: return "test"
