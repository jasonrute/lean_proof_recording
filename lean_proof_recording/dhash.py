from mpmath import mp, mpf, fmod
import hashlib

mp.dps = 50


def hash_string_to_int(arg):
    return int(hashlib.sha256(arg.encode("utf-8")).hexdigest(), 16) % 10 ** 30


def hash_string_to_float(arg):
    x = mpf(hash_string_to_int(arg))
    return fmod(x * mp.pi, mpf(1.0))


def get_split(arg, train_threshold=0.92, valid_threshold=0.96):
    float_hash = hash_string_to_float(arg.split()[0])
    if float_hash < train_threshold:
        return "train"
    elif float_hash < valid_threshold:
        return "valid"
    else:
        return "test"
