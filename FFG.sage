import re
import os
import sys
import math
import time
import glob
import json
import shutil
import random
import operator
import functools
import itertools
import collections
try:
    import pickle5 as pickle
except:
    import pickle


os.system("")               # ENABLE ANSI ESCAPE IN PRINT
LINE_CLEAR = '\x1b[2K'      # ANSI ESCAPE FOR LINE CLEAR


def repr_GF2(e, t):
    # represent integer "e" as a bitstring of t bits
    return bin(e)[2:].zfill(t)


def repr_GF2_tuple(e, t):
    # represent integer "e" as a tuple of its binary representation in t bits
    return tuple(list(map(int, repr_GF2(e, t))))


def repr_GF2_list(v, t):
    # represent each integer element of the vector "v" as a bitstring of t bits
    return tuple([repr_GF2(e, t) for e in v])


def repr_GF2_list_tuple(v, t):
    # represent each integer element of the vector "v" as a tuple 
    # of its binary representation in t bits
    return tuple([repr_GF2_tuple(e, t) for e in v])


def to_GF2_list(v):
    # v -> list of tuples of binary elements e.g. v = ((0,1,0), (1,0,1))
    # represent each tuple element of the vector "v" as a integer
    # to_GF2_list(((0,1,0), (1,0,1))) -> (2, 5)
    return tuple(int("".join(map(str, e)), 2) for e in v)


def GF2_list_to_int(v, t):
    # t -> bits
    # v -> list of integers e.g. v = (5, 7, 9)
    # compute the integer representation of v transforming each 
    # element of v as a bitstring of t bits, join all of them and transform
    # the result into an integer
    # GF2_list_to_int((5, 7, 9), 4) -> int("010101111001", 2) = 1401
    return int("".join([repr_GF2(e, t) for e in v]), 2)


def int_to_GF2_list(i, t, n):
    # i -> integer
    # t -> bits of each component
    # n -> number of elements
    # transform the integer "i" as the vector of "n" binary tuples of t bits
    # GF2_list_to_int(1401, 4, 3) -> ((0, 1, 0, 1), (0, 1, 1, 1), (1, 0, 0, 1))
    s = bin(i)[2:].zfill(t * n)
    return tuple(tuple(map(int, [e for e in s[i:i+t]])) for i in range(0, len(s), t))


def GF2_int_get_elem(i, t, n):
    # i -> integer
    # t -> bits of each component
    # n -> number of elements
    # decompose the binary representation of the integer "i" as tuples of t bits
    # tuple(GF2_int_get_elem(1401, 4, 3)) -> ((0, 1, 0, 1), (0, 1, 1, 1), (1, 0, 0, 1))
    r = bin(i)[2:].zfill(t * n)
    for i in range(0, t * n, t):
        yield tuple(map(int, [e for e in r[i:i+t]]))


def beta_GF2_list_to_int(v):
    # v -> vector of bitstrings
    # transform v into an integer (i.e., inverse function of beta_int_to_GF2_list)
    # beta_GF2_list_to_int(("0101", "0111", "1001")) -> 1401
    return int("".join(v), 2)


def beta_int_to_GF2_list(i, t, n):
    # i -> integer
    # t -> bits of each component
    # n -> number of elements
    # as int_to_GF2_list but each component is a bitstring of t bits
    # beta_int_to_GF2_list(1401, 4, 3) -> ["0101", "0111", "1001"]
    s = bin(i)[2:].zfill(t * n)
    return list(s[i:i+t] for i in range(0, len(s), t))


def xor(A, B):
    # compute the XOR between the two integers A and B
    return int(A ^^ B)


def gl_order(q, n):
    # returns the order of the group GL(n) over GF(2)               
    qn = q ** n
    return functools.reduce(operator.mul, (qn - q**i for i in range(n)))


# returns the group GL(n) over GF(2)
def generate_invertible_gln(n):
    MS = MatrixSpace(GF(2), n, n)
    for values in itertools.product(range(2), repeat=n*n):
        g = MS(values)
        try:
            gi = g.inverse()
            yield g
        except:
            pass


def dumps_sort_dict(D, key=None):
    result = "{\n"
    result += "".join("\t{}: {}\n".format(k, v) for k, v in sorted(D.items(), key=key))
    result += "}"
    return result


def str_dict(obj):
    # transform the keys of a dictionary in strings
    if type(obj) == dict:
        return {str(k): str_dict(v) for k, v in obj.items()}
    return obj


def dumps(obj):
    # this function returns the string version of "obj"
    if type(obj) != dict:
        s = json.dumps(list(map(str, obj)), indent=4)
    else:
        s = json.dumps(str_dict(obj), indent=4)
    s = re.sub(r"\\n", r"\n     ", s)
    return re.sub(r"\"", "", s)
 

def pickle_write(DIRNAME, filename, data, mode="ab"):
    # write to the DISK a binary object with pickle
    with open(os.path.join(DIRNAME, filename), mode) as f:
        pickle.dump(data, f, protocol=pickle.HIGHEST_PROTOCOL)


def pickle_load(DIRNAME, filename):
    # load from the DISK a binary object with pickle
    with open(os.path.join(DIRNAME, filename), 'rb') as f:
        D = pickle.load(f)
    return D


# SUM TABLE for Q = (0, 1, 2, 3, 4, 5, 6, 7, 8, 9)
# table sum for STS(19)
STS_19_TABLE = {
    "len": 12,
    "neutral_element": 0,
    "tables": [
        [1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 4, 6],
        [2, 3, 4, 5, 3, 5, 6, 5, 7, 5, 8, 7],
        [8, 6, 7, 9, 4, 7, 9, 8, 9, 6, 9, 8]]}


# table sum for STS(27)
STS_27_TABLE = {
    "len": 26,
    "neutral_element": "n",
    "tables": [[
        [1,  2,  3,  4, 5, 6, 7,  8,  9,  6, 11, 12, 0,  2, 3, 4, 5,  6,  7,  8,  9, 10, 11, 12, 0, 1],
        [3,  4,  5, 10, 7, 8, 9, 10, 11, 12,  0,  1, 2,  5, 6, 7, 8,  9, 10, 11, 12,  0,  1,  2, 3, 4],
        [9,  6, 11, 12, 0, 1, 2,  3,  4,  5,  6,  7, 8, 10, 7, 8, 9, 10, 11, 12,  0,  1,  2,  3, 4, 5]
    ],[
        [1,  2,  3,  4, 5, 6, 7,  8,  9, 10, 11, 12, 0, 2, 3, 4, 5,  6,  7,  8,  9, 10, 11, 12, 0, 1],
        [3,  4,  5,  6, 7, 8, 9, 10, 11, 12,  0,  1, 2, 5, 6, 7, 8,  9, 10, 11, 12,  0,  1,  2, 3, 4],
        [9, 10, 11, 12, 0, 1, 2,  3,  4,  5,  6,  7, 8, 6, 7, 8, 9, 10, 11, 12,  0,  1,  2,  3, 4, 5]
    ]]}


# SUM TABLE for Q = "n0123456789abcde"
# table sum for STS(31)
STS_31_TABLE = {
    "len": 35,
    "neutral_element": "n",
    "tables": {
        2: ["00000001111112222223333444455556666",
            "13579bd3478bc3478bc789a789a789a789a",
            "2468ace569ade65a9edbcdecbededcbdebc"],
        3: ["00000001111112222223333444455556666",
            "13579bd3478bc3478bc789a789a789a789a",
            "2468ace569ade65a9edbcdedebcedcbcbed"],
        7: ["00000001111112222223333444455556666",
            "13579bd3478bc3478bc789a789a789a789a",
            "2468ace569ade65a9edbdececbdcedbdbce"],
        61: ["00000001111112222223333444455556666",
             "13579bd3478ac34789b789c789a78ab789a",
             "2468ace569bde65aecdbaedecdbd9cecdbe"],
        80: ["00000001111112222223333444455566678",
             "13579bd3469ac34578b678a58ab78979c9a",
             "2468ace578bde96aecdbcded9cebecaeddb"],
    }}


# function to sum elements in Q in table, where "e" is the neutral_element
# A + B = B + A
# A + A = e
# A + e = e + A = A
def sum_table(table_len, table, a, b, neutral_element=int(0)):
    if a == neutral_element:
        return b
    if b == neutral_element:
        return a
    if a == b:
        return neutral_element
    
    ab = set([a, b])
    for i in range(table_len):
        triple = set([table[j][i] for j in range(3)])
        if ab & triple == ab:
            return list(triple - ab)[0]
    return None


# sum for Q = (0, 1, 2, 3, 4, 5, 6, 7, 8, 9)
def sum_STS_19(A, B):
    return sum_table(STS_19_TABLE["len"], STS_19_TABLE["tables"], 
        A, B, neutral_element=STS_19_TABLE["neutral_element"])


# sum for Q = ("n", 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12)
def sum_STS_27(table_idx, A, B):
    return sum_table(STS_27_TABLE["len"], STS_27_TABLE["tables"][table_idx], 
        A, B, neutral_element=STS_27_TABLE["neutral_element"])


# sum for Q = "n0123456789abcde"
def sum_STS_31(table_idx, A, B):
    return sum_table(STS_31_TABLE["len"], STS_31_TABLE["tables"][table_idx], 
        A, B, neutral_element=STS_31_TABLE["neutral_element"])


# compute minimal assignment for Q such that one obtains all the elements of Q
def compute_minimal_element(sum_func, Q):
    flag = False
    el_map = {}
    element = Q[1:3]
    neutral_element = set(Q[0])
    get_min = lambda X, Y: X if X[1] <= Y[1] else Y 
    while not flag:
        el_map = {}
        elements = set(element)
        prev_len, next_len = int(0), len(elements)
        while prev_len < next_len:
            prev_len = len(elements)
            for (A, B) in itertools.combinations(elements, 2):
                AB_sum = sum_func(A, B)
                elements.add(AB_sum)
                AB = sorted([A, B])
                if AB_sum not in el_map:
                    el_map[AB_sum] = (AB[0], AB[1])
                else:
                    el_map[AB_sum] = get_min(el_map[AB_sum], (AB[0], AB[1]))
            next_len = len(elements)
        if len(elements) == len(Q) - 1:
            flag = True
        else:
            max_element = max(sorted(elements - neutral_element))
            element += Q[Q.index(max_element) + 1]
    return element, el_map


# function to sum elements in N
def sum_N(A, B):
    return int(xor(A, B))


# function to sum elements in Q
def sum_Q(A, B):
    return sum_N(A, B)


# returns the automorphism for the alphas
def alphas_automorphism(t):
    return generate_invertible_gln(t)


# returns the automorphism for the betas
def betas_automorphism(c):
    return generate_invertible_gln(c)


# returns the automorphism for the alphas when Q = (0, 1, 2, 3, 4, 5, 6, 7, 8, 9)
def betas_STS_19_automorphism(Q):
    for a, b, c in itertools.product(Q[1:], repeat=3):
        if a == b: continue
        ab_sum = sum_STS_19(a, b)
        if c == a or c == b or c == ab_sum: continue
        curr_beta = {}
        curr_beta[int(0)] = int(0)
        curr_beta[int(1)] = a
        curr_beta[int(2)] = b
        curr_beta[int(3)] = c
        curr_beta[int(8)] = sum_STS_19(curr_beta[int(1)], curr_beta[int(2)])
        curr_beta[int(6)] = sum_STS_19(curr_beta[int(1)], curr_beta[int(3)])
        curr_beta[int(7)] = sum_STS_19(curr_beta[int(6)], curr_beta[int(8)])
        curr_beta[int(4)] = sum_STS_19(curr_beta[int(2)], curr_beta[int(3)])
        curr_beta[int(5)] = sum_STS_19(curr_beta[int(4)], curr_beta[int(6)])
        curr_beta[int(9)] = sum_STS_19(curr_beta[int(1)], curr_beta[int(5)])
        yield curr_beta
    
    
# returns the automorphism for the alphas when Q = ("n", 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12)
def betas_STS_27_automorphism(table_idx, Q):
    if table_idx == 0:
        SIGMA_MAP = {
             0: 0, 1: 1, 10: 10,
             6: 8, 8: 6,
            11: 2, 2: 11,
             9: 3, 3: 9,
            12: 4, 4: 12,
             5: 7, 7: 5
        }
        id_map = lambda x: x
        rho = lambda x: (x * 3) % 13
        rho2 = lambda x, rho=rho: rho(rho(x))
        sigma = lambda x, SIGMA_MAP=SIGMA_MAP: SIGMA_MAP[x]
        rho_sigma = lambda x, rho=rho, sigma=sigma: rho(sigma(x))
        rho2_sigma = lambda x, rho2=rho2, sigma=sigma: rho2(sigma(x))
        for func in [id_map, rho, rho2, sigma, rho_sigma, rho2_sigma]:
            yield func
    elif table_idx == 1:
        for a in [1, 3, 9]:
            for b in Q[1:]:
                func = lambda x, a=a, b=b: (a * x + b) % 13
                yield func


def beta_STS_31_for_table(table_idx, a, b, c, d=None):
    curr_beta = {}
    if table_idx == 2:
        curr_beta["n"] = "n"
        curr_beta["0"] = a
        curr_beta["1"] = b
        curr_beta["3"] = c
        curr_beta["7"] = d
        curr_beta["2"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["1"])
        curr_beta["4"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["3"])
        curr_beta["5"] = sum_STS_31(table_idx, curr_beta["1"], curr_beta["3"])
        curr_beta["6"] = sum_STS_31(table_idx, curr_beta["1"], curr_beta["4"])
        curr_beta["8"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["7"])
        curr_beta["9"] = sum_STS_31(table_idx, curr_beta["1"], curr_beta["7"])
        curr_beta["a"] = sum_STS_31(table_idx, curr_beta["2"], curr_beta["7"])
        curr_beta["b"] = sum_STS_31(table_idx, curr_beta["3"], curr_beta["7"])
        curr_beta["c"] = sum_STS_31(table_idx, curr_beta["4"], curr_beta["7"])
        curr_beta["d"] = sum_STS_31(table_idx, curr_beta["6"], curr_beta["7"])
        curr_beta["e"] = sum_STS_31(table_idx, curr_beta["5"], curr_beta["7"])
    elif table_idx == 3:
        curr_beta["n"] = "n"
        curr_beta["0"] = a
        curr_beta["1"] = b
        curr_beta["3"] = c
        curr_beta["7"] = d
        curr_beta["2"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["1"])
        curr_beta["4"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["3"])
        curr_beta["5"] = sum_STS_31(table_idx, curr_beta["1"], curr_beta["3"])
        curr_beta["6"] = sum_STS_31(table_idx, curr_beta["2"], curr_beta["3"])
        curr_beta["8"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["7"])
        curr_beta["9"] = sum_STS_31(table_idx, curr_beta["1"], curr_beta["7"])
        curr_beta["a"] = sum_STS_31(table_idx, curr_beta["2"], curr_beta["7"])
        curr_beta["b"] = sum_STS_31(table_idx, curr_beta["3"], curr_beta["7"])
        curr_beta["c"] = sum_STS_31(table_idx, curr_beta["6"], curr_beta["7"])
        curr_beta["d"] = sum_STS_31(table_idx, curr_beta["4"], curr_beta["7"])
        curr_beta["e"] = sum_STS_31(table_idx, curr_beta["5"], curr_beta["7"])
    elif table_idx == 7:
        curr_beta["n"] = "n"
        curr_beta["0"] = a
        curr_beta["1"] = b
        curr_beta["3"] = c
        curr_beta["7"] = d
        curr_beta["2"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["1"])
        curr_beta["4"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["3"])
        curr_beta["5"] = sum_STS_31(table_idx, curr_beta["1"], curr_beta["3"])
        curr_beta["6"] = sum_STS_31(table_idx, curr_beta["2"], curr_beta["3"])
        curr_beta["8"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["7"])
        curr_beta["9"] = sum_STS_31(table_idx, curr_beta["1"], curr_beta["7"])
        curr_beta["a"] = sum_STS_31(table_idx, curr_beta["2"], curr_beta["7"])
        curr_beta["b"] = sum_STS_31(table_idx, curr_beta["3"], curr_beta["7"])
        curr_beta["c"] = sum_STS_31(table_idx, curr_beta["5"], curr_beta["7"])
        curr_beta["d"] = sum_STS_31(table_idx, curr_beta["6"], curr_beta["7"])
        curr_beta["e"] = sum_STS_31(table_idx, curr_beta["4"], curr_beta["7"])
    elif table_idx == 61:
        curr_beta["n"] = "n"
        curr_beta["0"] = a
        curr_beta["1"] = b
        curr_beta["3"] = c
        curr_beta["7"] = d
        curr_beta["2"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["1"])
        curr_beta["4"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["3"])
        curr_beta["5"] = sum_STS_31(table_idx, curr_beta["1"], curr_beta["3"])
        curr_beta["6"] = sum_STS_31(table_idx, curr_beta["2"], curr_beta["3"])
        curr_beta["8"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["7"])
        curr_beta["9"] = sum_STS_31(table_idx, curr_beta["1"], curr_beta["7"])
        curr_beta["a"] = sum_STS_31(table_idx, curr_beta["2"], curr_beta["7"])
        curr_beta["b"] = sum_STS_31(table_idx, curr_beta["3"], curr_beta["7"])
        curr_beta["c"] = sum_STS_31(table_idx, curr_beta["6"], curr_beta["7"])
        curr_beta["d"] = sum_STS_31(table_idx, curr_beta["5"], curr_beta["7"])
        curr_beta["e"] = sum_STS_31(table_idx, curr_beta["4"], curr_beta["7"])
    elif table_idx == 80:
        curr_beta["n"] = "n"
        curr_beta["0"] = a
        curr_beta["1"] = b
        curr_beta["3"] = c
        curr_beta["2"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["1"])
        curr_beta["4"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["3"])
        curr_beta["5"] = sum_STS_31(table_idx, curr_beta["1"], curr_beta["3"])
        curr_beta["6"] = sum_STS_31(table_idx, curr_beta["0"], curr_beta["5"])
        curr_beta["7"] = sum_STS_31(table_idx, curr_beta["1"], curr_beta["4"])
        curr_beta["8"] = sum_STS_31(table_idx, curr_beta["1"], curr_beta["6"])
        curr_beta["9"] = sum_STS_31(table_idx, curr_beta["2"], curr_beta["3"])
        curr_beta["a"] = sum_STS_31(table_idx, curr_beta["2"], curr_beta["5"])
        curr_beta["b"] = sum_STS_31(table_idx, curr_beta["3"], curr_beta["6"])
        curr_beta["c"] = sum_STS_31(table_idx, curr_beta["3"], curr_beta["7"])
        curr_beta["d"] = sum_STS_31(table_idx, curr_beta["4"], curr_beta["5"])
        curr_beta["e"] = sum_STS_31(table_idx, curr_beta["2"], curr_beta["7"])
    return curr_beta


# returns the automorphism for the alphas when Q = "n0123456789abcde"
def betas_STS_31_automorphism(table_idx, Q):
    table_len = STS_31_TABLE["len"]
    curr_table = STS_31_TABLE["tables"][table_idx]
    triples = [set(curr_table[j][i] for j in range(3)) for i in range(table_len)]
    repeat = 4 if table_idx != 80 else 3
    for elements in itertools.product(Q[1:], repeat=repeat):
        if len(set(elements)) != repeat: continue
        if table_idx != 80:
            a, b, c, d = elements
            ab_sum = sum_STS_31(table_idx, a, b)
            ac_sum = sum_STS_31(table_idx, a, c)
            bc_sum = sum_STS_31(table_idx, b, c)
            ab_c_sum = sum_STS_31(table_idx, ab_sum, c)
            if c == ab_sum or d in [ab_sum, ac_sum, bc_sum, ab_c_sum]: continue
        else:
            (a, b, c), d = elements, None
            ab_sum = sum_STS_31(table_idx, a, b)
            if c == ab_sum: continue

        curr_beta = beta_STS_31_for_table(table_idx, a, b, c, d=d)
        # check automorphism
        idx = int(0)
        flag = True
        while flag and idx < len(triples):
            A, B, C = triples[idx]
            beta_ABC = set([curr_beta[A], curr_beta[B], curr_beta[C]])
            if len(beta_ABC) != 3 or beta_ABC not in triples:
                flag = False
            idx += int(1)
        if not flag: continue
        yield curr_beta


# apply the beta to an elemnt of Q
def beta_map(beta, A, c):
    # beta_map:  Q  -> Q
    #            A |-> beta(A)
    # beta(A) = "beta" * A
    # vector(GF(2), A) = vector(GF(2), A) -> cast A to a vector object
    r = tuple(beta * vector(GF(2), repr_GF2_tuple(A, c)))
    return int("".join(map(str, r)), 2)


# apply the beta to an elemnt of Q = (0, 1, 2, 3, 4, 5, 6, 7, 8, 9)
def beta_STS_19_map(beta, A):
    return beta[A]


# apply the beta to an elemnt of Q = ("n", 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12)
def beta_STS_27_map(beta, A):
    return beta(A)


# apply the beta to an elemnt of Q = "n0123456789abcde"
def beta_STS_31_map(beta, A):
    return beta[A]


def seconds_to_age(t):
    # transform time "t" into its corresponding YEARS - DAYS - HOURS - MINUTES - SECONDS - MILLISECONDS
    idx = 0
    res = []
    ms = (t - int(t)) * 1000
    t = int(t)
    div = [60, 60, 24, 365]
    suffix = ["s", "m", "h", "d", "y"]
    while idx < len(div) and t >= div[idx]:
        t, r = divmod(t, div[idx])
        res.append(r)
        idx += 1
    res.append(t)
    res = res[::-1]
    return " ".join("{} {}".format(res[i], suffix[len(res) - i - 1]) for i in range(len(res))) + " {:.2f} ms".format(ms)


def get_size(obj, seen=None):
    size = sys.getsizeof(obj)
    if seen is None: seen = set()
    obj_id = id(obj)
    if obj_id in seen: return 0
    # Important mark as seen *before* entering recursion to gracefully handle
    # self-referential objects
    seen.add(obj_id)
    if isinstance(obj, dict):
        size += sum([get_size(v, seen) for v in obj.values()])
        size += sum([get_size(k, seen) for k in obj.keys()])
    elif hasattr(obj, '__dict__'):
        size += get_size(obj.__dict__, seen)
    elif hasattr(obj, '__iter__') and not isinstance(obj, (str, bytes, bytearray)):
        size += sum([get_size(i, seen) for i in obj])
    return size


def rescale_size(size):
    i = 0
    res = []
    scale = ["B", "KiB", "MiB", "GiB", "TiB", "PiB", "EiB", "ZiB", "YiB"]
    while i < (len(scale) - 1) and size >= 1024:
        size, r = divmod(size, 1024)
        res.append(r)
        i += 1
    res.append(size)
    res = res[::-1]
    # return "{:.3f} {}".format(size, scale[i])
    return " ".join("{} {}".format(res[i], scale[len(res) - i - 1]) for i in range(len(res)) if res[i] > 0)


class NQMappings(object):

    def __init__(self, DIR, t, c, num_representatives, index=None, Q_type=None, reset_files=False, enable_print=True):
        assert index is None or type(index) == int
        assert Q_type is None or Q_type in ["STS19", "STS27", "STS31", "UPDATE"]

        if Q_type is None:
            Q_type_str = "c_{}".format(c)
        elif Q_type == "UPDATE":
            Q_type_str = "STS31"
        else:
            Q_type_str = Q_type

        index = "" if index is None else "_{}".format(index)
        self.Q_type = Q_type

        self.t, self.c = t, c
        self.ENABLE_PRINT = enable_print
        self.num_representatives = num_representatives
        self.DIRNAME = os.path.join(DIR, "t_{}_{}{}".format(t, Q_type_str, index))
        self.OUTPUT_FILEPATH = os.path.join(self.DIRNAME, "output_t_{}_{}{}.txt".format(t, Q_type_str, index))
        if reset_files:
            if os.path.exists(self.DIRNAME):
                shutil.rmtree(self.DIRNAME)
            os.mkdir(self.DIRNAME)
            with open(self.OUTPUT_FILEPATH, "w") as fp:
                pass

        self.N_field = GF(2)
        # N = {0, 1}^t 
        # {0}^t = (0, ..., 0) -> neutral element
        self.N = list(int(e) for e in range(2 ** t))
        if self.Q_type is None or self.Q_type == "UPDATE":
            # Q = {0, 1}^c
            # {0}^c = (0, ..., 0) -> neutral element
            self.Q = list(int(e) for e in range(2 ** c))
        elif self.Q_type == "STS19":
            # 0 -> neutral element
            self.Q = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
        elif self.Q_type == "STS27":
            # n -> neutral element
            self.Q = ["n", 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
        elif self.Q_type == "STS31":
            # n -> neutral element
            self.Q = "n0123456789abcde"

        # Q_comb -> all the combinations with replacement of the elements of Q taken 2 at a time
        self.Q_comb = list(itertools.combinations_with_replacement(self.Q, 2))
        # remove (A, A), (A, 0), (0, A), where "0" is the neutral element in "Q"
        self.Q_comb = [(A, B) for A, B in self.Q_comb if A != self.Q[0] and B != self.Q[0] and A != B]

        self.f_printf("N -> GF(2)^{}\n".format(t))
        if self.Q_type is None:
            self.f_printf("Q -> GF(2)^{}\n".format(c))

        self.f_printf("\nN -> {}\n".format(dumps(repr_GF2_list_tuple(self.N, self.t))))
        if self.Q_type is None:
            self.f_printf("\nQ -> {}\n".format(dumps(repr_GF2_list_tuple(self.Q, self.c))))
        else:
            self.f_printf("\nQ -> {}\n".format(dumps(self.Q)))
    
    def class_reduction(self, filename, STS_31_NUM):
        if self.Q_type is not None and self.Q_type not in ["STS31", "UPDATE"]:
            return

        print("\nLoading factor systems...")
        
        Q_comb_len = len(self.Q_comb)
        new_factor_systems = []
        factor_systems = pickle_load(self.DIRNAME, filename)
        factor_systems = [sorted(k)[0] for k in factor_systems]
        factor_systems = [list(map(int, beta_int_to_GF2_list(F_j, self.t, Q_comb_len))) for F_j in factor_systems]
                    
        counter = int(0)
        print("Starting search...\n")
        start = time.perf_counter()
        for i, factor_system in enumerate(factor_systems):
            bad_factor_system = False
            S = self.Q[1:] if STS_31_NUM == 1 else self.Q[1]
            T = self.Q_comb[:]
            
            curr_time = time.perf_counter() - start
            expected_time = len(factor_systems) * curr_time / (i + 1)
            print("#F -> {} / {} - S length -> {} - Counter -> {} - Current time -> {} - Expected time -> {}...".format(
                i + 1, len(factor_systems), len(S), counter, seconds_to_age(curr_time), seconds_to_age(expected_time)), end="\r")

            while len(S) > 0:
                P = S[0]
                exit_early = None
                T = [(A, B) for A, B in T if A != P and B != P and self.sum_Q(A, B) != P]
                curr_time = time.perf_counter() - start
                print("#F -> {} / {} - S length -> {} - Counter -> {} - Current time -> {} - Expected time -> {}...".format(
                    i + 1, len(factor_systems), len(S), counter, seconds_to_age(curr_time), seconds_to_age(expected_time)), end="\r")
                if len(T) == 0: 
                    # factor_system is good
                    break
                for A, B in T:
                    PA_idx = self.find_in_Q_comb(P, A)
                    PA_B_idx = self.find_in_Q_comb(self.sum_Q(P, A), B)
                    AB_idx = self.find_in_Q_comb(A, B)
                    P_AB_idx = self.find_in_Q_comb(P, self.sum_Q(A, B))
                    left_side = self.sum_N(factor_system[PA_idx], factor_system[PA_B_idx])
                    right_side = self.sum_N(factor_system[AB_idx], factor_system[P_AB_idx])
                    if left_side != right_side:
                        exit_early = (A, B)
                        break
                if exit_early is not None:
                    A, B = exit_early
                    S = [E for E in S if E not in [P, A, B]]
                else: # check for next factor_system
                    counter += int(1)
                    bad_factor_system = True
                    break
                curr_time = time.perf_counter() - start
                print("#F -> {} / {} - S length -> {} - Counter -> {} - Current time -> {} - Expected time -> {}...".format(
                    i + 1, len(factor_systems), len(S), counter, seconds_to_age(curr_time), seconds_to_age(expected_time)), end="\r")

            if bad_factor_system is False:
                F_j = beta_GF2_list_to_int(list(map(str, factor_system)))
                new_factor_systems.append(F_j)
        curr_time = time.perf_counter() - start
        print("\n\nGood factor systems -> {}".format(len(factor_systems) - counter))
        print("Bad factor systems -> {}".format(counter))
        assert len(new_factor_systems) == len(factor_systems) - counter
        pickle_write(self.DIRNAME, "beta_classes_updated", new_factor_systems, mode="wb")

    def set_sumNQ(self, sum_N, sum_Q):
        self.sum_N, self.sum_Q = sum_N, sum_Q
        
        AB_AAB_BAB_pos = self.get_AB_AAB_BAB()
        Q_triple = []
        for e in AB_AAB_BAB_pos:
            Q_triple.append(self.Q_comb[e[0]])
        self.Q_comb = Q_triple[:]
 
    def set_automorphisms(self, aut_alpha, aut_beta):
        self.alpha_aut, self.beta_aut = aut_alpha, aut_beta
 
    def set_beta_map(self, curr_beta_map):
        self.beta_map = curr_beta_map
 
    def f_printf(self, text):        
        if not self.ENABLE_PRINT: return
        with open(self.OUTPUT_FILEPATH, "a") as fp:
            fp.writelines(text)
 
    def get_AB_AAB_BAB(self):
        # find_in_comb[(A, B)] is the index of (A, B) in Q_comb, that is,
        # in which position one finds (A, B) into the array Q_comb
        # we put (A, B) if A <= B, otherwise we put (B, A)
        find_in_comb = {}

        # Q_comb[i] = AB = (A, B)
        for i, AB in enumerate(self.Q_comb):
            A, B = AB
            # A = (a_1, a_2, ..., a_n)
            # B = (b_1, b_2, ..., b_n)
            # A <= B if a_j <= b_j for all j
            if A <= B:
                find_in_comb[(A, B)] = i
            else:
                find_in_comb[(B, A)] = i

        # AB_find -> returns position of (A, B) in Q_comb
        AB_find = lambda A, B: find_in_comb[(A, B)] if A <= B else find_in_comb[(B, A)]
        
        # AB_AAB_BAB_pos := [(a_00, a_01, a_02), ..., (a_l0, a_l1, a_l2)],
        # where, for all (A, B) in Q_comb, 
        # a_i0 is the position of (A, B) in Q_comb
        # a_i1 is the position of (A, A + B) in Q_comb
        # a_i2 is the position of (B, A + B) in Q_comb
        # these indices will be used in order to force the condition
        # F(A, B) = F(A, A + B) = F(B, A + B)
        AB_AAB_BAB_pos = []

        for AB in self.Q_comb:
            A, B = AB
            # AB_sum = A + B
            AB_sum = self.sum_Q(A, B)
            # AB_idx -> position of (A, B) in Q_comb
            AB_idx = AB_find(A, B)
            # AAB_idx -> position of (A, A + B) in Q_comb
            AAB_idx = AB_find(A, AB_sum)
            # BAB_idx -> position of (B, A + B) in Q_comb
            BAB_idx = AB_find(B, AB_sum)
            # sort the above indices such that
            # key := [k_0, k_1, k_2] with k_0 <= k_1 <= k_2
            key = tuple(sorted([AB_idx, AAB_idx, BAB_idx]))
            if len(set(key)) < 3:
                continue
            # ignore repeated "key" in order to avoid redundancy and increase efficiency
            if key not in AB_AAB_BAB_pos:
                AB_AAB_BAB_pos.append(key)
        return AB_AAB_BAB_pos
    
    def find_in_Q_comb(self, A, B):
        # find_in_Q_comb(A, B) is the index of (A, B), (A, A + B), (B, A + B) in Q_comb
        if A >= B: A, B = B, A
        AB_sum = self.sum_Q(A, B)
        triples = [(A, B), (min(A, AB_sum), max(A, AB_sum)), (min(B, AB_sum), max(B, AB_sum))]
        for i, (cA, cB) in enumerate(self.Q_comb):
            if (cA, cB) in triples:
                return i
        raise Exception("({}, {}) not found in Q".format(A, B))

    def find_phi_delta(self):
        # this functions computes all the delta1-phi functions
        
        # all_sum_Q -> dictionary of all (A + B) for A, B in Q_comb
        # all_sum_Q[(A, B)] = A + B
        # this dictionary is useful to speed up the delta1_def function because
        # precomputes these results
        all_sum_Q = {}
        for AB in self.Q_comb:
            A, B = AB
            all_sum_Q[(A, B)] = all_sum_Q[(B, A)] = self.sum_Q(A, B)
            
        # N_comb = all the combinations with replacement of the elements of N taken 2 at a time
        N_comb = list(itertools.combinations_with_replacement(self.N, 2))

        # all_sum_N -> dictionary of all (A + B) for A, B in N
        # all_sum_N[(A, B)] = A + B
        # this dictionary is useful to speed up the delta1_def function because
        # precomputes these results
        all_sum_N = {}
        for AB in N_comb:
            A, B = AB
            all_sum_N[(A, B)] = all_sum_N[(B, A)] = self.sum_N(A, B)

        # phi is a function which maps elements from Q to N
        # phi_func -> phi_j(R)
        phi_func = lambda phi, R: self.N[phi[self.Q.index(R)]]
        # delta1 phi_j partial := phi_j(R) + phi_j(S)
        delta1_partial = lambda phi, R, S: all_sum_N[(phi_func(phi, R), phi_func(phi, S))]
        # delta1 phi_j := delta1_phi_j_partial(R, S) + phi_j(R + S) := phi_j(R) + phi_j(S) + phi_j(R + S)
        delta1_def = lambda phi, R, S: all_sum_N[(delta1_partial(phi, R, S), phi_func(phi, all_sum_Q[(R, S)]))]
        
        if self.Q_type is None:
            self.f_printf("\nQ point combinations -> {}\n".format(dumps(
                [(repr_GF2_tuple(A, self.c), repr_GF2_tuple(B, self.c)) for A, B in self.Q_comb])))
        else:
            self.f_printf("\nQ point combinations -> {}\n".format(dumps(self.Q_comb)))
        
        # delta1_phi -> dictionary of all the delta1-phi-functions grouped by delta1-phi_j results,
        # that is, the results of applying delta1-phi_j to every (A, B) in Q_comb
        delta1_phi = set([])

        # phi -> array of length |Q| which describes the mapping from Q to N
        # phi = (a_0, a_1, ..., a_n), where a_0 is the index of an element in N
        # such phi-function maps Q[i] onto N[a_i] for all i
        for partial_phi in itertools.product(range(len(self.N)), repeat=len(self.Q)-1):
            # to ignore every phi which maps the first element of Q onto
            # an element of N different from N[0], we generate |Q|-1 elements
            # and force phi[0] = 0
            phi = (0, ) + partial_phi

            # list of all the applications of this phi to all (A, B) in Q_comb
            key = tuple(delta1_def(phi, R, S) for R, S in self.Q_comb)
            key = GF2_list_to_int(key, self.t)

            # "key" is used as a key for the dictionary "delta1_phi"
            # if exists another phi_j which produces the same "key" tuple,
            # append the latter to delta1_phi with key "key"
            # example:
            #     delta1_phi = {
            #         (0, 0, 1, 1, 1, 1, 0, 0): [
            #            (0, 1, 1, 2)
            #         ]
            #     }, where
            #     (0, 0, 1, 1, 1, 1, 0, 0) is the result of applying 
            #     phi_i = (0, 1, 1, 2) to all (A, B) in Q_comb
            #
            #     suppose that exists phi_j = (1, 2, 1, 1) such that
            #     delta1-phi_j = (0, 0, 1, 1, 1, 1, 0, 0) for all (A, B) in Q_comb
            #     the following instruction procudes the following result:
            #     delta1_phi = {
            #         (0, 0, 1, 1, 1, 1, 0, 0): [
            #            (0, 1, 1, 2),
            #            (1, 2, 1, 1)
            #         ]
            #     }, that is,
            #     we append (1, 2, 1, 1) to the list associated to the delta1-phi
            #     result (0, 0, 1, 1, 1, 1, 0, 0)
            
            # delta1_phi.get(key, []) returns delta1_phi[key] if
            # key exists in delta1_phi, otherwise returns an empty array []
            # delta1_phi[key] = delta1_phi.get(key, collections.deque([])) + collections.deque([phi])
            delta1_phi.add(key)
            
        delta1_phi = sorted(delta1_phi)
        print("There are {} delta1-phi functions".format(len(delta1_phi)))
        self.f_printf("\nThere are {} delta1-phi functions\n".format(len(delta1_phi)))
        for i, key in enumerate(delta1_phi):
            self.f_printf("\ndelta1-phi[{}] = F[{}] -> {}\n".format(i, key, int_to_GF2_list(key, self.t, len(self.Q_comb))))
            # self.f_printf("equals phi for delta1 -> {}\n".format(dumps(delta1_phi[key])))
        
        pickle_write(self.DIRNAME, "delta1_phi", delta1_phi, mode="wb")
        return delta1_phi

    def get_coset_representative(self, F, cosets, delta1):
        # return coset representative for F
        for c in [xor(F, d) for d in delta1]:
            if c in cosets:
                return int(c)
        return None

    def coset_blocks(self, delta1):
        start = time.perf_counter()
        num_F_functions = len(self.N) ** len(self.Q_comb)
        num_blocks = len(delta1) # * 8
        step = num_F_functions // num_blocks
        
        if self.num_representatives is None or self.num_representatives <= 0:
            assert num_F_functions % len(delta1) == 0
            self.num_representatives = num_F_functions // len(delta1)

        idx = int(0)
        cosets = set([])
        INNER_STEP_INC = int(50)
        inner_idx, MAX_INNER_STEP = int(0), step // 100

        print("There are {}^{} F-functions".format(len(self.N), len(self.Q_comb)))
        print("Expected number of coset representatives -> {}".format(self.num_representatives))

        if os.path.exists(os.path.join(self.DIRNAME, "cosets")):
            cosets = pickle_load(self.DIRNAME, "cosets")
        while idx < num_blocks and len(cosets) < self.num_representatives:
            inner_idx = int(0)
            prev_length = len(cosets)
            F = {idx*step + j: None for j in range(step)}
            while inner_idx < MAX_INNER_STEP and len(F) > 0 and len(cosets) < self.num_representatives:
                # get random F_i in F
                F_i, _ = F.popitem()

                curr_time = time.perf_counter() - start
                expected_time = int(0) if len(cosets) == 0 else self.num_representatives * curr_time / len(cosets)
                print(LINE_CLEAR + "Computing coset[{}] of {} - F[{}] - Block #{} - Current time -> {} - Expected time -> {}...".format(
                    len(cosets) + 1, self.num_representatives, F_i, idx, seconds_to_age(curr_time), seconds_to_age(expected_time)), end="\r")

                # remove coset [F_i] from F and
                # check if F_i belongs to a previous coset
                coset = None
                for c in [xor(F_i, d) for d in delta1]:
                    # remove coset from F
                    if c in F: 
                        del F[c]
                    # check if F_i belongs to a previous coset
                    if c in cosets:
                        coset = c

                if coset is None:
                    # F_i is a new representative
                    cosets.add(int(F_i))
                    inner_idx = int(0)
                else:
                    inner_idx += int(1)
            idx += int(1) if inner_idx < MAX_INNER_STEP else INNER_STEP_INC
            if prev_length < len(cosets):
                pickle_write(self.DIRNAME, "cosets", cosets, mode="wb")
        print()
        pickle_write(self.DIRNAME, "cosets", cosets, mode="wb")
        self.f_printf("\nThere are {} coset representatives\n".format(len(cosets)))
    
    def compute_alpha_F_old(self, delta1):
        # this function returns all the alpha * F functions
        start = time.perf_counter()

        self.f_printf("\nComputing alpha*F-functions...\n")

        # alpha_F -> a dictionary of all elements in alpha * F
        counter = 0
        alpha_cos = {}
        cosets = pickle_load(self.DIRNAME, "cosets")
        for i, alpha_i in enumerate(self.alpha_aut()):
            counter += 1
            for idx, F_j in enumerate(cosets):
                curr_time = time.perf_counter() - start
                print(LINE_CLEAR + "Computing alphas[{}] * coset[{}] - Time -> {}...".format(
                    i + 1, idx + 1, seconds_to_age(curr_time)), end="\r")

                if F_j not in alpha_cos:
                    alpha_cos[F_j] = set()
                # alpha_F = alpha_i * F_j
                # GF2_int_get_elem(F_j, self.t, len(self.Q_comb)) -> return the components of F_j
                alpha_F = tuple(tuple(alpha_i * vector(self.N_field, component)) for component in GF2_int_get_elem(F_j, self.t, len(self.Q_comb)))
                # transform alpha_F as an integer
                alpha_F = GF2_list_to_int(to_GF2_list(alpha_F), self.t)
                # get coset representative for alpha_F
                F_k = self.get_coset_representative(alpha_F, cosets, delta1)
                if F_k is None: 
                    raise Exception("alpha * F not in coset")
                # map representative F_j to the representative F_k computed from alpha_i * F_j
                alpha_cos[F_j].add(F_k)
        print()

        self.f_printf("\nThere are {} alpha-functions\n".format(counter))
        self.f_printf("\nThere are {} alpha*F mathces\n".format(len(alpha_cos)))
        # self.f_printf("\nmatch for alpha_i * [F_j] = [[F_i1], ..., [F_ik]]\n")
        classes = {}
        new_cosets = set([])
        classes_partition = {}
        for F_j in alpha_cos:
            k = tuple(sorted(alpha_cos[F_j]))
            # self.f_printf("(F_j, [[F_i1], ..., [F_ik]]) -> ({}, {})\n".format(F_j, k))
            classes[k] = classes.get(k, int(0)) + int(1)
        for k in classes:
            key = classes[k]
            classes_partition[key] = classes_partition.get(key, int(0)) + int(1)
        self.f_printf("\nClasses -> {}\n".format(dumps(classes)))
        self.f_printf("\nThere are {} classes\n".format(len(classes)))
        self.f_printf("\nClasses partition -> {}\n".format(dumps(classes_partition)))
        for group in classes:
            new_cosets.add(group[0])

        pickle_write(self.DIRNAME, "alpha_F", alpha_F, mode="wb")
        pickle_write(self.DIRNAME, "alpha_cosets", new_cosets, mode="wb")
        pickle_write(self.DIRNAME, "alpha_classes", classes, mode="wb")
        return new_cosets, classes

    def compute_beta_F_old(self, cosets, delta1):
        # this function returns all the F * beta functions
        start = time.perf_counter()

        self.f_printf("\nComputing F*beta-functions...\n")
            
        # beta_F -> a dictionary of all elements in F * beta
        counter = 0
        beta_cos = {}
        Q_comb_len = len(self.Q_comb)
        for i, beta_i in enumerate(self.beta_aut()):
            counter += 1
            # compute (beta(A), beta(B)) for any (A, B) in Q_comb and find the position
            # of (beta(A), beta(B)) in Q_comb in order to properly permute the function F and
            # compute F * beta
            Q_perm_idx = [self.find_in_Q_comb(self.beta_map(beta_i, A), self.beta_map(beta_i, B)) for A, B in self.Q_comb]
            for idx, F_j in enumerate(cosets):
                curr_time = time.perf_counter() - start
                print(LINE_CLEAR + "Computing coset[{}] * betas[{}] - Time -> {}...".format(
                    idx + 1, i + 1, seconds_to_age(curr_time)), end="\r")

                if F_j not in beta_cos:
                    beta_cos[F_j] = set()
                # cast integer coset representative F_j to list to fast permute its components
                F_j_list = beta_int_to_GF2_list(F_j, self.t, Q_comb_len)
                # F_beta = F_j * beta_i = permute F_j according to Q_perm_idx
                F_beta = beta_GF2_list_to_int([F_j_list[pos] for pos in Q_perm_idx])
                # get coset representative [F_k] for F_beta
                F_k = self.get_coset_representative(F_beta, cosets, delta1)
                if F_k is None: 
                    raise Exception("F * beta not in coset")
                # map representative F_j to the representative k computed from F_j * beta_i
                beta_cos[F_j].add(F_k)
            pickle_write(self.DIRNAME, "F_beta", beta_cos, mode="wb")

        print()
        self.f_printf("\nThere are {} beta-functions\n".format(counter))
        self.f_printf("\nThere are {} F*beta mathces\n".format(len(beta_cos)))
        # self.f_printf("\nmatch for [F_j] * beta_i = [[F_i1], ..., [F_ik]]\n")
        classes = {}
        classes_partition = {}
        for F_j in beta_cos:
            k = tuple(sorted(beta_cos[F_j]))
            # self.f_printf("(F_j, [[F_i1], ..., [F_ik]]) -> ({}, {})\n".format(F_j, k))
            classes[k] = classes.get(k, int(0)) + int(1)
        for k in classes:
            key = classes[k]
            classes_partition[key] = classes_partition.get(key, int(0)) + int(1)
        self.f_printf("\nClasses -> {}\n".format(dumps(classes)))
        self.f_printf("\nThere are {} classes\n".format(len(classes)))
        self.f_printf("\nClasses partition -> {}\n".format(dumps(classes_partition)))

        pickle_write(self.DIRNAME, "F_beta", beta_cos, mode="wb")
        pickle_write(self.DIRNAME, "beta_classes", classes, mode="wb")
        return classes

    def compute_alpha_F(self, delta1):
        # this function returns all the alpha * F functions
        start = time.perf_counter()

        print("Computing alpha*F-functions...\n")

        # alpha_F -> a dictionary of all elements in alpha * F
        idx = int(0)
        counter = int(0)
        alpha_cos = {}
        cosets = pickle_load(self.DIRNAME, "cosets")
        tmp_cosets = cosets.copy()
        
        for alpha_i in self.alpha_aut():
            counter += int(1)

        while len(tmp_cosets) > 0:
            F_j = tmp_cosets.pop()
            if F_j not in alpha_cos:
                alpha_cos[F_j] = set()
            # GF2_int_get_elem(F_j, self.t, len(self.Q_comb)) -> return the components of F_j
            F_j_list = [vector(self.N_field, component) for component in GF2_int_get_elem(F_j, self.t, len(self.Q_comb))]
            for i, alpha_i in enumerate(self.alpha_aut()):
                curr_time = time.perf_counter() - start
                expected_time = len(cosets) * curr_time / (len(cosets) - len(tmp_cosets))
                print(LINE_CLEAR + "Computing alpha[{}] * coset[{}] - Remaining representatives -> {} - Current time -> {} - Estimated time -> {}...".format(
                    i + 1, idx + 1, len(tmp_cosets), seconds_to_age(curr_time), seconds_to_age(expected_time)), end="\r")

                # alpha_F = alpha_i * F_j
                alpha_F = tuple(tuple(alpha_i * component) for component in F_j_list)
                # transform alpha_F as an integer
                alpha_F = GF2_list_to_int(to_GF2_list(alpha_F), self.t)
                # get coset representative for alpha_F
                F_k = self.get_coset_representative(alpha_F, cosets, delta1)
                if F_k is None: 
                    print("alpha[{}] -> {}".format(i + 1, alpha_i))
                    print("coset[{}] -> {}".format(idx + 1, F_j))
                    raise Exception("alpha * F is not representative")
                # map representative F_j to the representative F_k computed from alpha_i * F_j
                alpha_cos[F_j].add(F_k)
                if F_k in tmp_cosets:
                    tmp_cosets.remove(F_k)
            pickle_write(self.DIRNAME, "alpha_F", alpha_F, mode="wb")
            idx += int(1)

        print("\nThere are {} alpha-functions".format(counter))
        self.f_printf("\nThere are {} alpha-functions\n".format(counter))
        self.f_printf("\nThere are {} alpha*F mathces\n".format(len(alpha_cos)))
        # self.f_printf("\nmatch for alpha_i * [F_j] = [[F_i1], ..., [F_ik]]\n")
        new_cosets = set()
        classes_partition = {}
        classes = {tuple(alpha_cos[k]): len(alpha_cos[k]) for k in alpha_cos}
        for F_j in alpha_cos:
            key = len(alpha_cos[F_j])
            classes_partition[key] = classes_partition.get(key, int(0)) + int(1)
        for group in classes:
            new_cosets.add(group[0])
        self.f_printf("\nClasses -> {}\n".format(dumps_sort_dict(classes, lambda x: x[1])))
        self.f_printf("\nThere are {} classes\n".format(len(classes)))
        self.f_printf("\nClasses partition -> {}\n".format(dumps_sort_dict(classes_partition)))

        for k in sorted(classes_partition):
            v = classes_partition[k]
            is_are = "is" if v == 1 else "are"
            loop_s = "loop" if v == 1 else "loops"
            element_s = "element" if k == 1 else "elements"
            self.f_printf("There {} {} {} of {} {}\n".format(is_are, v, loop_s, k, element_s))
        
        pickle_write(self.DIRNAME, "alpha_F", alpha_F, mode="wb")
        pickle_write(self.DIRNAME, "alpha_cosets", new_cosets, mode="wb")
        pickle_write(self.DIRNAME, "alpha_classes", classes, mode="wb")
        return new_cosets, classes

    def compute_beta_F(self, cosets, delta1):
        # this function returns all the F * beta functions
        start = time.perf_counter()

        print("Computing F*beta-functions...\n")
            
        # beta_F -> a dictionary of all elements in F * beta
        idx = int(0)
        beta_cos = {}
        counter = int(0)
        tmp_cosets = cosets.copy()
        Q_comb_len = len(self.Q_comb)
        
        Q_perm_idx = []
        for i, beta_i in enumerate(self.beta_aut()):
            counter += int(1)
            curr_time = time.perf_counter() - start
            print(LINE_CLEAR + "Precomputing beta[{}] indices - Time -> {}...".format(
                i + 1, seconds_to_age(curr_time)), end="\r")
            # compute (beta(A), beta(B)) for any (A, B) in Q_comb and find the position
            # of (beta(A), beta(B)) in Q_comb in order to properly permute the function F and
            # compute F * beta
            curr_Q_perm_idx = [self.find_in_Q_comb(self.beta_map(beta_i, A), self.beta_map(beta_i, B)) for A, B in self.Q_comb]
            Q_perm_idx.append((curr_Q_perm_idx, beta_i))

        print("\nThere are {} beta-functions".format(counter))
        while len(tmp_cosets) > 0:
            F_j = tmp_cosets.pop()
            if F_j not in beta_cos:
                beta_cos[F_j] = set()
            # cast integer coset representative F_j to list to fast permute its components
            F_j_list = beta_int_to_GF2_list(F_j, self.t, Q_comb_len)
            for i in range(len(Q_perm_idx)):
                curr_time = time.perf_counter() - start
                expected_time = len(cosets) * curr_time / (len(cosets) - len(tmp_cosets))
                print(LINE_CLEAR + "Computing coset[{}] * beta[{}] - Remaining representatives -> {} - Current time -> {} - Estimated time -> {}...".format(
                    idx + 1, i + 1, len(tmp_cosets), seconds_to_age(curr_time), seconds_to_age(expected_time)), end="\r")

                # F_beta = F_j * beta_i = permute F_j according to Q_perm_idx
                F_beta = beta_GF2_list_to_int([F_j_list[pos] for pos in Q_perm_idx[i][0]])
                # get coset representative [F_k] for F_beta
                F_k = self.get_coset_representative(F_beta, cosets, delta1)
                if F_k is None: 
                    print("beta[{}] -> {}".format(i + 1, Q_perm_idx[i][1]))
                    print("coset[{}] -> {}".format(idx + 1, F_j))
                    raise Exception("F * beta is not a representative")
                # map representative F_j to the representative k computed from F_j * beta_i
                beta_cos[F_j].add(F_k)
                if F_k in tmp_cosets:
                    tmp_cosets.remove(F_k)
            pickle_write(self.DIRNAME, "F_beta", beta_cos, mode="wb")
            idx += int(1)

        print()
        self.f_printf("\nThere are {} beta-functions\n".format(counter))
        self.f_printf("\nThere are {} F*beta mathces\n".format(len(beta_cos)))
        # self.f_printf("\nmatch for [F_j] * beta_i = [[F_i1], ..., [F_ik]]\n")
        classes_partition = {}
        classes = {tuple(beta_cos[k]): len(beta_cos[k]) for k in beta_cos}
        for F_j in beta_cos:
            key = len(beta_cos[F_j])
            classes_partition[key] = classes_partition.get(key, int(0)) + int(1)
        self.f_printf("\nClasses -> {}\n".format(dumps_sort_dict(classes, lambda x: x[1])))
        self.f_printf("\nThere are {} classes\n".format(len(classes)))
        self.f_printf("\nClasses partition -> {}\n\n".format(dumps_sort_dict(classes_partition)))
        
        for k in sorted(classes_partition):
            v = classes_partition[k]
            is_are = "is" if v == 1 else "are"
            orbit_s = "orbit" if v == 1 else "orbits"
            element_s = "element" if k == 1 else "elements"
            self.f_printf("There {} {} {} of {} {}\n".format(is_are, v, orbit_s, k, element_s))

        pickle_write(self.DIRNAME, "F_beta", beta_cos, mode="wb")
        pickle_write(self.DIRNAME, "beta_classes", classes, mode="wb")
        return classes

    def join_classes(self, alpha_classes, beta_classes):
        classes = []
        for beta_group in beta_classes:
            new_group = []
            beta_group = set(beta_group)
            for alpha_group in alpha_classes:
                if len(beta_group & set(alpha_group)) > 0:
                    new_group.append(alpha_group)
            classes.append(new_group)
        self.f_printf("\nJoined classes -> {}\n".format(dumps(classes)))
        pickle_write(self.DIRNAME, "joined_classes", classes, mode="wb")


def test(DIR, t, c, num_representatives, index):
    start_time = time.perf_counter()
    R = NQMappings(DIR, t, c, num_representatives, index=index)
    R.set_sumNQ(sum_N, sum_Q)
    
    alpha_aut = lambda t=t, alphas_automorphism=alphas_automorphism: alphas_automorphism(t)
    beta_aut = lambda c=c, betas_automorphism=betas_automorphism: betas_automorphism(c)
    curr_beta_map = lambda beta, A, c=c, beta_map=beta_map: beta_map(beta, A, c)
    
    R.set_automorphisms(alpha_aut, beta_aut)
    R.set_beta_map(curr_beta_map)
    
    print("Computing phi and delta1-phi functions...")
    delta1list = R.find_phi_delta()
    end_time = time.perf_counter() - start_time

    flag = str(input("Compute cosets (y|n)? -> ")).lower()
    if flag.startswith("y"):
        print("Computing cosets of the F-functions...")
        start_time = time.perf_counter()
        R.coset_blocks(delta1list)
        end_time += (time.perf_counter() - start_time)

    alpha_classes = None
    flag = str(input("Compute alpha * F (y|n)? -> ")).lower()
    if flag.startswith("y"):
        print("Computing and matching alpha * F functions with F-cosets...")
        start_time = time.perf_counter()
        cosets, alpha_classes = R.compute_alpha_F(delta1list)
        end_time += (time.perf_counter() - start_time)
    else:
        print("Loading cosets from disk...")
        start_time = time.perf_counter()
        # cosets = list(filter(lambda x: not x.startswith("F-"), os.listdir("./backup_cosets_1_4")))
        # cosets = set(list(map(int, cosets)))
        # assert len(cosets) == num_representatives
        # pickle_write(R.DIRNAME, "cosets", cosets)
        cosets = pickle_load(R.DIRNAME, "cosets")
        end_time += (time.perf_counter() - start_time)
    
    print("Computing and matching F * beta functions with F-cosets...")
    start_time = time.perf_counter()
    beta_classes = R.compute_beta_F(cosets, delta1list)
    end_time += (time.perf_counter() - start_time)
    
    if alpha_classes is not None:
        flag = str(input("Join classes (y|n)? -> ")).lower()
        if flag.startswith("y"):
            start_time = time.perf_counter()
            R.join_classes(alpha_classes, beta_classes)
            end_time += (time.perf_counter() - start_time)

    print("END in {}".format(seconds_to_age(end_time)))

    
def test_STS_19(DIR, t, c, num_representatives):
    start_time = time.perf_counter()
    R = NQMappings(DIR, t, c, num_representatives, Q_type="STS19")
    R.set_sumNQ(sum_N, sum_STS_19)
    alpha_aut = lambda t=t, alphas_automorphism=alphas_automorphism: alphas_automorphism(t)
    beta_aut = lambda R=R, betas_STS_19_automorphism=betas_STS_19_automorphism: betas_STS_19_automorphism(R.Q)
    R.set_automorphisms(alpha_aut, beta_aut)
    R.set_beta_map(beta_STS_19_map)
    
    print("Computing phi and delta1-phi functions...")
    delta1list = R.find_phi_delta()

    print("Computing cosets of the F-functions...")
    R.coset_blocks(delta1list)

    print("Computing and matching F * beta functions with F-cosets...")
    # cosets = list(filter(lambda x: not x.startswith("F-"), os.listdir(R.DIRNAME)))
    # cosets = set(list(map(int, cosets)))
    cosets = pickle_load(R.DIRNAME, "cosets")
    beta_classes = R.compute_beta_F(cosets, delta1list)

    end_time = time.perf_counter() - start_time
    print("END in {}".format(seconds_to_age(end_time)))


def test_STS_27(DIR, t, c, num_representatives, index):
    start_time = time.perf_counter()
    
    R = NQMappings(DIR, t, c, num_representatives, index=index, Q_type="STS27")
    
    STS_27_sum = lambda a, b, index=index, sum_STS_27=sum_STS_27: sum_STS_27(index, a, b)
    alpha_aut = lambda t=t, alphas_automorphism=alphas_automorphism: alphas_automorphism(t)
    beta_aut = lambda index=index, R=R, betas_STS_27_automorphism=betas_STS_27_automorphism: betas_STS_27_automorphism(index, R.Q)
    
    R.set_sumNQ(sum_N, STS_27_sum)
    R.set_automorphisms(alpha_aut, beta_aut)
    R.set_beta_map(beta_STS_27_map)
    
    print("Computing phi and delta1-phi functions...")
    delta1list = R.find_phi_delta()

    print("Computing cosets of the F-functions...")
    R.coset_blocks(delta1list)

    print("Computing and matching F * beta functions with F-cosets...")
    # cosets = list(filter(lambda x: not x.startswith("F-"), os.listdir(R.DIRNAME)))
    # cosets = set(list(map(int, cosets)))
    cosets = pickle_load(R.DIRNAME, "cosets")

    beta_classes = R.compute_beta_F(cosets, delta1list)

    end_time = time.perf_counter() - start_time
    print("END in {}".format(seconds_to_age(end_time)))


def test_STS_31(DIR, t, c, num_representatives, index):
    start_time = time.perf_counter()

    if index == 1:
        R = NQMappings(DIR, t, c, num_representatives, index=index, Q_type="UPDATE", reset_files=True, enable_print=True)
        R.set_sumNQ(sum_N, sum_Q)
        
        alpha_aut = lambda t=t, alphas_automorphism=alphas_automorphism: alphas_automorphism(t)
        beta_aut = lambda c=c, betas_automorphism=betas_automorphism: betas_automorphism(c)
        curr_beta_map = lambda beta, A, c=c, beta_map=beta_map: beta_map(beta, A, c)
    else:
        R = NQMappings(DIR, t, 0, num_representatives, index=index, Q_type="STS31", reset_files=True, enable_print=True)
        Q_STS_31_sum = lambda A, B, index=index: sum_STS_31(index, A, B)
        R.set_sumNQ(sum_N, Q_STS_31_sum)
        
        alpha_aut = lambda t=t, alphas_automorphism=alphas_automorphism: alphas_automorphism(t)
        beta_aut = lambda R=R, betas_automorphism=betas_STS_31_automorphism, index=index: betas_automorphism(index, R.Q)
        curr_beta_map = lambda beta, A, beta_map=beta_STS_31_map: beta_map(beta, A)
    
    R.set_automorphisms(alpha_aut, beta_aut)
    R.set_beta_map(curr_beta_map)
    
    if not os.path.exists(os.path.join(R.DIRNAME, "delta1_phi")):
        print("Computing phi and delta1-phi functions...")
        delta1list = R.find_phi_delta()
        end_time = time.perf_counter() - start_time
    else:
        print("Loading delta1_phi from disk...")
        delta1list = pickle_load(R.DIRNAME, "delta1_phi")
        end_time = time.perf_counter() - start_time

    if not os.path.exists(os.path.join(R.DIRNAME, "cosets")):
        print("Computing cosets of the F-functions...")
        start_time = time.perf_counter()
        R.coset_blocks(delta1list)
        end_time += (time.perf_counter() - start_time)

    print("Loading cosets from disk...")
    start_time = time.perf_counter()
    cosets = pickle_load(R.DIRNAME, "cosets")
    end_time += (time.perf_counter() - start_time)
    
    print("Computing and matching F * beta functions with F-cosets...")
    start_time = time.perf_counter()
    beta_classes = R.compute_beta_F(cosets, delta1list)
    end_time += (time.perf_counter() - start_time)

    print("END in {}".format(seconds_to_age(end_time)))


if __name__ == "__main__":
    try:
        Q_types = ["STS19", "STS27", "STS31", "ALL"]
        DIR = str(input("Main directory -> ")) or "D:\GiuseppeFilippone\FFG"
        while True:
            Q_type = str(input("Insert Q type ({}) -> ".format(", ".join(Q_types)))).upper()
            if Q_type in Q_types:
                break
        if Q_type != "STS19":
            indices = str(input("Indices -> ")).strip()
            indices = [None] if indices == "" else list(map(int, indices.split(" ")))
        if Q_type != "STS31" or (Q_type == "STS31" and 1 in indices):
            t, c = [int(e) for e in str(input("Insert t c -> ")).split(" ")]
        else:
            t, c = int(str(input("Insert t -> "))), 0
        num_representatives = eval(str(input("Expected number of cosets -> ")))
        for index in indices:
            if Q_type == "ALL" or (Q_type == "STS31" and index == 1):
                test(DIR, t, c, num_representatives, index)
            elif Q_type == "STS19":
                test_STS_19(DIR, t, c, num_representatives)
            elif Q_type == "STS27":
                test_STS_27(DIR, t, c, num_representatives, index)
            elif Q_type == "STS31":
                test_STS_31(DIR, t, c, num_representatives, index)
    except KeyboardInterrupt as e:
        print("\n\nProcess interrupted")
    except Exception as e:
        print()
        print(e)
