p = 0b100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011100010101010000100100111011011000011111101011001101110011010000101000000011001001110001000000000000000000000000000000001
q = 0b100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011100010101010000100100111011010010110001010000110110010011000010000101100101011111101010000000000000000000000000000000001
# assert(is_prime(p))
# assert(is_prime(q))
Fp = GF(p)
Fq = GF(q)
ep = EllipticCurve(Fp, [0, 5])
eq = EllipticCurve(Fq, [0, 5])
# assert(ep.order() == q)
# assert(eq.order() == p)
zetap = Fp(0b1010100001000010000010101101010110101111010010111110010010100100110111110101111001001000101000110111011111000001111011001101001111000100000011111101100100011100110111010010000011010001001101000010110011000101010111011001110100100000100001100100111001000)
zetaq = Fq(0b11011011000110011011010011101000011110000001001001101001011000100001111010110110001011010111111111100101110011000111111111111001101001110011111000110111100111001000001110010100101110110000010100001110010100110000101011110100010100100011111010010011111101)
# assert(zetap^3 == Fp(1))
# assert(zetaq^3 == Fq(1))
# a = ep.random_element()
# a_endo1 = ep(a[0] * int(zetap), a[1])
# a_endo2 = a * int(zetaq)
# assert(a_endo1 == a_endo2)
# a = eq.random_element()
# a_endo1 = eq(a[0] * int(zetaq), a[1])
# a_endo2 = a * int(zetap)
# assert(a_endo1 == a_endo2)
Sp = 33
Sq = 34

def fourhex(a):
    s = ""
    s = s + "0x" + (a % (2^64)).hex()
    a = a >> 64
    for i in range(0, 3):
        s = s + ", 0x" + (a % (2^64)).hex()
        a = a >> 64                  
    return s

def printparams(name, prime, field, zeta, S):
    print(("%s: " % name) + "%s" % fourhex(p))
    R = 2^256 % prime
    R2 = 2^(256*2) % prime
    R3 = 2^(256*3) % prime
    print(("%s (R): " % name) + "%s" % fourhex(R))
    print(("%s (R2): " % name) + "%s" % fourhex(R2))
    print(("%s (R3): " % name) + "%s" % fourhex(R3))
    print(("%s (S): " % name) + "%s" % S)
    t = (prime - 1) // (2^S)
    generator = field(5)
    assert(generator.multiplicative_order() == (prime - 1))
    assert((generator^t).multiplicative_order() == 2^S)
    root_of_unity = generator^((prime - 1) // (2^S))
    print(("%s (ROOT_OF_UNITY): " % name) + "%s" % fourhex(int(root_of_unity)))
    print(("%s (NUM_BITS): " % name) + "%s" % (len(bin(prime)) - 2))
    print(("%s (CAPACITY): " % name) + "%s" % (len(bin(prime)) - 3))
    print(("%s (RESCUE_ALPHA): " % name) + "%s" % (fourhex(5)))
    invalpha = Mod(5, prime - 1)^(-1)
    print(("%s (RESCUE_INVALPHA): " % name) + "%s" % (fourhex(int(invalpha))))
    assert((generator^5)^(invalpha) == generator)
    print(("%s ((t - 1) // 2): " % name) + "%s" % (fourhex((t - 1) // 2)))
    print(("%s (prime - 2): " % name) + "%s" % (fourhex(prime - 2)))
    print(("%s (ZETA): " % name) + "%s" % (fourhex(int(zeta))))


printparams("Fp", p, Fp, zetap, Sp)
printparams("Fq", q, Fq, zetaq, Sq)
