#!/usr/bin/env python3

from functools import reduce

# WARNING: This implementation may contain bugs and has not been audited. 
# It is only for educational purposes. DO NOT use it in production.

from utils import log_2, pow_2
from curve import Fr as Field, G1Point, G2Point
from merlin.merlin_transcript import MerlinTranscript
from mle2 import MLEPolynomial

# WARNING: 
#   1. For demonstration, we deliberately use an insecure random number 
#      generator, random.Random. To generate secure randomness, use 
#      the standard library `secrets` instead.
#        
#      See more here: https://docs.python.org/3/library/secrets.html
#
#   2. Challenges are only 1 byte long for simplicity, which is not secure.

import random

# Implementation of Zeromorph-PCS from Section 6.1 in [KT23]:
# 
# - [KT23] https://eprint.iacr.org/2023/917 
# -  Kohrita, Tohru, and Patrick Towa. 
# - "Zeromorph: Zero-knowledge multilinear-evaluation proofs from homomorphic univariate commitments." 


from unipoly import UniPolynomial
from kzg10_non_hiding import Commitment, KZG10_PCS

Zeromorph_PCS_Argument = tuple[list[Commitment], Commitment, Commitment, dict]

CnstPoly = UniPolynomial.const

class Zeromorph_PCS:

    def __init__(self, kzg_pcs: KZG10_PCS, debug: int = 0):
        """
        Args:
            pcs: the PedersenCommitment instance to use for the proof
        """
        self.kzg_pcs = kzg_pcs
        self.rng = random.Random("ipa-pcs")
        self.debug = debug

    def commit(self, polynomial: MLEPolynomial) -> Commitment:
        """
        Commit to a vector of coefficients.
        """

        evals = polynomial.evals
        cm = self.kzg_pcs.commit(UniPolynomial(evals))

        return cm

    @staticmethod
    def periodic_poly(dim, degree):
        """
        Compute the periodic polynomial Phi(X^d)

            Phi_k(X)   = 1 + X   + X^2  + X^3  + ... + X^(2^k-1)
            Phi_k(X^d) = 1 + X^d + X^2d + X^3d + ... + X^(2^(k-1))d

        Args:
            dim: dimension of the space of size 2^k
            degree: degree of X^d

        Returns:
            list: the coefficients of Phi(X^d)
        """
        n = pow_2(dim)
        coeffs = [0] * (n * degree)
        for i in range(n):
            coeffs[i * degree] = 1
        return UniPolynomial(coeffs)

    def prove_evaluation(self, 
                    f_cm: Commitment, 
                    f_mle: MLEPolynomial, 
                    us: list[Field], 
                    transcript: MerlinTranscript) -> tuple[Field, Zeromorph_PCS_Argument]:
        """
        Generate evaluation proof for f_mle(us) = v

        Args:
            f_cm: commitment to the polynomial f_mle
            f_mle: the MLE polynomial to prove the evaluation of
            us: the evaluation point
            tr: the transcript to use for the proof

        Returns: (v, arg)
            v: the evaluation of f_mle at us
            arg: the proof argument
        """
        n = len(us)
        N = pow_2(n)
        assert n == f_mle.num_var, f"Number of variables mismatch, {n} != {f_mle.num_var}"
        us = us
        evals = f_mle.evals.copy()
        if self.debug > 1:
            print(f"P> f={f_mle}, point={us}")
        
        transcript.absorb(b"commitment", f_cm)
        transcript.absorb(b"point", us)

        # v = f_mle.evaluate(us)

        # > Round 1.

        # Decompose f_mle into quotient polynomials and remainder
        quotients, rem = f_mle.decompose_by_div(us)
        if self.debug > 0:
            print(f"P> check evaluation of f_mle")
            assert rem == f_mle.evaluate(us), "Evaluation does not match"
            print(f"P> check evaluation of f_mle passed")
        v = rem
        transcript.absorb(b"evaluation", v)

        f_uni = UniPolynomial(evals)

        # Commit to q_i(X), quotient polynomials 
        q_cm_vec = []
        q_uni_vec = []
        for i in range(n):
            qi_poly = UniPolynomial(quotients[i].evals)
            qi_cm = self.kzg_pcs.commit(qi_poly)
            q_cm_vec.append(qi_cm)
            q_uni_vec.append(qi_poly)
            transcript.absorb(b"qi_cm", qi_cm)
        
        # > Round 2.

        beta = transcript.squeeze(Field, b"beta", 4)

        if self.debug > 0:
            print(f"P> beta={beta}")

        q_hat_uni = UniPolynomial([0])
        coeffs = [0] * N
        coeffs.append(1)
        beta_power = 1
        for i in range(n):
            x_deg_2_to_i_uni = UniPolynomial(coeffs[pow_2(i):])
            q_hat_uni += (x_deg_2_to_i_uni * q_uni_vec[i]) * UniPolynomial([Field(beta_power)])
            beta_power *= beta
        
        q_hat_cm = self.kzg_pcs.commit(q_hat_uni)
        transcript.absorb(b"q_hat_cm", q_hat_cm)

        # > Round 3.

        zeta = transcript.squeeze(Field, b"zeta", 4)
        if self.debug > 0:
            print(f"P> zeta={zeta}")

        # compute r(X) = f(X) - v * phi_n(zeta) - ∑_i (c_i * qi(X))
        #
        #   r_ζ(X) = f(X) - v * 𝚽_n(ζ) 
        #            - ∑_i ( ζ^{2^i} * 𝚽_{n-i-1}(ζ^{2^{i+1}}) - u_i * 𝚽_{n-i}(ζ^{2^i}) ) * q_i(X)
        #          = f(X) - v_𝚽 - ∑_i c_i * q_i(X)
        
        phi_uni_at_zeta = self.periodic_poly(n, 1).evaluate(zeta)
        if self.debug > 1:
            print(f"P> f_uni={f_uni}, v={v}, phi_uni_at_zeta={phi_uni_at_zeta}")

        r_uni = f_uni - UniPolynomial([phi_uni_at_zeta * v])
        for i in range(n):
            c_i = zeta**(pow_2(i)) * self.periodic_poly(n-i-1, pow_2(i+1)).evaluate(zeta) \
                    - us[i] * self.periodic_poly(n-i, pow_2(i)).evaluate(zeta)
            r_uni -= UniPolynomial([c_i]) * q_uni_vec[i]

        if self.debug > 1:
            print("P> r_uni=", r_uni)
        if self.debug > 0:
            print(f"P> check r_uni(zeta) == 0")
            assert r_uni.evaluate(zeta) == 0, f"Evaluation does not match, {r_uni.evaluate(zeta)}!=0"
            print(f"P> check r_uni(zeta) == 0 passed")

        # compute s(X) = q_hat(X) - ∑_i ( beta^{i} * X^{2^n - 2^i} * q_i(X) ) 
        #
        #    s_ζ(X) = q_hat(X) - ∑_i ( beta^{i} * ζ^{2^n - 2^i} * q_i(X) )

        s_uni = q_hat_uni
        for i in range(n):
            e_i = (beta**i) * (zeta**(pow_2(n) - pow_2(i)))
            s_uni -= UniPolynomial([e_i]) * q_uni_vec[i]

        if self.debug > 1:
            print(f"P> s_uni={s_uni}")
        if self.debug > 0:
            print(f"P> check s_uni(zeta) == 0")
            assert s_uni.evaluate(zeta) == 0, f"Evaluation does not match, {s_uni.evaluate(zeta)}!=0"
            print(f"P> check s_uni(zeta) == 0 passed")
        
        # > Round 4.

        alpha = transcript.squeeze(Field, b"alpha", 4)
        if self.debug > 0:
            print(f"P> alpha={alpha}")

        a_uni = s_uni + r_uni * UniPolynomial([alpha])

        if self.debug > 0:
            print(f"P> check a_uni(zeta) == 0")
            assert a_uni.evaluate(zeta) == 0, f"Evaluation does not match, {a_uni.evaluate(zeta)}!=0"
            print(f"P> check a_uni(zeta) == 0 passed")

        a_uni_cm = self.kzg_pcs.commit(a_uni)
        a_uni_at_zeta, arg = self.kzg_pcs.prove_eval_and_degree(a_uni_cm, a_uni, zeta, pow_2(n))
        if self.debug > 0:
            print(f"P> check a_uni_at_zeta == 0")
            assert a_uni_at_zeta == 0, f"Evaluation does not match, {a_uni_at_zeta}!=0"
            print(f"P> check a_uni_at_zeta == 0 passed")

        # if self.debug > 1:
        #     v_cm = self.kzg_pcs.commit(UniPolynomial([phi_uni_at_zeta * v]))
        #     r_cm = f_cm - v_cm 
        #     print("P> f_cm - v_cm=", r_cm)
        #     for i in range(k):
        #         c_i = zeta**(pow_2(i)) * self.periodic_poly(k-i-1, pow_2(i+1)).evaluate(zeta) \
        #                    - us[i] * self.periodic_poly(k-i, pow_2(i)).evaluate(zeta)
        #         r_cm = r_cm - q_cm_vec[i].scalar_mul(c_i)

        #     print(f"P> r_cm={r_cm}, r({zeta})={r_uni.evaluate(zeta)}")
        #     checked = self.kzg_pcs.verify_eval_and_degree(r_cm, zeta, 0, pow_2(k), arg)
        #     print("P> 👀  r(zeta) == 0 ✅" if checked else "👀  r(zeta) == 0 ❌")

        return v, (q_cm_vec, q_hat_cm, arg)

    def verify_evaluation(self, 
                    f_cm: Commitment, 
                    us: list[Field], 
                    v: Field,
                    arg: dict,
                    transcript: MerlinTranscript) -> bool:
        """
        Verify the evaluation of a polynomial at a given point.

            arg: `f(us) = v`, 
            
                where f is an MLE polynomial, us is a log-n sized evaluation point.

        Args:
            f_cm: the commitment to the polynomial
            us: the evaluation point
            v: the evaluation value
            arg: the argument generated by the prover
            tr: the proof transcript

        Returns:
            bool: True if the argument is valid, False otherwise
        """
        n = len(us)
        print(f"V> f_cm={f_cm}")
        print(f"V> point={us}")
        print(f"V> evaluation={v}")
        transcript.absorb(b"commitment", f_cm)
        transcript.absorb(b"point", us)

        # > Round 1.

        transcript.absorb(b"evaluation", v)

        q_cm_vec, q_hat_cm, eval_deg_arg = arg

        for i in range(n):
            qi_cm = q_cm_vec[i]
            print(f"V> q_cm={qi_cm}")
            transcript.absorb(b"qi_cm", qi_cm)

        # > Round 2.

        beta = transcript.squeeze(Field, b"beta", 4)
        if self.debug > 0:
            print(f"V> beta={beta}")

        print(f"V> q_hat_cm={q_hat_cm}")
        transcript.absorb(b"q_hat_cm", q_hat_cm)

        # > Round 3.

        zeta = transcript.squeeze(Field, b"zeta", 4)
        if self.debug > 0:
            print(f"V> zeta={zeta}")

        # compute r(X) = f(X) - v * phi_n(zeta) - ∑_i (c_i * qi(X))
        #
        #   r_ζ(X) = f(X) - v * 𝚽_n(ζ) 
        #            - ∑_i ( ζ^{2^i} * 𝚽_{n-i-1}(ζ^{2^{i+1}}) - us_i * 𝚽_{n-i}(ζ^{2^i}) ) * q_i(X)
        #          = f(X) - v_𝚽 - ∑_i c_i * q_i(X)
        
        phi_uni_at_zeta_mul_v = self.periodic_poly(n, 1).evaluate(zeta) * v
        if self.debug > 1:
            print(f"V> phi_uni_at_zeta_mul_v={phi_uni_at_zeta_mul_v}")

        r_cm = f_cm - self.kzg_pcs.commit(UniPolynomial([phi_uni_at_zeta_mul_v]))
        for i in range(n):
            c_i = zeta**(pow_2(i)) * self.periodic_poly(n-i-1, pow_2(i+1)).evaluate(zeta) \
                    - us[i] * self.periodic_poly(n-i, pow_2(i)).evaluate(zeta)
            r_cm -= q_cm_vec[i].scalar_mul(c_i)

        # compute h(X) = q_hat(X) - ∑_i ( beta^{i} * X^{2^k - 2^i} * q_i(X) ) 
        #
        #    h_ζ(X) = q_hat(X) - ∑_i ( beta^{i} * ζ^{2^k - 2^i} * q_i(X) )

        s_cm = q_hat_cm
        for i in range(n):
            e_i = (beta**i) * (zeta**(pow_2(n) - pow_2(i)))
            s_cm -=  q_cm_vec[i].scalar_mul(e_i)

        if self.debug > 1:
            print(f"V> s_cm={s_cm}")

        # > Round 4.

        alpha = transcript.squeeze(Field, b"alpha", 4)
        if self.debug > 0:
            print(f"V> alpha={alpha}")

        a_cm = s_cm + r_cm.scalar_mul(alpha)

        # if debug > 0:
        #     assert a_uni.evaluate(zeta) == 0, f"Evaluation does not match, {a_uni.evaluate(zeta)}!=0"
        #     print(f"V> 👀 a(zeta={zeta}) == 0 ✅")

        checked = self.kzg_pcs.verify_eval_and_degree(a_cm, zeta, 0, pow_2(n), eval_deg_arg)
        if self.debug > 0:
            print("V> 👀  a(zeta) == 0 ✅" if checked else "👀  a(zeta) == 0 ❌")
        
        return checked

def test_zeromorph_uni_pcs():

    # # initialize the PedersenCommitment and the IPA_PCS
    kzg = KZG10_PCS(G1Point, G2Point, Field, 24)
    kzg.debug = True

    zeromorph_pcs = Zeromorph_PCS(kzg, debug = 2)

    tr = MerlinTranscript(b"test-zeromorph-pcs")

    # A simple instance f(x) = y
    coeffs = [Field(2), Field(3), Field(4), Field(5), Field(6), Field(7), Field(8), Field(9), \
             Field(10), Field(11), Field(12), Field(13), Field(14), Field(15), Field(16), Field(17)]
    us = [Field(4), Field(2), Field(3), Field(0)]
    eqs = MLEPolynomial.eqs_over_hypercube(us)

    y = sum([a * b for a, b in zip(coeffs, eqs)])
    f = MLEPolynomial(coeffs, 4)
    assert f.evaluate(us) == y

    f_cm = zeromorph_pcs.commit(f)

    v, arg = zeromorph_pcs.prove_evaluation(f_cm, f, us, tr.fork(b""))
    assert v == y
    zeromorph_pcs.verify_evaluation(f_cm, us, v, arg, tr.fork(b""))

if __name__ == "__main__":
    test_zeromorph_uni_pcs()