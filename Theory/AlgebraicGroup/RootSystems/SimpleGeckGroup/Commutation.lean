module

public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup
public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations

/-!
# Commuting simple Geck curves

Distinct simple roots give commuting positive-negative Geck operators. When their
Cartan entry is zero, the positive-positive and negative-negative operators also
commute: in the adjoint sl₂ representation, the other operator is a primitive
vector of weight zero, so the opposite operator annihilates it.

The characteristic-zero matrix identities descend to the integral Geck matrices.
Their factorial identities then imply that all divided powers commute, by
cancelling nonzero factorials over ℤ. Only afterwards do we specialize to the
coefficient ring and sum the cubic curves. This proves the group identities over
arbitrary commutative rings, including characteristics two and three.

Sources: Geck (2017), Lemmas 3.3 and 3.5, as formalized in Mathlib's
`GeckConstruction.Relations`; GLS3 §§2.4 and 2.6, especially the commuting
subsystem factors in Proposition 2.6.2(a) (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
namespace RootPairing.SimpleGeckGroup
open IntegralGeckConstruction
attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [P.IsCrystallographic] [P.IsReduced]
  [P.IsIrreducible] {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- A primitive vector of weight zero generates the trivial sl₂ module. -/
private theorem commute_geck_e_e (i j : b.support) (hij : i ≠ j)
    (hc : b.cartanMatrix j i = 0) :
    Commute (GeckConstruction.e i) (GeckConstruction.e j) := by
  open GeckConstruction in
  have hp : (isSl2Triple i).symm.HasPrimitiveVectorWith (e j) (0 : K) :=
    { ne_zero := (isSl2Triple j).e_ne_zero
      lie_h := by simp only [neg_lie, lie_h_e, hc, zero_smul, neg_zero]
      lie_e := by rw [← lie_skew, lie_e_f_ne hij.symm, neg_zero] }
  have hh := hp.pow_toEnd_f_eq_zero_of_eq_nat (n := 0) (by simp)
  change _ * _ = _ * _
  simpa only [zero_add, pow_one, LieModule.toEnd_apply_apply, Ring.lie_def,
    sub_eq_zero] using hh

private theorem commute_geck_f_f (i j : b.support) (hij : i ≠ j)
    (hc : b.cartanMatrix j i = 0) :
    Commute (GeckConstruction.f i) (GeckConstruction.f j) := by
  open GeckConstruction in
  have hp : (isSl2Triple i).HasPrimitiveVectorWith (f j) (0 : K) :=
    { ne_zero := (isSl2Triple j).f_ne_zero
      lie_h := by simp only [lie_h_f, hc, neg_zero, zero_smul]
      lie_e := lie_e_f_ne hij }
  have hh := hp.pow_toEnd_f_eq_zero_of_eq_nat (n := 0) (by simp)
  change _ * _ = _ * _
  simpa only [zero_add, pow_one, LieModule.toEnd_apply_apply, Ring.lie_def,
    sub_eq_zero] using hh

omit [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] [DecidableEq ι] in
private theorem commute_integral_of_map {A B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ}
    (h : Commute (A.map (algebraMap ℤ K)) (B.map (algebraMap ℤ K))) : Commute A B := by
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ K)
  simpa only [Matrix.map_mul] using h.eq

private theorem commute_eMatrix_eMatrix (i j : b.support) (hij : i ≠ j)
    (hc : b.cartanMatrix j i = 0) : Commute (eMatrix i) (eMatrix j) := by
  apply commute_integral_of_map (K := K)
  simpa only [map_eMatrix] using commute_geck_e_e i j hij hc

private theorem commute_eMatrix_fMatrix (i j : b.support) (hij : i ≠ j) :
    Commute (eMatrix i) (fMatrix j) := by
  apply commute_integral_of_map (K := K)
  rw [map_eMatrix, map_fMatrix]
  change _ * _ = _ * _
  simpa only [Ring.lie_def, sub_eq_zero] using GeckConstruction.lie_e_f_ne hij

private theorem commute_fMatrix_fMatrix (i j : b.support) (hij : i ≠ j)
    (hc : b.cartanMatrix j i = 0) : Commute (fMatrix i) (fMatrix j) := by
  apply commute_integral_of_map (K := K)
  simpa only [map_fMatrix] using commute_geck_f_f i j hij hc

omit [P.IsIrreducible] in
private theorem simpleFamily_factorial (i : Bool × b.support) (a : ℕ) :
    (simpleFamily.dividedPower i 1) ^ a = a.factorial • simpleFamily.dividedPower i a := by
  rcases i with ⟨s, i⟩
  cases s
  · simpa only [simpleFamily, fDividedPower_one] using fMatrix_pow_eq_factorial_smul i a
  · exact eMatrix_pow_eq_factorial_smul i a

omit [P.IsIrreducible] in
/-- Cancel the two nonzero factorials entrywise over ℤ, before specialization. -/
private theorem commute_dividedPowers (i j : Bool × b.support)
    (h : Commute (simpleFamily.dividedPower i 1) (simpleFamily.dividedPower j 1))
    (a c : ℕ) : Commute (simpleFamily.dividedPower i a) (simpleFamily.dividedPower j c) := by
  have hh := (h.pow_pow a c).eq
  rw [simpleFamily_factorial, simpleFamily_factorial] at hh
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul] at hh
  rw [Nat.mul_comm c.factorial a.factorial] at hh
  ext x y
  exact nsmul_right_injective (Nat.mul_ne_zero (Nat.factorial_ne_zero a)
    (Nat.factorial_ne_zero c)) (congrFun₂ hh x y)

omit [P.IsIrreducible] in
private theorem commute_simple_curves {S : Type*} [CommRing S] (i j : Bool × b.support)
    (h : Commute (simpleFamily.dividedPower i 1) (simpleFamily.dividedPower j 1))
    (t u : S) : Commute (simpleFamily.curve i t) (simpleFamily.curve j u) := by
  have hc (a c : ℕ) :
      Commute (simpleFamily.coefficient (S := S) i a)
        (simpleFamily.coefficient j c) :=
    (commute_dividedPowers i j h a c).map (Int.castRingHom S).mapMatrix
  have hs (a c : ℕ) (x y : S) :
      Commute (x • simpleFamily.coefficient i a) (y • simpleFamily.coefficient j c) :=
    ((hc a c).smul_left x).smul_right y
  unfold IntegralCubicFamily.curve
  apply Commute.add_left
  · apply Commute.add_left
    · apply Commute.add_left
      · exact Commute.one_left _
      · exact (((Commute.one_right _).add_right (hs 1 1 t u)).add_right
          (hs 1 2 t (u ^ 2))).add_right (hs 1 3 t (u ^ 3))
    · exact (((Commute.one_right _).add_right (hs 2 1 (t ^ 2) u)).add_right
        (hs 2 2 (t ^ 2) (u ^ 2))).add_right (hs 2 3 (t ^ 2) (u ^ 3))
  · exact (((Commute.one_right _).add_right (hs 3 1 (t ^ 3) u)).add_right
      (hs 3 2 (t ^ 3) (u ^ 2))).add_right (hs 3 3 (t ^ 3) (u ^ 3))

variable {S : Type*} [CommRing S]

/-- Positive curves for orthogonal simple roots commute over every coefficient ring. -/
theorem commute_positive_positive_of_cartan_eq_zero (i j : b.support)
    (hij : i ≠ j) (hc : b.cartanMatrix j i = 0) (t u : S) :
    Commute (positive i t) (positive j u) := by
  apply Subtype.ext
  apply Units.ext
  exact (commute_simple_curves (true, i) (true, j)
    (commute_eMatrix_eMatrix i j hij hc) t u).eq

/-- Opposite-sign curves for distinct simple roots commute over every coefficient ring. -/
theorem commute_positive_negative (i j : b.support) (hij : i ≠ j) (t u : S) :
    Commute (positive i t) (negative j u) := by
  apply Subtype.ext
  apply Units.ext
  exact (commute_simple_curves (true, i) (false, j)
    (by simpa only [simpleFamily, eDividedPower_one, fDividedPower_one] using
      commute_eMatrix_fMatrix i j hij) t u).eq

/-- Negative curves for orthogonal simple roots commute over every coefficient ring. -/
theorem commute_negative_negative_of_cartan_eq_zero (i j : b.support)
    (hij : i ≠ j) (hc : b.cartanMatrix j i = 0) (t u : S) :
    Commute (negative i t) (negative j u) := by
  apply Subtype.ext
  apply Units.ext
  exact (commute_simple_curves (false, i) (false, j)
    (by simpa only [simpleFamily, fDividedPower_one] using
      commute_fMatrix_fMatrix i j hij hc) t u).eq

end RootPairing.SimpleGeckGroup
