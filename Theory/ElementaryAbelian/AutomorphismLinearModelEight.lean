module

public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Automorphisms of an elementary abelian group of order eight

For a finite elementary abelian two-group `E` of order eight,
`elementaryEight_mulAut_equiv_GL` identifies its full automorphism group with
`GL₃(𝔽₂)`. This is the standard elementary-group/vector-space correspondence,
used in Stellmacher (9.1)(c) and the small elementary-core calculations in
Section 11; the result does not require any campaign hypotheses.

The proof uses the actual `ZMod 2`-module instance on `Additive E` from
`VectorSpace`. The finite-vector-space cardinality formula forces dimension
three. Multiplicative automorphisms become additive automorphisms, whose
`ZMod 2`-linearity follows from `ZMod.map_smul`; forgetting linearity gives
the inverse, and both conversions preserve composition. Finally a basis of
size three identifies the resulting linear automorphism group with the matrix
general linear group. This equivalence is shared by order computations and
normalizer-quotient recognition.
-/

open scoped IsMulCommutative

universe u

/-- The full automorphism group of an elementary abelian group of order eight
is isomorphic to the three-dimensional general linear group over `ZMod 2`. -/
public theorem elementaryEight_mulAut_equiv_GL (E : Type u) [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hcard : Nat.card E = 8) :
    Nonempty (MulAut E ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
  classical
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive E) = 2 ^ 3 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hsize
    simpa only [Nat.card_zmod, hcard, show (2 : ℕ) ^ 3 = 8 by decide] using hsize.symm
  have hdim : Module.finrank (ZMod 2) (Additive E) = 3 :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  let autLinear : MulAut E ≃* (Additive E ≃ₗ[ZMod 2] Additive E) :=
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let basis := Module.finBasisOfFinrankEq (ZMod 2) (Additive E) hdim
  exact ⟨autLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive E)).symm.trans
      (Matrix.GeneralLinearGroup.toLin' basis).symm)⟩
