module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.RootDuality.Negation
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.WeylDuality

/-!
# Exceptional twisting of highest-vector equations

The exceptional root formula transports the actual rank-one normalizer and
positive-coroot words. Hence a positive-root fixed vector remains fixed after
pullback, and its simple-coroot exponents change by `exceptionalWeight`.
These are action identities, independent of any representation classification.

Source: GLS3, Remark 2.8.4, with the positive-coroot convention fixed in
`ExceptionalTensor.BasicWeights`.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
variable (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ)

include hψ

/-- Transport of the actual rank-one normalizer word. -/
lemma exceptional_nElement (r : F4Chevalley.Root) (t : Fˣ) :
    ψ (algebraicNElement r t) =
      algebraicNElement (exceptionalRootPermutation r) (exceptionalParameter r t) := by
  let := typeF4RootPairing.indexNeg
  simp only [algebraicNElement, map_mul]
  rw [hψ, hψ, exceptionalRootPermutation_neg, exceptionalParameter_neg]
  by_cases hr : IsLongRoot r
  · simp only [exceptionalParameter_of_long hr]
  · simp only [exceptionalParameter_of_short hr, Units.val_pow_eq_pow_val,
      CharTwo.neg_eq, inv_pow]

/-- Transport of the actual coroot word, including the short-root square. -/
lemma exceptional_corootElement (r : F4Chevalley.Root) (t : Fˣ) :
    ψ (algebraicCorootElement r t) =
      algebraicCorootElement (exceptionalRootPermutation r) (exceptionalParameter r t) := by
  simp only [algebraicCorootElement, map_mul, map_inv, exceptional_nElement ψ hψ]
  have h1 : exceptionalParameter r (1 : Fˣ) = 1 := by
    by_cases hr : IsLongRoot r
    · rw [exceptionalParameter_of_long hr]
    · rw [exceptionalParameter_of_short hr, one_pow]
  rw [h1]

omit [CharP F 2] in
/-- Pullback by the exceptional endomorphism preserves positive-root fixed
vectors, since its root permutation preserves the positive system. -/
lemma exceptional_positive_fixed {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F (PointGroup F) V) (v : V)
    (hv : ∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → ∀ t : F,
      ρ (algebraicRootElement r t) v = v) :
    ∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → ∀ t : F,
      ρ (ψ (algebraicRootElement r t)) v = v := by
  intro r hr t
  rw [hψ]
  exact hv _ ((WordRelations.exceptionalRootPermutation_isPos r).mpr hr) _

/-- The exceptional root formula gives the actual transformation of the four
simple-coroot eigenvalues, in the positive-coroot convention of BasicWeights. -/
lemma exceptional_coroot_eigenvector {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F (PointGroup F) V) (a : Weight) (v : V)
    (hv : ∀ (i : Fin 4) (t : Fˣ),
      ρ (algebraicCorootElement (typeF4SimpleRootIndex i) t) v = ((t : F) ^ a i) • v)
    (i : Fin 4) (t : Fˣ) :
    ρ (ψ (algebraicCorootElement (typeF4SimpleRootIndex i) t)) v =
      ((t : F) ^ exceptionalWeight a i) • v := by
  rw [exceptional_corootElement ψ hψ, exceptionalRootPermutation_simple, hv]
  have hlong (j : Fin 4) : IsLongRoot (typeF4SimpleRootIndex j) ↔ j.val < 2 :=
    typeF4SimpleRootIndex_mem_pair_iff j
  have hparam (j : Fin 4) : exceptionalParameter (typeF4SimpleRootIndex j) t =
      if j.val < 2 then t else t ^ 2 := by
    by_cases hj : j.val < 2
    · rw [if_pos hj]
      exact exceptionalParameter_of_long ((hlong j).mpr hj) t
    · rw [if_neg hj]
      exact exceptionalParameter_of_short (fun h => hj ((hlong j).mp h)) t
  rw [hparam]
  fin_cases i <;> simp [Fin.revPerm, Fin.rev, exceptionalWeight, pow_mul]

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
