module

public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel
public import Theory.Representation.BinaryPermutation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.BigOperators.Pi

/-!
# The five singular vectors of the binary Hermitian space

The nonzero singular matrices are parametrized by `Option (Field 1)`:
the point at infinity is the first diagonal matrix unit, and the point `z`
is the Hermitian matrix with coordinates `(norm z, 1, z)`. The fixed field
has two elements, so the determinant equation shows these are all the
nonzero singular matrices.

These five vectors sum to zero and span the binary Hermitian space. For
spanning, they contain both diagonal matrix units, and subtracting the
diagonal part of the point `z` supplies every off-diagonal Hermitian matrix.
The sum relation follows from the sums of the elements and their norms in F₄.
These facts feed the equivariant deleted-permutation-module identification
in `AlternatingFive.Intertwining`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma I.1.6(3), printed p.408 (PDF p.419), the
identification of the orthogonal module for L₂(4) with the natural A₅ module.
-/

@[expose] public section

noncomputable section
open Representation.OrthogonalFourMinus.FiniteModel
namespace Representation.OrthogonalFourMinus.AlternatingFive
local instance : Algebra (ZMod 2) (fixedField 1) := ZMod.algebraOfModule 2 (fixedField 1)
local instance : Fintype (Field 1) := Fintype.ofFinite _
local instance : Fintype (fixedField 1) := Fintype.ofFinite _

lemma card_field : Fintype.card (Field 1) = 4 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 2 (by decide)

lemma fixed_eq_zero_or_one (a : fixedField 1) : a = 0 ∨ a = 1 := by
  have hc : Fintype.card (fixedField 1) = 2 := by
    simpa [Nat.card_eq_fintype_card] using card_fixedField 1
  have ha : a * (a - 1) = 0 := by
    have h := FiniteField.pow_card a
    rw [hc, pow_two] at h
    simp only [mul_sub, mul_one, h, sub_self]
  simpa only [sub_eq_zero] using mul_eq_zero.mp ha

/-- The nonzero singular Hermitian matrices. -/
def Point := {X : Space 1 // X ≠ 0 ∧ form 1 X = 0}

/-- The point at infinity and the four affine singular vectors. -/
def pointVector : Option (Field 1) → Space 1
  | none => (coordinates 1).symm ((1, 0), 0)
  | some z => (coordinates 1).symm ((FiniteModel.norm 1 z, 1), z)

lemma pointVector_ne_zero (t : Option (Field 1)) : pointVector t ≠ 0 := by
  cases t with
  | none =>
    intro h
    have := congrArg (fun X => (coordinates 1 X).1.1) h
    simp [pointVector] at this
  | some z =>
    intro h
    have := congrArg (fun X => (coordinates 1 X).1.2) h
    simp [pointVector] at this

lemma pointVector_singular (t : Option (Field 1)) : form 1 (pointVector t) = 0 := by
  cases t <;> simp only [pointVector, form_coordinates, mul_zero, mul_one,
    (norm_eq_zero_iff 1 0).mpr rfl, sub_self]

def parametrize (t : Option (Field 1)) : Point :=
  ⟨pointVector t, pointVector_ne_zero t, pointVector_singular t⟩

lemma parametrize_injective : Function.Injective parametrize := by
  intro t u h
  have h' := congrArg (fun p : Point => coordinates 1 p.val) h
  cases t with
  | none =>
    cases u with
    | none => rfl
    | some z =>
      have he := congrArg (fun v => v.1.2) h'
      simp [parametrize, pointVector] at he
  | some z =>
    cases u with
    | none =>
      have he := congrArg (fun v => v.1.2) h'
      simp [parametrize, pointVector] at he
    | some w =>
      have he := congrArg Prod.snd h'
      exact congrArg some he

lemma parametrize_surjective : Function.Surjective parametrize := by
  intro X
  let v := coordinates 1 X.val
  have hq : v.1.1 * v.1.2 - FiniteModel.norm 1 v.2 = 0 := by
    exact (form_eq_coordinates 1 X.val).symm.trans X.property.2
  rcases fixed_eq_zero_or_one v.1.2 with hb | hb
  · have hz : v.2 = 0 := by
      apply (norm_eq_zero_iff 1 _).mp
      simpa [hb] using hq
    have ha : v.1.1 = 1 := by
      rcases fixed_eq_zero_or_one v.1.1 with ha | ha
      · exfalso
        apply X.property.1
        apply (coordinates 1).injective
        exact Prod.ext (Prod.ext ha hb) hz
      · exact ha
    refine ⟨none, Subtype.ext ?_⟩
    apply (coordinates 1).injective
    change ((1, 0), 0) = v
    exact (Prod.ext (Prod.ext ha hb) hz).symm
  · have ha : v.1.1 = FiniteModel.norm 1 v.2 := by
      apply sub_eq_zero.mp
      simpa only [hb, mul_one] using hq
    refine ⟨some v.2, Subtype.ext ?_⟩
    apply (coordinates 1).injective
    change ((FiniteModel.norm 1 v.2, 1), v.2) = v
    exact Prod.ext (Prod.ext ha.symm hb.symm) rfl

def pointEquiv : Option (Field 1) ≃ Point :=
  Equiv.ofBijective parametrize ⟨parametrize_injective, parametrize_surjective⟩

lemma norm_eq_one {z : Field 1} (hz : z ≠ 0) : FiniteModel.norm 1 z = 1 :=
  (fixed_eq_zero_or_one _).resolve_left (by simpa using hz)

lemma sum_norm : ∑ z : Field 1, FiniteModel.norm 1 z = 1 := by
  classical
  have h (z : Field 1) : FiniteModel.norm 1 z = if z = 0 then 0 else 1 := by
    split_ifs with hz
    · simp [hz]
    · exact norm_eq_one hz
  simp only [h]
  simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
    Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, card_field]
  norm_num
  exact (CharP.cast_eq_iff_mod_eq (fixedField 1) 2).mpr rfl

lemma sum_field : ∑ z : Field 1, z = 0 := by
  simpa only [pow_one] using FiniteField.sum_pow_lt_card_sub_one (Field 1) 1 (by rw [card_field]; decide)

lemma sum_pointVector : ∑ t : Option (Field 1), pointVector t = 0 := by
  apply (coordinates 1).injective
  rw [map_sum, map_zero]
  simp only [Fintype.sum_option, pointVector, LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_sum, sum_norm, Prod.fst_zero]
      exact CharTwo.add_self_eq_zero _
    · simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum,
        Finset.sum_const, Finset.card_univ, card_field, nsmul_eq_mul, mul_one,
        zero_add, Prod.fst_zero, Prod.snd_zero]
      exact (CharP.cast_eq_zero_iff (fixedField 1) 2 4).mpr (by decide)
  · simp [Prod.snd_sum, sum_field]

lemma span_pointVector : Submodule.span (ZMod 2) (Set.range pointVector) = ⊤ := by
  let W := Submodule.span (ZMod 2) (Set.range pointVector)
  have hm (t) : pointVector t ∈ W := Submodule.subset_span ⟨t, rfl⟩
  have hdiag (a b : fixedField 1) : (coordinates 1).symm ((a,b),0) ∈ W := by
    rcases fixed_eq_zero_or_one a with rfl | rfl <;>
      rcases fixed_eq_zero_or_one b with rfl | rfl
    · change (coordinates 1).symm 0 ∈ W
      simpa only [map_zero] using W.zero_mem
    · simpa only [pointVector, (norm_eq_zero_iff 1 0).mpr rfl] using hm (some 0)
    · exact hm none
    · have he : (coordinates 1).symm ((1,1),0) = pointVector none + pointVector (some 0) := by
        apply (coordinates 1).injective
        simp [pointVector, (norm_eq_zero_iff 1 0).mpr rfl]
      rw [he]
      exact W.add_mem (hm none) (hm (some 0))
  apply Submodule.eq_top_iff'.mpr
  intro X
  let v := coordinates 1 X
  have he : X = (coordinates 1).symm ((v.1.1 - FiniteModel.norm 1 v.2, v.1.2 - 1),0) +
      pointVector (some v.2) := by
    apply (coordinates 1).injective
    simp [pointVector, v]
  rw [he]
  exact W.add_mem (hdiag _ _) (hm _)

end Representation.OrthogonalFourMinus.AlternatingFive
