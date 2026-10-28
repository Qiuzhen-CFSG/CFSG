module

public import Theory.Representation.Mathieu.M22James.Model
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.Fusion
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension.Matrix
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer
public import Theory.ElementaryAbelian.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The genuine `3.M₂₂.2` twelve-dimensional model

The degree-twelve alternative in Aschbacher--Smith, G.11.2(13), uses the
quasisimple triple cover from A.3.5 and its involutory outer extension.  This
file uses the certified ATLAS matrices for that cover, together with the
proved identification of the cover's binary module and its matrix normalizer.
The central scalar has order three.  An inner involution has displacement rank
four; an outer involution inverts the scalar and has displacement rank six.
Consequently no involution in the concrete extension has displacement rank two.

The cover is the perfect derived subgroup of the matrix group; it is not the
split product `M₂₂ × C₃`.  The outer involution is retained as an actual matrix
and its conjugation action on the scalar is used in the rank calculation.
Source: Aschbacher--Smith, G.7.3(2)(iii), G.11.2(13), and the proof of
6.2.19, printed pp.348, 364, 691 (PDF pp.359, 375, 708).
-/

@[expose] public section

open Subgroup
open scoped Matrix
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open Sporadic.Mathieu

namespace Representation.RankTwo.TripleCover

noncomputable def binaryAction :
    Representation (ZMod 2) actionGroup M22TripleCover.BinarySpace :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    ((Units.coeHom Matrix12).comp actionGroup.subtype)

private theorem cover_conj_scalar (d : M22TripleCover) :
    coverInclusion d * scalarElement * (coverInclusion d)⁻¹ = scalarElement := by
  change coverInclusion d * coverInclusion M22TripleCover.scalar *
    (coverInclusion d)⁻¹ = coverInclusion M22TripleCover.scalar
  have hd : d * M22TripleCover.scalar * d⁻¹ = M22TripleCover.scalar := by
    rw [Subgroup.mem_center_iff.mp M22TripleCover.scalar_mem_center d,
      mul_assoc, mul_inv_cancel, mul_one]
  exact congrArg coverInclusion hd

private theorem triple_outer_conj_scalar (g : actionGroup)
    (hg : g ∉ coverSubgroup) :
    g * scalarElement * g⁻¹ = scalarElement⁻¹ := by
  have hm : g * outerElement ∈ coverSubgroup :=
    (Subgroup.mul_mem_iff_of_index_two coverSubgroup_index).mpr
      (iff_of_false hg outerElement_not_mem_cover)
  rw [← coverInclusion_range] at hm
  obtain ⟨d, hd⟩ := hm
  have he : g = coverInclusion d * outerElement := by
    rw [hd, mul_assoc, ← pow_two, outerElement_sq, mul_one]
  rw [he, mul_inv_rev]
  calc
    coverInclusion d * outerElement * scalarElement *
        (outerElement⁻¹ * (coverInclusion d)⁻¹) =
      coverInclusion d * (outerElement * scalarElement * outerElement⁻¹) *
        (coverInclusion d)⁻¹ := by simp only [mul_assoc]
    _ = coverInclusion d * scalarElement⁻¹ * (coverInclusion d)⁻¹ := by
      rw [outerElement_conj_scalar]
    _ = scalarElement⁻¹ := by
      change (MulAut.conj (coverInclusion d)) scalarElement⁻¹ = scalarElement⁻¹
      rw [map_inv]
      exact congrArg Inv.inv (cover_conj_scalar d)

local notation "ρ₀" => M22TripleCover.binaryRepresentation

noncomputable def innerRepresentative : M22TripleCover :=
  ⟨coreB, coreB_mem_derivedGroup⟩

theorem innerRepresentative_sq : innerRepresentative ^ 2 = 1 := by
  apply Subtype.ext
  change (unitD ^ 2) ^ 2 = 1
  rw [← pow_mul]
  exact unitD_pow_four

theorem innerRepresentative_ne_one : innerRepresentative ≠ 1 := by
  intro h
  have hm := congrArg (fun x : M22TripleCover =>
    ((x : Matrix12ˣ) : Matrix12)) h
  change (coreB : Matrix12) = 1 at hm
  rw [coe_coreB] at hm
  have hentry := congrArg (fun A : Matrix12 => A 0 0) hm
  norm_num [matrixB, fromRows] at hentry

private def reducedRows : Matrix (Fin 4) (Fin 12) (ZMod 2) :=
  fun i j => if (![17, 10, 800, 2112] : Fin 4 → ℕ) i |>.testBit j.val then 1 else 0

private def leftFactor : Matrix (Fin 12) (Fin 4) (ZMod 2) :=
  fun i j => if (![1, 0, 3, 0, 1, 6, 8, 6, 14, 8, 11, 8] : Fin 12 → ℕ) i |>.testBit j.val then 1 else 0

private def rowOperations : Matrix (Fin 4) (Fin 12) (ZMod 2) :=
  fun i j => if (![1, 5, 37, 64] : Fin 4 → ℕ) i |>.testBit j.val then 1 else 0

theorem representative_matrix_rank : (matrixB - 1).rank = 4 := by
  have hfac : matrixB - 1 = leftFactor * reducedRows := by decide +kernel
  have hrow : reducedRows = rowOperations * (matrixB - 1) := by decide +kernel
  have hpiv : reducedRows.submatrix id (![0, 1, 5, 6] : Fin 4 → Fin 12) = 1 := by
    decide +kernel
  have hr : reducedRows.rank = 4 := by
    apply le_antisymm (Matrix.rank_le_height _)
    have h := Matrix.rank_submatrix_le reducedRows id
      (![0, 1, 5, 6] : Fin 4 → Fin 12)
    rw [hpiv, Matrix.rank_one] at h
    exact h
  apply le_antisymm
  · calc
      (matrixB - 1).rank = (leftFactor * reducedRows).rank := congrArg Matrix.rank hfac
      _ ≤ reducedRows.rank := Matrix.rank_mul_le_right _ _
      _ = 4 := hr
  · rw [← hr, hrow]
    exact Matrix.rank_mul_le_right _ _

private theorem finrank_range_eq_matrix_rank
    {k : Type*} [Field k] {n : ℕ}
    (f : Module.End k (Fin n → k)) (A : Matrix (Fin n) (Fin n) k)
    (h : f = Matrix.toLin' A) : Module.finrank k (LinearMap.range f) = A.rank := by
  subst f
  rfl

theorem innerRepresentative_rank :
    Module.finrank (ZMod 2) (movedSpace ρ₀ innerRepresentative) = 4 := by
  have h : ρ₀ innerRepresentative - 1 = Matrix.toLin' (matrixB - 1) := by
    change Matrix.toLinAlgEquiv' (coreB : Matrix12) - 1 =
      Matrix.toLinAlgEquiv' (matrixB - 1)
    rw [coe_coreB, map_sub, map_one]
  exact (finrank_range_eq_matrix_rank _ _ h).trans representative_matrix_rank

private theorem finrank_movedSpace_conj
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) {x y : G} (h : IsConj x y) :
    Module.finrank k (movedSpace ρ x) = Module.finrank k (movedSpace ρ y) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  let f : V ≃ₗ[k] V :=
    LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)
  apply finrank_movedSpace_transport ρ ρ (MulAut.conj g) f
  intro a z
  change ρ g (ρ a z) = ρ (g * a * g⁻¹) (ρ g z)
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

noncomputable def projection : M22TripleCover →* M22 :=
  M22TripleCover.centralQuotientEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (center M22TripleCover))

private theorem projection_surjective : Function.Surjective projection :=
  M22TripleCover.centralQuotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective _)

private theorem projection_ker : projection.ker = center M22TripleCover := by
  rw [projection, MonoidHom.ker_comp_of_injective _ _
    M22TripleCover.centralQuotientEquiv.injective, QuotientGroup.ker_mk']

private theorem central_cube {z : M22TripleCover}
    (hz : z ∈ center M22TripleCover) : z ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := (⟨z, hz⟩ : center M22TripleCover))
  rw [M22TripleCover.center_card] at h
  exact congrArg Subtype.val h

private theorem square_one_lift_unique {x y : M22TripleCover}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (he : projection x = projection y) : x = y := by
  have hz : x * y⁻¹ ∈ center M22TripleCover := by
    rw [← projection_ker, MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  have hc : Commute (x * y⁻¹) y :=
    (Subgroup.mem_center_iff.mp hz y).symm
  have hz2 : (x * y⁻¹) ^ 2 = 1 := by
    have hxy : x = (x * y⁻¹) * y := (inv_mul_cancel_right x y).symm
    have h := congrArg (fun a : M22TripleCover => a ^ 2) hxy
    rw [hx, hc.mul_pow, hy, mul_one] at h
    exact h.symm
  have hz3 := central_cube hz
  have hz1 : x * y⁻¹ = 1 := by
    simpa only [pow_succ, hz2, one_mul] using hz3
  exact mul_inv_eq_one.mp hz1

private theorem projection_involution_order {x : M22TripleCover}
    (hx : x ^ 2 = 1) (hne : x ≠ 1) : orderOf (projection x) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, hx, map_one]
  · intro h
    apply hne
    exact square_one_lift_unique hx (one_pow 2)
      (h.trans (map_one projection).symm)

private theorem cover_involutions_isConj {x y : M22TripleCover}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    IsConj x y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (m22_involutions_isConj _ _
    (projection_involution_order hx hx1) (projection_involution_order hy hy1))
  obtain ⟨g, rfl⟩ := projection_surjective c
  apply isConj_iff.mpr
  refine ⟨g, square_one_lift_unique ?_ hy ?_⟩
  · rw [conj_pow, hx, mul_one, mul_inv_cancel]
  · simpa only [map_mul, map_inv] using hc

theorem inner_involution_rank (x : M22TripleCover) (hx : x ^ 2 = 1)
    (hne : x ≠ 1) :
    Module.finrank (ZMod 2) (movedSpace ρ₀ x) = 4 := by
  apply (finrank_movedSpace_conj ρ₀
    (cover_involutions_isConj hx innerRepresentative_sq hne
      innerRepresentative_ne_one)).trans
  exact innerRepresentative_rank

theorem outer_involution_rank (x : actionGroup) (hx : x ^ 2 = 1)
    (hout : x ∉ coverSubgroup) :
    Module.finrank (ZMod 2) (movedSpace binaryAction x) = 6 := by
  have hs : scalarElement⁻¹ = scalarElement ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']
    simpa only [scalarElement_order] using pow_orderOf_eq_one scalarElement
  have hxs : x * scalarElement = scalarElement ^ 2 * x := by
    have h := congrArg (fun a : actionGroup => a * x)
      (triple_outer_conj_scalar x hout)
    simpa only [hs, mul_assoc, inv_mul_cancel, mul_one] using h
  have hs3 : scalarElement ^ 3 = 1 := by
    simpa only [scalarElement_order] using pow_orderOf_eq_one scalarElement
  have h := finrank_range_inverting_cubic (binaryAction scalarElement)
    (binaryAction x) (by rw [← map_pow, hs3, map_one])
    (fun v hv => (M22TripleCover.scalar_fixed_iff v).mp hv)
    (by rw [← map_mul, ← pow_two, hx, map_one])
    (by rw [← map_mul, hxs, map_mul, map_pow])
  rw [M22TripleCover.binarySpace_finrank] at h
  change 2 * Module.finrank (ZMod 2) (movedSpace binaryAction x) = 12 at h
  omega

theorem concrete_involution_rank_cases (x : actionGroup) (hx : x ^ 2 = 1)
    (hne : x ≠ 1) :
    Module.finrank (ZMod 2) (movedSpace binaryAction x) = 4 ∨
      Module.finrank (ZMod 2) (movedSpace binaryAction x) = 6 := by
  by_cases hin : x ∈ coverSubgroup
  · rw [← coverInclusion_range] at hin
    obtain ⟨y, rfl⟩ := hin
    left
    apply inner_involution_rank
    · apply Subgroup.inclusion_injective derivedGroup_le_actionGroup
      rw [map_pow, map_one]
      exact hx
    · intro hy
      apply hne
      rw [hy, map_one]
  · exact Or.inr (outer_involution_rank x hx hin)

theorem concrete_no_rank_two (x : actionGroup) (hx : x ^ 2 = 1) :
    Module.finrank (ZMod 2) (movedSpace binaryAction x) ≠ 2 := by
  by_cases he : x = 1
  · subst x
    rw [movedSpace, map_one, sub_self, LinearMap.range_zero, finrank_bot]
    decide
  · rcases concrete_involution_rank_cases x hx he with h | h <;> omega

theorem elementary_no_rank_two (X : Subgroup actionGroup)
    [IsElementaryAbelian 2 X] (x : actionGroup) (hx : x ∈ X) :
    Module.finrank (ZMod 2) (movedSpace binaryAction x) ≠ 2 :=
  concrete_no_rank_two x (elemPow_eq_one_of_isElementaryAbelian x hx)

end Representation.RankTwo.TripleCover
