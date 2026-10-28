/-
The semidirect-product perfectness and centralizer arguments are adapted from
Gerald Höhn's Atlas/GroupTheory/SemidirectPerfect.lean and AffineNormal.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
The adapted portions are covered by the ATLAS Research and Attribution License
1.0; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: specialize to CFSG's natural SL₂ action, use Lean/mathlib 4.33.0 and
project module boundaries, and connect to the intrinsic two-core and F*(G).
-/
module

public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.SpecificGroups.SL2.Affine.Core
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Perfectness and generalized Fitting structure of the special affine group

For a finite field F with at least four elements, F² ⋊ SL₂(F) is perfect.
Choose a nonzero scalar a with a² ≠ 1. The corresponding diagonal matrix
has invertible difference from the identity on the plane, so every translation
is an action commutator. The embedded SL₂ is perfect by the same scalar choice.

Faithfulness of the natural action makes the translation plane its own
centralizer. In characteristic two this plane is O₂, and the theorem on
self-centralizing prime cores gives F*(F² ⋊ SL₂(F)) = O₂(F² ⋊ SL₂(F)).
This second assertion also holds over F₂. Both results are transported along
actual group isomorphisms, for use by the PSL₃ point and line local groups.

These are the intrinsic structural inputs for Aschbacher–Smith, C.1.7
(printed p.123) and F.1.12(I)(1),(II) (printed pp.262–264). No shortness,
block property or residual equality is assumed.
-/

public section

open Matrix
open scoped MatrixGroups commutatorElement
namespace Matrix.SL2
variable (F : Type*) [Field F]

/-- The natural affine group over a finite field is finite. -/
instance affine_finite [Finite F] : Finite (Affine F) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

private theorem exists_good_scalar [Finite F] (hcard : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  by_contra h
  push Not at h
  have hsubset : (Finset.univ : Finset F) ⊆ {0, 1, -1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · rcases sq_eq_one_iff.mp (h a ha) with h1 | hneg
      · simp [h1]
      · simp [hneg]
  have hc := Finset.card_le_card hsubset
  have hthree : ({0, 1, -1} : Finset F).card ≤ 3 := by
    exact (Finset.card_insert_le _ _).trans (by
      have := Finset.card_insert_le (1 : F) {-1}
      simpa using Nat.add_le_add_right this 1)
  have hle : Nat.card F ≤ 3 := by
    simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using hc.trans hthree
  omega

private theorem naturalAction_differences {a : F} (ha : a ≠ 0) (ha1 : a ≠ 1)
    (v : Multiplicative (Fin 2 → F)) :
    ∃ g : SL(2, F), ∃ w : Multiplicative (Fin 2 → F),
      naturalAction F g w * w⁻¹ = v := by
  refine ⟨SpecialLinearGroup.diag2 a ha,
    Multiplicative.ofAdd ![Multiplicative.toAdd v 0 / (a - 1),
      Multiplicative.toAdd v 1 / (a⁻¹ - 1)], ?_⟩
  have hai : a⁻¹ ≠ 1 := by simpa using ha1
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_inv, naturalAction_apply]
  simp only [toAdd_ofAdd, ← sub_eq_add_neg]
  rw [SpecialLinearGroup.diag2_coe']
  ext i
  fin_cases i <;> simp <;>
    field_simp [sub_ne_zero.mpr ha1, sub_ne_zero.mpr hai]

private theorem semidirect_perfect_of_differences
    {N P : Type*} [Group N] [Group P] [Group.IsPerfect P]
    (φ : P →* MulAut N)
    (hdiff : ∀ n : N, ∃ p : P, ∃ w : N, φ p w * w⁻¹ = n) :
    Group.IsPerfect (N ⋊[φ] P) := by
  constructor
  apply top_unique
  intro x _
  have hl : ∀ n : N, (SemidirectProduct.inl n : N ⋊[φ] P) ∈
      commutator (N ⋊[φ] P) := by
    intro n
    obtain ⟨p, w, rfl⟩ := hdiff n
    have he : (SemidirectProduct.inl (φ p w * w⁻¹) : N ⋊[φ] P) =
        ⁅(SemidirectProduct.inr p : N ⋊[φ] P), SemidirectProduct.inl w⁆ := by
      rw [map_mul, map_inv, SemidirectProduct.inl_aut]
      simp only [commutatorElement_def, map_inv]
    rw [he]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hr : ∀ p : P, (SemidirectProduct.inr p : N ⋊[φ] P) ∈
      commutator (N ⋊[φ] P) := by
    intro p
    have hp := Group.IsPerfect.mem_commutator (g := p)
    have hm := Subgroup.mem_map_of_mem (SemidirectProduct.inr : P →* N ⋊[φ] P) hp
    rw [map_commutator_eq] at hm
    exact (Subgroup.commutator_mono le_top le_top) hm
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  exact (commutator (N ⋊[φ] P)).mul_mem (hl x.left) (hr x.right)

/-- The affine special linear group is perfect when the field has at least four elements. -/
theorem affine_isPerfect [Finite F] (hcard : 4 ≤ Nat.card F) :
    Group.IsPerfect (Affine F) := by
  obtain ⟨a, ha, hasq⟩ := exists_good_scalar F hcard
  let : Group.IsPerfect SL(2, F) := ⟨commutator_eq_top ha hasq⟩
  have ha1 : a ≠ 1 := by rintro rfl; simp at hasq
  exact semidirect_perfect_of_differences (naturalAction F)
    (naturalAction_differences F ha ha1)

/-- An affine element centralizes every translation exactly when it is a translation. -/
theorem centralizer_translations_eq :
    Subgroup.centralizer (translations F : Set (Affine F)) = translations F := by
  rw [← range_inl_eq_translations]
  ext x
  constructor
  · intro hx
    have hr : naturalAction F x.right = 1 := by
      ext u : 1
      have h := congrArg SemidirectProduct.left
        (Subgroup.mem_centralizer_iff.mp hx (SemidirectProduct.inl u) ⟨u, rfl⟩)
      apply mul_left_cancel (a := x.left)
      simpa only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, map_one, MulAut.one_apply, mul_comm u] using h.symm
    have he : x.right = 1 := naturalAction_injective F (hr.trans (map_one _).symm)
    exact ⟨x.left, by ext <;> simp [he]⟩
  · rintro ⟨u, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨v, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]

/-- In characteristic two, the full generalized Fitting subgroup is the translation two-core. -/
theorem affine_generalizedFitting_eq_twoCore [Finite F] [CharP F 2] :
    Theory.GroupTheory.generalizedFitting (Affine F) = pCore 2 (Affine F) := by
  apply Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing
  rw [affine_twoCore_eq, centralizer_translations_eq]

/-- Transfer affine perfectness through an actual multiplicative equivalence. -/
theorem isPerfect_of_equiv_affine [Finite F] (hcard : 4 ≤ Nat.card F)
    {L : Type*} [Group L] (e : L ≃* Affine F) : Group.IsPerfect L := by
  let := affine_isPerfect F hcard
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- The intrinsic generalized Fitting identity in any group isomorphic to the affine model. -/
theorem generalizedFitting_eq_twoCore_of_equiv_affine [Finite F] [CharP F 2]
    {L : Type*} [Group L] (e : L ≃* Affine F) :
    Theory.GroupTheory.generalizedFitting L = pCore 2 L := by
  let : Finite L := Finite.of_equiv (Affine F) e.symm.toEquiv
  apply Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing
  apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  calc
    (Subgroup.centralizer (pCore 2 L : Set L)).map e.toMonoidHom ≤
        Subgroup.centralizer ((pCore 2 L).map e.toMonoidHom : Set (Affine F)) :=
      Subgroup.map_centralizer_le_centralizer_image _ _
    _ ≤ (pCore 2 L).map e.toMonoidHom := by
      rw [pCore_map_iso, affine_twoCore_eq, centralizer_translations_eq]
end Matrix.SL2
