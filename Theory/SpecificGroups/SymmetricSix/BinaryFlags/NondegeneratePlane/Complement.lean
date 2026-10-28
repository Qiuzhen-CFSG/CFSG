module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane.Stabilizer

/-!
# Complementary native binary planes

The first and last three letters give disjoint planes of dimension two in
the actual binary augmentation quotient. The ambient dimension is four,
so these planes are complementary. Their coordinate supports are disjoint,
which identifies each as the orthogonal complement of the other under the
descended dot product.

Source: Aschbacher--Smith, 13.5.6, printed p.917, the splitting attached
to the nondegenerate-plane stabilizer.
-/

@[expose] public section

open Subgroup BinaryPermutation Equiv Equiv.Perm
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane
open NaturalGeometry NaturalPairing Representation.BinaryOffender

def blockSwap : S := swap 0 3 * swap 1 4 * swap 2 5
noncomputable def secondPlane : Submodule (ZMod 2) V := move blockSwap plane

theorem secondPlane_span : secondPlane = Submodule.span (ZMod 2)
    {pairVector 3 4,pairVector 3 5} := by
  rw [secondPlane,move,plane,Submodule.map_span,Set.image_insert_eq,Set.image_singleton,
    pairVector_map,pairVector_map]
  rfl

theorem secondPlane_finrank : Module.finrank (ZMod 2) secondPlane = 2 :=
  (move_finrank blockSwap plane).trans plane_finrank

private theorem mem_move_iff (g : S) (W : Submodule (ZMod 2) V) (v : V) :
    v ∈ move g W ↔ naturalRepresentation Ω g⁻¹ v ∈ W := by
  constructor
  · rintro ⟨w,hw,rfl⟩
    rw [Representation.inv_self_apply]
    exact hw
  · intro hv
    exact ⟨_,hv,Representation.self_inv_apply _ _ _⟩

theorem pairVector_mem_secondPlane_iff {i j : Ω} (hij : i ≠ j) :
    pairVector i j ∈ secondPlane ↔ 3 ≤ i.val ∧ 3 ≤ j.val := by
  rw [secondPlane,mem_move_iff,pairVector_map,
    pairVector_mem_plane_iff_small (blockSwap⁻¹.injective.ne hij)]
  have h : ∀ i : Ω, (blockSwap⁻¹ i).val < 3 ↔ 3 ≤ i.val := by decide
  rw [h,h]

theorem plane_secondPlane_disjoint : Disjoint plane secondPlane := by
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  intro v hv
  rcases vector_cases v with rfl | ⟨d,rfl⟩
  · exact Submodule.zero_mem _
  · have h1 := (pairVector_mem_plane_iff_small (ne_of_lt d.property)).mp hv.1
    have h2 := (pairVector_mem_secondPlane_iff (ne_of_lt d.property)).mp hv.2
    omega

theorem plane_secondPlane_isCompl : IsCompl plane secondPlane := by
  apply (Submodule.isCompl_iff_disjoint plane secondPlane ?_).mpr plane_secondPlane_disjoint
  rw [plane_finrank,secondPlane_finrank,finrank_natural_even Ω (by decide)]
  decide

theorem plane_card : Nat.card plane = 4 := by
  let _ : Fintype plane := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K := ZMod 2),ZMod.card,plane_finrank]
  decide

theorem secondPlane_card : Nat.card secondPlane = 4 := by
  let _ : Fintype secondPlane := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K := ZMod 2),ZMod.card,secondPlane_finrank]
  decide

private theorem pair_orthogonal (i j : Ω) (hi : 3 ≤ i.val) (hj : 3 ≤ j.val) :
    pairVector i j ∈ form.orthogonal plane := by
  intro v hv
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hv
  have h1 : form (pairVector 0 1) (pairVector i j) = 0 := by
    rw [pair_form]
    revert i j hi hj
    decide
  have h2 : form (pairVector 0 2) (pairVector i j) = 0 := by
    clear h1
    rw [pair_form]
    revert i j hi hj
    decide
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,h1,h2,smul_zero,add_zero]

theorem secondPlane_eq_orthogonal : secondPlane = form.orthogonal plane := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [secondPlane_span]
    apply Submodule.span_le.mpr
    rintro v (rfl | rfl)
    · exact pair_orthogonal 3 4 (by decide) (by decide)
    · exact pair_orthogonal 3 5 (by decide) (by decide)
  · rw [secondPlane_finrank,LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
      finrank_natural_even Ω (by decide),plane_finrank]
    decide

theorem plane_eq_orthogonal_second : plane = form.orthogonal secondPlane := by
  rw [secondPlane_eq_orthogonal,
    LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl]

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane
