module
public import Theory.Representation.BinaryPermutation.SevenTriangle
public import Mathlib.Logic.Equiv.Fintype
/-!
# Simultaneous seven-letter point and triangle-plane coordinates

A nonzero point of a pair plane is one of its three edges. Rebase at that
edge and extend the resulting ordered triple to a permutation. The same
permutation sends the point to e₅,₆ and the plane to its span with e₅,₇.

Source: Aschbacher–Smith, 13.7.6(3b), printed p.939.
-/
@[expose] public section
namespace BinaryPermutation.SevenTriangle.Marking
open SevenParabolic Module
private theorem pair_comm (i j : Fin 7) : pair i j = pair j i := by
  apply Subtype.ext
  exact add_comm _ _
private theorem pair_sum (i j k : Fin 7) : pair i j + pair i k = pair j k := by
  apply Subtype.ext
  change (Pi.single i 1 + Pi.single j 1) + (Pi.single i 1 + Pi.single k 1) = Pi.single j 1 + Pi.single k 1
  have h : (Pi.single i 1 : Fin 7 → ZMod 2) + Pi.single i 1 = 0 := ZModModule.add_self _
  linear_combination h

private theorem span_pair_add {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] (a b : E) :
    Submodule.span (ZMod 2) {a,b} = Submodule.span (ZMod 2) {a+b,a} := by
  have ha : a ∈ Submodule.span (ZMod 2) {a+b,a} := Submodule.subset_span (by simp)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl)
    · exact ha
    · exact Submodule.mem_span_pair.mpr ⟨1,1,by
        simp only [one_smul,add_right_comm,ZModModule.add_self,zero_add]⟩
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl)
    · exact Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    · exact Submodule.subset_span (by simp)

/-- Rebase the triangle at the actual specified nonzero point. -/
theorem plane_basis_through (U : Submodule (ZMod 2) Space) (hd : finrank (ZMod 2) U = 2)
    (hweight : ∀ w ∈ U, w ≠ 0 → weight w = 2)
    (u : Space) (hu : u ∈ U) (hun : u ≠ 0) :
    ∃ i j k : Fin 7, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ u = pair i j ∧
      U = Submodule.span (ZMod 2) {pair i j,pair i k} := by
  obtain ⟨i,j,k,hij,hik,hjk,hU⟩ := plane_basis U hd hweight
  obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp (hU ▸ hu)
  have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hc a with rfl | rfl <;> rcases hc b with rfl | rfl
  · simp only [zero_smul,add_zero] at hab
    exact (hun hab.symm).elim
  · simp only [zero_smul,one_smul,zero_add] at hab
    refine ⟨i,k,j,hik,hij,hjk.symm,hab.symm,?_⟩
    rw [hU,Set.pair_comm]
  · simp only [one_smul,zero_smul,add_zero] at hab
    exact ⟨i,j,k,hij,hik,hjk,hab.symm,hU⟩
  · simp only [one_smul,pair_sum] at hab
    refine ⟨j,k,i,hjk,hij.symm,hik.symm,hab.symm,?_⟩
    rw [hU,span_pair_add,pair_sum,pair_comm j i]

/-- Every nonzero vector of a triangle plane is a pair vector. -/
theorem triangle_plane_weights (i j k : Fin 7) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∀ w ∈ Submodule.span (ZMod 2) {pair i j,pair i k}, w ≠ 0 → weight w = 2 := by
  intro w hw hn
  obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp hw
  have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hc a with rfl | rfl <;> rcases hc b with rfl | rfl
  · simp only [zero_smul,add_zero] at hab
    exact (hn hab.symm).elim
  · simp only [zero_smul,one_smul,zero_add] at hab
    rw [←hab]
    exact pair_weight i k hik
  · simp only [one_smul,zero_smul,add_zero] at hab
    rw [←hab]
    exact pair_weight i j hij
  · simp only [one_smul,pair_sum] at hab
    rw [←hab]
    exact pair_weight j k hjk

private theorem pair_permute (g : Equiv.Perm (Fin 7)) (i j : Fin 7) :
    action g (pair i j) = pair (g i) (g j) := by
  apply Subtype.ext
  funext a
  simp only [action,coreRepresentation_apply,representation_apply,pair,Pi.add_apply,Pi.single_apply]
  simp only [g.symm_apply_eq]

/-- One permutation gives the exact printed point and seed-plane coordinates. -/
theorem canonical_flag (U : Submodule (ZMod 2) Space) (hd : finrank (ZMod 2) U = 2)
    (hweight : ∀ w ∈ U, w ≠ 0 → weight w = 2)
    (u : Space) (hu : u ∈ U) (hun : u ≠ 0) :
    ∃ g : Equiv.Perm (Fin 7), action g u = pair56 ∧
      U.map (action g) = Submodule.span (ZMod 2) {pair56,pair57} := by
  obtain ⟨i,j,k,hij,hik,hjk,rfl,hU⟩ := plane_basis_through U hd hweight u hu hun
  have hinj : Function.Injective (![i,j,k] : Fin 3 → Fin 7) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  obtain ⟨g,hg⟩ := Equiv.Perm.exists_extending_pair
    (![i,j,k] : Fin 3 → Fin 7) (![4,5,6] : Fin 3 → Fin 7) hinj (by decide)
  have hi : g i = 4 := hg 0
  have hj : g j = 5 := hg 1
  have hk : g k = 6 := hg 2
  have h56 : pair (4 : Fin 7) 5 = pair56 := by apply Subtype.ext; decide
  have h57 : pair (4 : Fin 7) 6 = pair57 := by apply Subtype.ext; decide
  refine ⟨g,by rw [pair_permute,hi,hj,h56],?_⟩
  rw [hU,Submodule.map_span,Set.image_pair,pair_permute,pair_permute,hi,hj,hk,h56,h57]
end BinaryPermutation.SevenTriangle.Marking
