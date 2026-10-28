module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Planes
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Representative
/-!
# Generator criteria for the pure Held actors

A permutation preserving the finite generated subgroup in one direction
normalizes it. Signed words in the four literal two-generators remain in
the candidate. These lemmas assemble the concrete certificates for the
lower action witnesses of GLS3 Table 5.3p and quasithin pp.509–511.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
open Subgroup

def twoGenerator (i : Bool) (k : Fin 4) : He := evalLocalWord i (twoWord i 0 k)

def evalTwo (i : Bool) (w : List (Fin 4 × ℤ)) : He :=
  (w.map fun t => twoGenerator i t.1 ^ t.2).prod

theorem evalTwo_mem (i : Bool) (w : List (Fin 4 × ℤ)) :
    evalTwo i w ∈ candidateTwo i 0 := by
  induction w with
  | nil => exact (candidateTwo i 0).one_mem
  | cons t w hw =>
    exact (candidateTwo i 0).mul_mem
      ((candidateTwo i 0).zpow_mem (subset_closure ⟨t.1, rfl⟩) _) hw

theorem representation_evalTwo (i : Bool) (w : List (Fin 4 × ℤ)) :
    representation (evalTwo i w) =
      (w.map fun t => representation (twoGenerator i t.1) ^ t.2).prod := by
  simp only [evalTwo, map_list_prod, List.map_map, Function.comp_def, map_zpow]

theorem normalizes_generated {ι : Type*} (g : ι → He) (n : Equiv.Perm (Fin 2058))
    (h : ∀ k, n * representation (g k) * n⁻¹ ∈ (closure (Set.range g)).map representation) :
    n ∈ normalizer ((closure (Set.range g)).map representation : Set (Equiv.Perm (Fin 2058))) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rw [map_map, MonoidHom.map_closure, closure_le]
    rintro _ ⟨y, ⟨k, rfl⟩, rfl⟩
    exact h k
  · exact (Nat.card_congr ((MulAut.conj n).subgroupMap
      ((closure (Set.range g)).map representation)).toEquiv).le
end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
