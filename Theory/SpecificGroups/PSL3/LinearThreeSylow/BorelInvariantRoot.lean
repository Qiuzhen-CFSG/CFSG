module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.RootScalars
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Roots in Borel-invariant unipotent subgroups

A nontrivial subgroup of a Sylow two-subgroup, invariant under its whole
normalizer, meets the Sylow center nontrivially. The Borel is transitive on
the nonidentity elements of that center, so the subgroup contains the
whole center. Sylow conjugacy identifies this center with a conjugate of
the projective highest-root group in the original matrix coordinates.

Source: the root containment used in Aschbacher--Smith, proof of 15.3.38,
printed p.1136. The scalar transitivity is proved in `RootScalars`.
-/

public section
open Subgroup Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3.LinearThree.RootScalars
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.BorelStructure

variable (F : Type*) [Field F] [Finite F]

/-- Borel invariance forces a nonzero unipotent subgroup to contain the Sylow center. -/
theorem sylow_center_le_of_borel_invariant {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (P : Sylow 2 PSL(3,F))
    (W : Subgroup PSL(3,F)) (hWP : W ≤ (P : Subgroup PSL(3,F)))
    (hBW : normalizer (P : Set PSL(3,F)) ≤ normalizer (W : Set PSL(3,F)))
    (hW : W ≠ ⊥) : (center P).map (P : Subgroup PSL(3,F)).subtype ≤ W := by
  have hPW : (P : Subgroup PSL(3,F)) ≤ normalizer (W : Set PSL(3,F)) :=
    (P : Subgroup PSL(3,F)).le_normalizer.trans hBW
  let : (W.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hWP).mpr hPW
  let : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW
  let : Nontrivial (W.subgroupOf P) := (subgroupOfEquivOfLe hWP).toEquiv.nontrivial
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  obtain ⟨z, hz, hzC⟩ := exists_nontrivial_center_mem_normal (p := 2) (W.subgroupOf P)
  have hzG : ((z : P) : PSL(3,F)) ≠ 1 := by
    intro he
    exact hz (Subtype.ext (Subtype.ext he))
  have hzC' : ((z : P) : PSL(3,F)) ∈ (center P).map (P : Subgroup PSL(3,F)).subtype :=
    mem_map_of_mem _ hzC
  intro w hw
  by_cases hw1 : w = 1
  · exact hw1 ▸ W.one_mem
  obtain ⟨b, hb, he⟩ := sylow_center_nonidentity_transitive F hn hF (MulEquiv.refl _) P
    _ hzC' hzG w hw hw1
  exact he ▸ (mem_normalizer_iff.mp (hBW hb) _).mp z.property

/-- The contained root is an inner conjugate in the prescribed projective group. -/
theorem exists_root_le_of_borel_invariant {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (P : Sylow 2 PSL(3,F))
    (W : Subgroup PSL(3,F)) (hWP : W ≤ (P : Subgroup PSL(3,F)))
    (hBW : normalizer (P : Set PSL(3,F)) ≤ normalizer (W : Set PSL(3,F)))
    (hW : W ≠ ⊥) : ∃ g : PSL(3,F),
      (projectiveCenter F).map (MulAut.conj g).toMonoidHom ≤ W := by
  obtain ⟨g, hP, _⟩ := Matrix.PSL3.CartanActions.BorelQuotient.sylow_normalizer_conjugate F hn hF P
  refine ⟨g, ?_⟩
  have hZ : (projectiveCenter F).map (MulAut.conj g).toMonoidHom =
      (center P).map (P : Subgroup PSL(3,F)).subtype := by
    rw [projectiveCenter_eq_mapped_center, map_subgroup_center_eq _ (MulAut.conj g).injective, hP]
  rw [hZ]
  exact sylow_center_le_of_borel_invariant F hn hF P W hWP hBW hW

end Matrix.PSL3.LinearThree.BorelStructure
