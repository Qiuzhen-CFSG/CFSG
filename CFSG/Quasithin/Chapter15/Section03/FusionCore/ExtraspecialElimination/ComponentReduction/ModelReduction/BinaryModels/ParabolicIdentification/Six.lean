module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Local
public import Theory.SpecificGroups.SymmetricSix.Parabolics

/-!
# The six-letter parabolic position

Every index-three overgroup of a Sylow two-subgroup of A₆ is a conjugate
of the duad or syntheme stabilizer restricted from S₆. The exhaustive
standard-Borel theorem gives containment, and index multiplicativity
upgrades it to equality. Sylow conjugacy and the supplied component
isomorphism transport this equality without changing the marking.

These are actual permutation stabilizers, including their intersection
with A₆. Their comparison with the symplectic matrix action is a separate
geometric transport step.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.1144, clause 15.3.49(l); the concrete six-letter quadrangle in I.5,
printed pp.419–422.
-/

@[expose] public section

open Subgroup CFSG.Quasithin.Chapter1

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification

namespace Six
open Theory.SpecificGroups.SymmetricSix

theorem index_three_over_borel (P : Subgroup A6) (hB : a6Borel ≤ P)
    (hi : a6Borel.relIndex P = 3) :
    P = a6DuadStabilizer ∨ P = a6SynthemeStabilizer := by
  have hidx : P.index = 15 := by
    have h := relIndex_mul_index hB
    rw [hi, a6Borel_index] at h
    omega
  have hn : P ≠ ⊤ := by
    intro h
    simp [h] at hidx
  rcases a6_overgroup_borel P hB hn with hd | hs
  · left
    apply le_antisymm hd
    apply relIndex_eq_one.mp
    have h := relIndex_mul_index hd
    rw [a6DuadStabilizer_index, hidx] at h
    omega
  · right
    apply le_antisymm hs
    apply relIndex_eq_one.mp
    have h := relIndex_mul_index hs
    rw [a6SynthemeStabilizer_index, hidx] at h
    omega

theorem index_three_over_sylow (T : Sylow 2 A6) (P : Subgroup A6)
    (hTP : (T : Subgroup A6) ≤ P) (hi : (T : Subgroup A6).relIndex P = 3) :
    ∃ g : A6, P = (MulAut.conj g).mapSubgroup a6DuadStabilizer ∨
      P = (MulAut.conj g).mapSubgroup a6SynthemeStabilizer := by
  obtain ⟨g, hg, _⟩ := a6_coatoms_over_sylow T
  let e := (MulAut.conj g).mapSubgroup
  have hb : a6Borel ≤ e.symm P := by
    have h := e.symm.monotone hTP
    rwa [← hg, e.symm_apply_apply] at h
  have hidx : a6Borel.relIndex (e.symm P) = 3 := by
    have h := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      a6Borel (e.symm P) (MulAut.conj g).injective
    change (e a6Borel).relIndex (e (e.symm P)) = _ at h
    rw [hg, e.apply_symm_apply] at h
    exact h.symm.trans hi
  refine ⟨g, ?_⟩
  rcases index_three_over_borel (e.symm P) hb hidx with h | h
  · exact Or.inl ((e.apply_symm_apply P).symm.trans (congrArg e h))
  · exact Or.inr ((e.apply_symm_apply P).symm.trans (congrArg e h))

theorem ambient_position {K : Type*} [Group K] [Finite K]
    (L S P : Subgroup K) (e : L ≃* A6) (hs : IsSylowIn 2 S L)
    (hSP : S ≤ P) (hPL : P ≤ L) (hi : S.relIndex P = 3) :
    ∃ g : A6,
      (P.subgroupOf L).map e.toMonoidHom = (MulAut.conj g).mapSubgroup a6DuadStabilizer ∨
      (P.subgroupOf L).map e.toMonoidHom =
        (MulAut.conj g).mapSubgroup a6SynthemeStabilizer := by
  obtain ⟨Q, _, hQ, hiQ⟩ := model_inputs L S P e hs hSP hPL hi
  exact index_three_over_sylow Q _ hQ hiQ

end Six
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification
