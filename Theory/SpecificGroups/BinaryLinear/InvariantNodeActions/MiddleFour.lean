module
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions

/-! The middle maximal parabolic of a binary four-dimensional Sylow flag
is invariant under every automorphism preserving that Sylow. Inner
automorphisms preserve all cuts; graph-times-inner automorphisms reverse
the three cuts and therefore preserve the middle one. This reuses the
actual full-flag and graph-duality theorems, with no finite enumeration.
Source: Aschbacher--Smith 2.5.2, printed p.551. -/
public section
open Subgroup
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic

theorem exists_sylow_invariant_middle (T : Sylow 2 (LinearGroup 4)) :
    ∃ W : Submodule (ZMod 2) (Space 4), Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup (LinearGroup 4)) ≤ parabolic W ∧
      ∀ α : MulAut (LinearGroup 4), (T : Subgroup (LinearGroup 4)).map α.toMonoidHom = T →
        (parabolic W).map α.toMonoidHom = parabolic W := by
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer (m := 3) T
  let W := cutSpace b (1 : Fin 3)
  have hp : parabolic W = cutStabilizer b {1} := by
    ext g
    simp only [mem_cutStabilizer, Set.mem_singleton_iff, forall_eq]
    rfl
  refine ⟨W,cutSpace_finrank b 1,?_,?_⟩
  · rw [hb,hp]
    exact (cutStabilizer_le_iff _ _ _).mpr (Set.subset_univ _)
  · intro α hα
    obtain ⟨g,rfl | rfl⟩ := OuterCyclic.inner_graph (Or.inl rfl) α
    · rw [hb] at hα
      rw [hp]
      exact inner_fixes_cutStabilizer b g hα {1}
    · rw [hb] at hα
      rw [graph_inner_map_parabolic]
      have hh := graph_inner_cutSpace_of_fullFlag b g hα (1 : Fin 3)
      exact congrArg parabolic hh

end BinaryLinear.InvariantNodeActions
