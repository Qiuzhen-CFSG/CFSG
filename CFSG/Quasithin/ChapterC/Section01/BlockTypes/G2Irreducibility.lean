module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ModuleIrreducibility
public import Theory.Representation.G2NaturalBinary

/-!
# Irreducibility of the intrinsic natural G₂ block module

The actual derived binary G₂ action is transitive on nonzero natural vectors.
Thus its invariant additive subgroups are trivial or full. Literal block-module
coordinates transport this statement to the normal-subgroup interval in C.1.7.
No elementary-core or short-group hypothesis is used here.

Source: Aschbacher–Smith C.1.7 and C.1.30, printed pp.123,135.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
open Atlas.G2.Natural

/-- A natural G₂ central quotient supplies the irreducibility clause of shortness. -/
theorem BlockModuleModel.g2_irreducible {L : Type*} [Group L]
    (model : BlockModuleModel L g2TwoNaturalAction) : BlockModuleIrreducible L := by
  let : Nontrivial (Space (ZMod 2)) := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank (ZMod 2) (Space (ZMod 2)) by rw [finrank_space]; decide)
  apply model.irreducible
  intro W hW
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  have hn : ¬ ∀ x ∈ W, x = 1 := fun h => hb ((Subgroup.eq_bot_iff_forall W).mpr h)
  push Not at hn
  obtain ⟨v, hv, hv1⟩ := hn
  apply top_unique
  intro w _
  by_cases hw : w = 1
  · exact hw ▸ W.one_mem
  have hv0 : v.toAdd ≠ 0 := fun h => hv1 (Multiplicative.toAdd.injective h)
  have hw0 : w.toAdd ≠ 0 := fun h => hw (Multiplicative.toAdd.injective h)
  obtain ⟨g, hg⟩ := Binary.natural_transitive hv0 hw0
  have he : g2TwoNaturalAction g v = w := Multiplicative.toAdd.injective hg
  exact he ▸ hW g v hv
end CFSG.Quasithin.ChapterC
