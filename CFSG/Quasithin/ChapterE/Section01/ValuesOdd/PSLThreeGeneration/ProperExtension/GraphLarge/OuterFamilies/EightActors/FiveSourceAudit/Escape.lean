module
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups

/-!
# Recovering an actual escaping family member

A solvable overgroup of the ambient Sylow lies in the generation target by
E.1.13 and E.1.8. If it does not normalize the original weak closure, some
actual rank-one E-member escapes that normalizer. The actor remains in the
original conjugation-invariant family, including when it is an outer eight-group.

The model construction of the solvable overgroup and its movement remain
separate inputs; the theorem does not assume E-membership or an E-generation
conclusion. Source: Aschbacher--Smith E.1.8, E.1.13 and E.1.14(7), pp.210--214.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit
variable {G : Type*} [Group G] [Finite G]

/-- A solvable Sylow overgroup which moves the original weak closure supplies
an actual E-member for an actual member of the original family. -/
theorem exists_escape_of_solvable_overgroup (T : Sylow 2 G)
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (H : Subgroup G) [Group.IsSolvable H] (hTH : (T : Subgroup G) ≤ H)
    (hmove : ¬ H ≤ normalizer (weakClosure (T : Subgroup G) Ω : Set G)) :
    ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ ∃ K : Subgroup G,
      IsEMemberAt 1 (T : Subgroup G) A K ∧
      ¬ K ≤ normalizer (weakClosure (T : Subgroup G) Ω : Set G) := by
  classical
  by_contra! h
  apply hmove
  have he : eFamilySubgroup 1 (T : Subgroup G) Ω ≤
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) := by
    apply iSup_le
    intro A
    apply sSup_le
    intro K hK
    exact h A.1 A.2.1 A.2.2 K hK
  exact (ChiefOrbit.solvable_overgroup_le_generationTarget (by decide) T H hTH hΩ).trans
    (sup_le he le_rfl)
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit
