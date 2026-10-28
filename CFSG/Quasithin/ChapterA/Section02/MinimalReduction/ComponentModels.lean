module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.ProperSections
public import Theory.Quasithin.ComponentRanks
public import Theory.GroupTheory.GeneralizedFitting.LayerImages

/-!
# The source C-list input for distinct components

Two distinct components of the original quasithin group each have all
ordinary odd-prime ranks at most two. Applying the genuine proper-section
induction to a component and then its actual central quotient supplies
strong quasithinness and the full C model predicate for that quotient.
This closes the initial component-list step of A.2.12; the subsequent
odd-center covering sieve and shared-center product analysis remain separate.

Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G : Type u} [Group G] [Finite G]

theorem component_centralQuotient_models_of_ne
    (ih : TheoremsOnProperSections K G) (hG : IsQuasithin G) (hK : IsKGroup K G)
    {C D : Subgroup G} (hC : IsComponent G C) (hD : IsComponent G D)
    (hne : C ≠ D) :
    IsStronglyQuasithin C ∧ IsStronglyQuasithin (C ⧸ center C) ∧
      IsTheoremCModel (C ⧸ center C) := by
  let := hC.2
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  have hcproper : C ≠ ⊤ := by
    intro ht
    exact hne (hD.eq_of_le hC (ht ▸ le_top)).symm
  have hsqt : IsStronglyQuasithin C := fun p hp ho =>
    hC.primeRank_le_two_of_ne hD hne hG p hp ho
  have hsemiC : componentLayer C = ⊤ := by
    apply top_unique
    apply le_sSup
    exact ⟨(inferInstance : (⊤ : Subgroup C).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup C) ≃* C).symm⟩
  have hsemi : IsSemisimple (C ⧸ center C) :=
    componentLayer_eq_top_of_surjective (QuotientGroup.mk' (center C))
      (QuotientGroup.mk'_surjective _) hsemiC
  have hsec : IsSectionOf (C ⧸ center C) C :=
    IsSectionOf.of_surjective _ (QuotientGroup.mk'_surjective (center C))
  have hq := (ih.subgroup C hcproper).1.stronglyQuasithin_section hsqt
    (hK.subgroup C) hsec hsemi
  refine ⟨hsqt, hq, ?_⟩
  exact (ih.section_of_proper_subgroup hcproper hsec).2.2 inferInstance
    (Group.IsPerfect.not_isMulCommutative _) hq ((hK.subgroup C).quotient _)

theorem component_centralQuotient_models_of_semisimple_not_quasisimple
    (ih : TheoremsOnProperSections K G) (hG : IsQuasithin G) (hK : IsKGroup K G)
    (hsemi : IsSemisimple G) (hn : ¬ IsQuasisimple G)
    {C : Subgroup G} (hC : IsComponent G C) :
    IsStronglyQuasithin C ∧ IsStronglyQuasithin (C ⧸ center C) ∧
      IsTheoremCModel (C ⧸ center C) := by
  have hcproper : C ≠ ⊤ := by
    intro ht
    let : IsQuasisimple (⊤ : Subgroup G) := ht ▸ hC.2
    exact hn (IsQuasisimple.of_mulEquiv topEquiv)
  have hex : ∃ D : Subgroup G, IsComponent G D ∧ C ≠ D := by
    by_contra! hh
    apply hcproper
    apply top_unique
    rw [← hsemi]
    apply sSup_le
    intro D hD
    exact (hh D hD).symm.le
  obtain ⟨D, hD, hne⟩ := hex
  exact component_centralQuotient_models_of_ne ih hG hK hC hD hne

end CFSG.Quasithin.ChapterA.Section02
