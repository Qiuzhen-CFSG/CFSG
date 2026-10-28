module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.Contracts
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The moving offender in the high-three-rank branch

Generation by best offenders makes some best offender move every noncentral
subgroup. Components centralize the three-core, so an offender moving that
core is not contained in the component. Oddness of the component centralizer
makes the actual conjugation homomorphism injective on each best offender.

These prove the selection and faithfulness assertions on printed p.106 of
Aschbacher–Smith, combined 1 March 2004 manuscript, in the proof of B.5.7.
The earlier argument still must supply the odd centralizer; no classification
or natural-module identification follows from this file alone.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank
universe u v
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V)

private theorem component_centralizes_threeCore {L : Subgroup G} (hL : IsComponent G L) :
    L ≤ centralizer (pCore 3 G : Set G) := by
  rcases hL.normal_dichotomy (pCore 3 G) with hle | hc
  · let := hL.2
    let := IsQuasisimple.simple (G := L)
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    let := (pCore_isPGroup (p := 3) (G := G)).isNilpotent
    let : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective hle)
    exact (Group.IsPerfect.not_isSolvable L inferInstance).elim
  · exact commutator_eq_bot_iff_le_centralizer.mp hc

/-- Oddness of the centralizer gives faithfulness on the actual component,
for every best offender of the original representation. -/
theorem offender_conjugation_faithful {L : Subgroup G}
    (d : NoncentralContext K G L) {A : Subgroup G} (hA : IsBestOffender ρ A) :
    Function.Injective ((@MulAut.conjNormal G _ L d.normal).comp A.subtype) := by
  let : L.Normal := d.normal
  let : IsElementaryAbelian 2 A := hA.1.2
  apply injective_comp_subtype_of_coprime_ker (p := 2)
    (MulAut.conjNormal : G →* MulAut L) ?_ A (IsElementaryAbelian.isPGroup 2 A)
  rw [MulAut.conjNormal_ker_eq_centralizer]
  exact Nat.coprime_two_left.mpr d.odd_centralizer

/-- The offender which moves `O₃(G)` lies outside `L` and acts faithfully
on `L`. This is the actual offender selected in B.5.7, before applying B.5.1. -/
theorem exists_moving_offender (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (d : NoncentralContext K G L) :
    ∃ A : Subgroup G, IsBestOffender ρ A ∧
      ¬ A ≤ centralizer (pCore 3 G : Set G) ∧ ¬ A ≤ L ∧
      Function.Injective ((@MulAut.conjNormal G _ L d.normal).comp A.subtype) := by
  have hex : ∃ A : Subgroup G, IsBestOffender ρ A ∧
      ¬ A ≤ centralizer (pCore 3 G : Set G) := by
    by_contra! hn
    have hJ : offenderSubgroup ρ ≤ centralizer (pCore 3 G : Set G) := by
      apply iSup_le
      intro A
      apply iSup_le
      rintro ⟨hA, _⟩
      exact hn A hA
    rw [hyp.generated] at hJ
    exact d.noncentral (centralizer_eq_top_iff_subset.mp (top_unique hJ))
  obtain ⟨A, hA, hm⟩ := hex
  exact ⟨A, hA, hm, fun h => hm (h.trans (component_centralizes_threeCore hL)),
    offender_conjugation_faithful ρ d hA⟩

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank
