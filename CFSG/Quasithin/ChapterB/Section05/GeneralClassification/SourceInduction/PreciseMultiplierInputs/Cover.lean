module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.PreparationInput
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.NilpotentRadical
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# The B.5.7 lifted cover from A.3.6

A.3.6 applies to the actual component of the prepared SQTK cover, whose
trivial two-core follows from the original odd kernel and O₂(G)=1. Its
common clauses give center order one or three. The preparation input then
supplies positive component rank and the fitting identity. Existing rank
and component-lifting arguments construct the full lifted-cover record,
retaining the same projection and the same component image.

No faithful module of the covering group is assumed. The genuine A.3.6,
A.2 and B.5.2/B.5.5 implications remain explicit for their source owners.
Source: Aschbacher–Smith, A.3.6, pp.43–45, and B.5.2–7, pp.103–106.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.PreciseMultiplierInputs
open HighThreeRank HighThreeRank.CoverCentralizer
open HighThreeRank.CoverCentralizer.SourceConstruction
open ComponentReduction
universe u v

private theorem center_card_of_common
    {X : Type u} [Group X] [Finite X] [IsQuasisimple X]
    (h : Chapter1.Section02.A36Common X) :
    Nat.card (center X) = 1 ∨ Nat.card (center X) = 3 := by
  rcases h.2.2.1 with hf | hc
  · have ht : fittingSubgroup X = ⊤ :=
      hf.1.trans generalizedFitting_eq_top_of_quasisimple
    have hnil : Group.IsNilpotent (⊤ : Subgroup X) :=
      ht ▸ inferInstanceAs (Group.IsNilpotent (fittingSubgroup X))
    let := hnil
    let : Group.IsNilpotent X :=
      Group.nilpotent_of_mulEquiv (topEquiv : (⊤ : Subgroup X) ≃* X)
    let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
    let : Nontrivial X := (QuotientGroup.mk'_surjective (center X)).nontrivial
    exact (Group.IsPerfect.not_isNilpotent X inferInstance).elim
  · simpa only [hc.1] using hc.2.2

/-- A.3.6 bounds the center of the original lifted component. No faithful
representation of the covering group is required. -/
theorem lift_center_order {K : GroupClass.{u}}
    (h36 : Chapter1.Section02.A36Input K)
    {G : Type u} [Group G] [Finite G]
    (c : PreparedCover K G) (h2 : pCore 2 G = ⊥)
    {M : Subgroup c.Cover} (hM : IsComponent c.Cover M) :
    Nat.card (center M) = 1 ∨ Nat.card (center M) = 3 := by
  let := hM.2
  let : IsQuasisimple (⊤ : Subgroup M) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have ht : IsComponent M ⊤ :=
    ⟨(inferInstance : (⊤ : Subgroup M).Normal).isSubnormal, inferInstance⟩
  have hc := center_card_of_common (h36 M (c.sqtk.subgroup M)
    (lift_twoCore_eq_bot c h2 hM) ⊤ ht.isCComponent).2
  have he := Nat.card_congr (centerCongr (topEquiv : (⊤ : Subgroup M) ≃* M)).toEquiv
  rwa [he] at hc

variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The original B.5.2 cover and preparation facts construct the full lifted
cover, using A.3.6 for its center field. All quotient and component maps are
the maps supplied by the original prepared cover. -/
theorem liftedCover_of_preparation
    (h52 : CoverInput K)
    (h5 : PreliminaryActions.Preparation.ComponentInput.{u,v} K)
    (hA : SemisimpleInput K) (h36 : Chapter1.Section02.A36Input K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (hrL : 1 < primeRank 3 L) :
    Nonempty (LiftedCover K G L) := by
  obtain ⟨hposG, hfit⟩ := component_facts_of_preparation ρ h5 hyp
  obtain ⟨c⟩ := h52 G hyp.quotient
  obtain ⟨M, hM, hmap⟩ := c.component_lifts L hL
  have hz := lift_center_order h36 c.prepared hyp.twoCore hM
  have hrM := lift_rank c.prepared.projection M hmap hrL
  have hpos (D : Subgroup c.prepared.Cover) (hD : IsComponent c.prepared.Cover D) :
      0 < primeRank 3 D := by
    have hi := hposG (D.map c.prepared.projection) (component_image c.prepared hD)
    apply Nat.pos_of_ne_zero
    intro hd
    exact (Nat.ne_of_gt hi) (PrimeRank.eq_zero_of_surjective
      (c.prepared.projection.subgroupMap D)
      (c.prepared.projection.subgroupMap_surjective D) hd)
  have hEc : componentLayer c.prepared.Cover = M :=
    layer_eq_of_components_positive hM hrM
      (c.prepared.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide))
      (by rcases hz with h | h <;> omega) hpos
  have hE : componentLayer G = L := by
    apply le_antisymm
    · apply sSup_le
      intro D hD
      obtain ⟨N, hN, hn⟩ := c.component_lifts D hD
      have hNM : N ≤ M := hEc ▸
        (show N ≤ componentLayer c.prepared.Cover from le_sSup hN)
      rw [← hn, ← hmap]
      exact map_mono hNM
    · exact le_sSup hL
  let := hL.2
  have hsq : IsSQTK K L := by
    apply quasisimple_section_sqtk hA c.prepared.sqtk
    exact ⟨M, (MulEquiv.subgroupCongr hmap).toMonoidHom.comp
        (c.prepared.projection.subgroupMap M),
      (MulEquiv.subgroupCongr hmap).surjective.comp
        (c.prepared.projection.subgroupMap_surjective M)⟩
  exact ⟨{
    cover := c.prepared
    lift := M
    component := hM
    component_image := hmap
    lift_layer := hEc
    layer := hE
    component_sqtk := hsq
    fitting := hE ▸ hfit
    center_order := hz }⟩

end CFSG.Quasithin.ChapterB.SourceInduction.PreciseMultiplierInputs
