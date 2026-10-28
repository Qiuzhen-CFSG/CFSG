module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.Contracts

/-!
# The B.5.7 cover reduction from the existing B.5.5 preparation input

The cover construction uses two consequences of B.5.5: every component has
positive three-rank, and F*(G) = E(G)O₃(G)Z(G). The preparation input already
supplies both. For the rank assertion, its faithful chief section has actor
LA/ker(action); applying the proved model-rank theorem to that literal
projection avoids transporting all the action data to another actor.

The local construction below lifts the selected component through the B.5.2
cover, proves uniqueness of the lifted component, and supplies the exact layer
and Fitting equalities. Its source-input application discharges both local
facts from `Preparation.ComponentInput`. The final application invokes the
existing cover-centralizer reduction on this constructed witness.

The genuine earlier inputs remain B.5.2 and B.5.5 (producer
`qt-b05-quotient-components`), A.2.1 (`qt-a-02`), and the multiplier bound from
I.1.3 (`qt-i-01`). Final source discharge belongs to
`qt-b05-general-classification`.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
B.5.2--5 and the opening reduction of B.5.7, printed pp.103--106.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer
open ComponentReduction.PreliminaryActions
universe u v
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

namespace SourceConstruction

/-- The B.5.5 preparation section proves positive component three-rank through
its original quotient projection, with no change of section or action model. -/
theorem component_rank_pos_of_preparation (h : Preparation.ComponentConclusion ρ)
    {L : Subgroup G} (hL : IsComponent G L) : 0 < primeRank 3 L := by
  obtain ⟨A, _, _, ⟨s⟩⟩ := h.chief L hL
  have hi := rank_pos_of_section_action
    s.sectionData.projection (L.subgroupOf (L ⊔ A)) s.actions
  rwa [primeRank_equiv 3 (subgroupOfEquivOfLe
    (show L ≤ L ⊔ A from le_sup_left))] at hi

/-- Exactly the two B.5.5 facts consumed by the high-three-rank cover argument. -/
theorem component_facts_of_preparation (h5 : Preparation.ComponentInput.{u,v} K)
    (hyp : FFHypothesis K ρ) :
    (∀ L, IsComponent G L → 0 < primeRank 3 L) ∧
      generalizedFitting G = (componentLayer G ⊔ pCore 3 G) ⊔ center G := by
  have h := h5 G V ρ hyp
  exact ⟨fun L hL => component_rank_pos_of_preparation ρ h hL, h.fitting⟩

/-- Construct the literal lifted cover from local component-rank positivity
and the source Fitting equality. The following source application supplies
both facts from the already required B.5.5 preparation input. -/
theorem exists_liftedCover_of_component_facts (h52 : CoverInput K)
    (hA : SemisimpleInput K) (hI : MultiplierInput K)
    (hyp : FFHypothesis K ρ)
    (hposG : ∀ D, IsComponent G D → 0 < primeRank 3 D)
    (hfit : generalizedFitting G = (componentLayer G ⊔ pCore 3 G) ⊔ center G)
    {L : Subgroup G} (hL : IsComponent G L) (hrL : 1 < primeRank 3 L) :
    Nonempty (LiftedCover K G L) := by
  obtain ⟨c⟩ := h52 G hyp.quotient
  obtain ⟨M, hM, hmap⟩ := c.component_lifts L hL
  have hz := lift_center_order hA hI c.prepared hyp.twoCore hM
  have hrM := lift_rank c.prepared.projection M hmap hrL
  have hpos (D : Subgroup c.prepared.Cover) (hD : IsComponent c.prepared.Cover D) :
      0 < primeRank 3 D := by
    have hi := hposG (D.map c.prepared.projection)
      (component_image c.prepared hD)
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

/-- B.5.5 in its preparation encoding supplies every component fact required
to construct the B.5.7 cover. No second B.5.5 input is retained. -/
theorem exists_liftedCover_of_preparation (h52 : CoverInput K)
    (h5 : Preparation.ComponentInput.{u,v} K)
    (hA : SemisimpleInput K) (hI : MultiplierInput K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (hrL : 1 < primeRank 3 L) :
    Nonempty (LiftedCover K G L) := by
  obtain ⟨hpos, hfit⟩ := component_facts_of_preparation ρ h5 hyp
  exact exists_liftedCover_of_component_facts ρ h52 hA hI hyp hpos hfit hL hrL

end SourceConstruction

/-- Apply the existing B.5.7 centralizer reduction to the cover constructed
from the same B.5.5 preparation input used by the component recursion. -/
theorem reduction_of_preparation (h52 : SourceConstruction.CoverInput K)
    (h5 : Preparation.ComponentInput.{u,v} K)
    (hA : SourceConstruction.SemisimpleInput K)
    (hI : SourceConstruction.MultiplierInput K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (hr : 1 < primeRank 3 L) :
    (IsSQTK K L ∧ generalizedFitting G = L ⊔ center G) ∨
      Nonempty (NoncentralContext K G L) := by
  obtain ⟨d⟩ := SourceConstruction.exists_liftedCover_of_preparation ρ h52 h5 hA hI hyp hL hr
  exact reduction_of_liftedCover hyp hL hr d

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer
