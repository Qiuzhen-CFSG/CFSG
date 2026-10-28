module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.Contracts
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.ComponentRanks
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.Offender
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.Quotient

/-!
# Faithful seed preparation from the full earlier B.5.5 implication

The full universal B.5.5 input supplies normality and the fixed-core action.
The imported proofs pass to U, identify its centralizer, transport minimality
to A⁺, and prove all intrinsic group requirements of the literal quotient
LA/C_LA(U). The SQTK presentation already supplies the component's K-group
property. The full component models and three-rank-one hypothesis give its
odd-prime rank bound. `prepared_of_three_rank_one` combines these proofs into
`Prepared`, discharging every local quotient requirement. `prepared_of_source`
specializes to the source setup, for every component moved by the chosen
minimal best offender. No reduced list or SQTK conclusion is inserted into
the earlier input.

Earlier-source inventory: only the complete universal `ComponentInput`
(B.5.5) is used. `CoverInput` is the separately published full
B.5.2 contract and is not currently assumed by the proved assembly.
The producer of both earlier implications is qt-b05-quotient-components;
their final discharge belongs to qt-b05-general-classification.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.2–B.5.5, printed pp.103–105; B.5.9, printed p.107, first paragraph.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation
open QuasisimpleSource
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}

/-- The K-group assertion descends through the actual SQTK quotient and
to every subgroup. No prime-rank quotient monotonicity is used. -/
theorem component_isKGroup (hyp : FFHypothesis K ρ) (L : Subgroup G) : IsKGroup K L := by
  obtain ⟨q⟩ := hyp.quotient
  have hG : IsKGroup K G :=
    (IsKGroup.equiv q.equiv).mp (q.sqtk.isKGroup.quotient q.kernel)
  exact hG.subgroup L

set_option backward.isDefEq.respectTransparency false in
/-- Preparation from the complete universal earlier B.5.5 implication and
an explicit odd-prime-rank bound for the actual component. The source assembly
below supplies this bound from the full model list and three-rank one. -/
theorem prepared_of_component_rank
    (earlier : ComponentInput.{u,v} K) (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L) (hrank : IsStronglyQuasithin L) :
    Prepared ρ K hLA := by
  let : Module.Finite (ZMod 2) V := hyp.finite_module
  have h5 := earlier G V ρ hyp
  let : L.Normal := h5.normal L hL
  obtain ⟨hfaith,hcentral,_⟩ := h5.fixedCore L hL A hA.1 hLA
  have hcore := normal_twoCore_eq_bot (L := L) hyp.twoCore
  have hf := seedComponent_faithful ρ hLA hcore hfaith
  have hc := seed_centralizer_eq ρ hLA hL hf hcentral
  have hm := seed_noncentral ρ hLA hL hc
  have hmin := seedOffender_minimal ρ hyp.faithful hA hLA hm
  let : IsElementaryAbelian 2 A := hA.1.1.2
  have hp : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  let : IsQuasisimple L := hL.2
  have hs : IsSQTK K L := ⟨hrank,component_isKGroup ρ hyp L⟩
  refine ⟨inferInstance,hf,hc,hm,hmin,?_⟩
  exact {
    finite_module := inferInstance
    faithful := seedQuotientAction_faithful ρ hLA
    quasisimple := IsQuasisimple.of_mulEquiv (seedComponentEquiv ρ hLA hf)
    sqtk := (IsSQTK.equiv (seedComponentEquiv ρ hLA hf)).mp hs
    fitting := seedQuotient_fitting_sup_center ρ hLA hL.2 hf hp
    twoCore := seedQuotient_twoCore ρ hLA hf hp
    generated := seedQuotient_generated ρ hLA hmin.1 }

/-- The first-paragraph quotient preparation in B.5.9. The odd-prime rank
condition is proved from the full B.5.5 models of this actual component. -/
theorem prepared_of_three_rank_one
    (earlier : ComponentInput.{u,v} K) (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L) (h3 : primeRank 3 L = 1) :
    Prepared ρ K hLA :=
  prepared_of_component_rank ρ earlier hyp hA hL hLA
    (component_stronglyQuasithin ρ earlier hyp hL h3)

/-- Apply the preparation to every moved component in the source setup after
B.5.7 and B.5.8. Centralization of F(G) belongs to that setup; the local
preparation already follows from the other hypotheses, as proved above.
The only retained earlier-source implication is the complete B.5.5 input. -/
theorem prepared_of_source
    (earlier : ComponentInput.{u,v} K) (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (_hAF : A ≤ centralizer (fittingSubgroup G : Set G))
    (h3 : ∀ M, IsComponent G M → primeRank 3 M = 1)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L) : Prepared ρ K hLA :=
  prepared_of_three_rank_one ρ earlier hyp hA hL hLA (h3 L hL)
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation
