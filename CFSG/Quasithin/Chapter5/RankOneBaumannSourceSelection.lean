module
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourcePushingUp
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Selection
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionContaining
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ContainingComponentQuotient

/-!
# Aligned original-input Baumann counterexamples

The original local-family and faithful-module hypotheses supply 12.2.1.
An auxiliary homogeneous constituent can therefore be selected to apply the
existing 4.3.3 Sylow alignment and 1.2.4 containing-component proofs. This
constituent is an internal choice: the original reduced W is unchanged,
and the source C.2.8 module is the actual omega-center commutator.

C.2.11 places the Fitting preimage of the containing normal component in
N(L). Fitting functoriality and the quasisimple quotient of L then prove
that the component itself has quasisimple two-core quotient. Thus the
constrained quotient identification is discharged, at the original scope.
The ordinary full-normalizer identification and source model exclusions
are still needed for the final Baumann normalizer bound.

Source: Aschbacher--Smith 1.2.4, C.2.11, and 4.3.2--5,
printed pp.505,148,613--614; application in 5.1.7(1), pp.633--634.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter4 Chapter4.Section02.Unitary Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

/-- The original source Input supplies 12.2.1, without the later model exclusions. -/
theorem Input.original_section1221
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L := by
  have hOmega (Q : Subgroup G) : centralOmega Q = Stellmacher.omegaOneCenterAmbient Q := by
    apply le_antisymm
    · apply (omegaOneAmbient_le_iff _ _).mpr
      intro x hx hp
      exact (Stellmacher.mem_omegaOneCenterAmbient_iff Q x).mpr
        ⟨hx.1,hp,mem_centralizer_iff.mp hx.2⟩
    · intro x hx
      obtain ⟨hxQ,hp,hc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff Q x).mp hx
      exact (omegaOneAmbient_le_iff _ _).mp le_rfl x
        ⟨hxQ,mem_centralizer_iff.mpr hc⟩ hp
  refine ⟨h.qtke,⟨h.maximal_local,?_,?_⟩,h.quotient_quasisimple⟩
  · exact ⟨h.local_mem.2.1,h.local_mem.2.2.1,h.local_mem.2.2.2.1⟩
  · have hh := h.local_mem.2.2.2.2
    rw [hOmega,commutator_comm] at hh
    simpa only [Subgroup.pCoreIn,ChapterA.Section04.intrinsicSignalizerModule,
      ChapterA.Section04.signalizerModule_eq_commutator_omegaCenter] using hh

private theorem Input.auxiliary_chosen
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    ∃ U : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T L U) :=
  h.original_section1221.exists_chosen_of_normalizes h.sylow_normalizes

/-- The literal omega-center module equals the moved subgroup under Baumann escape. -/
theorem Input.original_fullModule_eq_moved
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) = ⁅W,L⁆ := by
  have hs := ChapterA.Section04.sylow_core_sectionCentralizer T L
    h.local_mem.2.2.1 h.sylow_normalizes
  rw [← sectionCentralizerIn_eq_twoSectionCentralizer] at hs
  obtain ⟨P,hP⟩ := hs
  simpa only [hP] using h.original_fullModule_eq_moved_of_baumann_escape hout P

/-- The selected normal containing component has quasisimple quotient, by C.2.11. -/
theorem Input.original_containing_component_quotient
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : OutsideChoice T L) (K : Subgroup c.H) (hK : K.IsCComponent)
    (hLK : L ≤ K.map c.H.subtype) (hn : K.Normal) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  obtain ⟨U,⟨D⟩⟩ := h.auxiliary_chosen
  exact (c.c28 D h.original_section1221).normal_containing_component_quotient
    inf_le_right h.quotient_quasisimple K hK hLK hn

/-- Baumann escape supplies a full Sylow intersection and an actual normal,
escaping, quasisimple-quotient component containing the original L. -/
theorem Input.original_outside_component_of_baumann_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    ∃ (c : OutsideChoice T L) (K : Subgroup c.H),
      ChapterC.IsAlternatingBlock L 5 ∧
      fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) = ⁅W,L⁆ ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple c.H (c.H ⊓ normalizer (L : Set G))
        L (c.intermediate.pCoreIn 2) ⁅W,L⁆ ∧
      K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      L ≤ K.map c.H.subtype ∧ ¬ K.map c.H.subtype ≤ normalizer (L : Set G) ∧
      K.Normal ∧ (IsComponent c.H K ∨ generalizedFitting K = pCore 2 K) ∧
      (T : Subgroup G) ⊓ c.H < (T : Subgroup G) ∧
      normalizer ((T : Subgroup G) ⊓ c.H : Set G) ≤ normalizer (L : Set G) ∧
      ∃ P : Sylow 2 c.H, (P : Subgroup c.H).map c.H.subtype = (T : Subgroup G) ⊓ c.H := by
  obtain ⟨U,⟨D⟩⟩ := h.auxiliary_chosen
  obtain ⟨c⟩ := exists_outside_choice D h.original_section1221
    (fun hu => hout (h.baumann_normalizer_of_source_uniqueness hu.2.2))
  obtain ⟨K,hK,hLK,houtK,hn⟩ := c.exists_normal_escaping_component D h.original_section1221 h.linear
  have hc := c.c28 D h.original_section1221
  rw [h.original_fullModule_eq_moved hout] at hc
  exact ⟨c,K,(h.alternating_block_of_baumann_escape hout).2.1,
    h.original_fullModule_eq_moved hout,hc,hK,h.original_containing_component_quotient c K hK hLK hn,
    hLK,houtK,hn,hK.component_or_generalizedFitting_eq_pCore hc.oddCore_eq_bot,
    c.sylow_data D h.original_section1221 h.linear⟩

/-- In the constrained branch every clause of the shared source configuration
is now constructed, including the quotient and the full component normalizer. -/
theorem Input.original_configuration_of_constrained_component
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : OutsideChoice T L) (K : Subgroup c.H) (hK : K.IsCComponent)
    (hLK : L ≤ K.map c.H.subtype)
    (houtK : ¬ K.map c.H.subtype ≤ normalizer (L : Set G))
    (hKN : K.Normal) (hf : generalizedFitting K = pCore 2 K) :
    ∃ d : SourceConfiguration T L, d.I = c.intermediate ∧ d.H = c.H ∧
      d.K.map d.H.subtype = K.map c.H.subtype ∧
      generalizedFitting d.K = pCore 2 d.K ∧ (ChapterC.IsBlock d.K ↔ ChapterC.IsBlock K) := by
  obtain ⟨U,⟨D⟩⟩ := h.original_section1221.exists_chosen_of_normalizes h.sylow_normalizes
  have hq := h.original_containing_component_quotient c K hK hLK hKN
  have hNK := c.component_normalizer_of_constrained K hK hKN hf
  have hs := h.original_section1221
  have hpsl := h.linear
  have hu := unique_sylow_join D hs
  have hout : ¬ c.H ≤ normalizer (L : Set G) :=
    fun hh => c.outside (c.maximal.eq_of_le hu.1.1 hh)
  have hLI : L ≤ c.intermediate := le_sup_left
  have hI : c.intermediate ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    sup_le_sup_left inf_le_left L
  have hIH : c.intermediate ≤ c.H := sup_le c.contains inf_le_right
  have hmax := fun J hIJ hJ => c.intermediate_maximal D hs (J := J) hIJ hJ
  obtain ⟨hIe,hIc⟩ := intermediate_core_identities D hs hLI hI
  obtain ⟨hST,hnS,hS⟩ := c.sylow_data D hs hpsl
  obtain ⟨hRS,hRJ⟩ := selected_core_sylow D hs hLI hI hmax c.maximal hIH hout
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) :=
    (source_core_section_intersection D hs).le.trans inf_le_left
  have hTQ : (T : Subgroup G) ≤
      normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    le_sup_right.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  obtain ⟨t,ht,htout,htn,htsq,htcore⟩ := exists_source_crossing_in_core hST hQT hTQ hRS
  have hc := c.c28 D hs
  let d : SourceConfiguration T L := {
    I := c.intermediate
    H := c.H
    K := K
    t := t
    le_I := hLI
    I_le := hI
    I_maximal := hmax
    I_eq := hIe
    core_intersection := hIc
    maximal := c.maximal
    I_le_H := hIH
    outside := hout
    c28 := hc
    component := hK
    quotient := hq
    le_component := hLK
    component_outside := houtK
    component_normal := hKN
    component_cases := hK.component_or_generalizedFitting_eq_pCore hc.oddCore_eq_bot
    normalizer_component := hNK
    sylow_strict := hST
    sylow := hS
    normalizer_sylow := hnS
    strict_unique := fun _ hSX hXT => c.strict_unique D hs hSX hXT
    core_sylow := hRS
    core_join := hRJ
    crossing_mem := ht
    crossing_outside := htout
    crossing_normalizes := htn
    crossing_square := htsq
    crossing_core := htcore }
  exact ⟨d,rfl,rfl,rfl,hf,Iff.rfl⟩


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
