module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionAligned
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ComponentEscape

/-!
# Assembling the aligned rank-one source configuration

The maximal outside choice is promoted to a full Sylow intersection using
original 4.3.1. The intermediate-core identities then supply 4.3.4 and the
crossing element of 4.3.5, including its conditional placement in O₂(LT).
The constructor retains only the actual escaping containing component and
its normalizer identification as inputs. Its application supplies the
configuration premise in the original uniqueness assembly.

Source: Aschbacher–Smith 4.3.2–5, printed pp.613–614.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The source Sylow intersection is proper and its full normalizer lies in N(L). -/
theorem OutsideChoice.sylow_data (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (c : OutsideChoice T L) :
    (T : Subgroup G) ⊓ c.H < (T : Subgroup G) ∧
      normalizer ((T : Subgroup G) ⊓ c.H : Set G) ≤ normalizer (L : Set G) ∧
      ∃ P : Sylow 2 c.H, (P : Subgroup c.H).map c.H.subtype = (T : Subgroup G) ⊓ c.H := by
  have hu := unique_sylow_join D h
  have hST : (T : Subgroup G) ⊓ c.H < (T : Subgroup G) := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    exact c.outside (hu.2.2 c.H c.maximal (sup_le c.contains (inf_eq_left.mp he)))
  obtain ⟨P,hP⟩ := c.local_sylow D h
  have hindex : ¬ 2 ∣ ((T : Subgroup G) ⊓ c.H).relIndex
      (c.H ⊓ normalizer (L : Set G)) := by
    have he := relIndex_map_map_of_injective (P : Subgroup _) ⊤
      (c.H ⊓ normalizer (L : Set G)).subtype_injective
    simp only [← MonoidHom.range_eq_map,range_subtype,relIndex_top_right,hP] at he
    rw [he]
    exact P.not_dvd_index
  obtain ⟨Q,hQ⟩ := exists_sylow_component D
  have hQS : (Q : Subgroup L).map L.subtype ≤ (T : Subgroup G) ⊓ c.H := by
    rw [hQ]
    exact inf_le_inf_left _ c.contains
  exact ⟨hST,source_sylow_promotion D h hpsl c.H _ hST Q hQS inf_le_right hindex
    (fun _ hSX hXT => c.strict_unique D h hSX hXT)⟩

/-- Complete the simultaneous configuration from the remaining source component.
All core, Sylow, C.2.8, maximality and crossing premises are discharged here. -/
theorem OutsideChoice.source_configuration_of_component
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : OutsideChoice T L) (K : Subgroup c.H)
    (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hLK : L ≤ K.map c.H.subtype)
    (houtK : ¬ K.map c.H.subtype ≤ normalizer (L : Set G))
    (hKN : K.Normal) (hNK : c.H = normalizer (K.map c.H.subtype : Set G)) :
    Nonempty (SourceConfiguration T L) := by
  have hu := unique_sylow_join D h
  have hout : ¬ c.H ≤ normalizer (L : Set G) :=
    fun hh => c.outside (c.maximal.eq_of_le hu.1.1 hh)
  have hLI : L ≤ c.intermediate := le_sup_left
  have hI : c.intermediate ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    sup_le_sup_left inf_le_left L
  have hIH : c.intermediate ≤ c.H := sup_le c.contains inf_le_right
  have hmax := fun J hIJ hJ => c.intermediate_maximal D h (J := J) hIJ hJ
  obtain ⟨hIe,hIc⟩ := intermediate_core_identities D h hLI hI
  obtain ⟨hST,hnS,hS⟩ := c.sylow_data D h hpsl
  obtain ⟨hRS,hRJ⟩ := selected_core_sylow D h hLI hI hmax c.maximal hIH hout
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) :=
    (source_core_section_intersection D h).le.trans inf_le_left
  have hTQ : (T : Subgroup G) ≤
      normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    le_sup_right.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  obtain ⟨t,ht,htout,htn,htsq,htcore⟩ := exists_source_crossing_in_core hST hQT hTQ hRS
  have hc := c.c28 D h
  exact ⟨{
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
    strict_unique := fun _ hSX hXT => c.strict_unique D h hSX hXT
    core_sylow := hRS
    core_join := hRJ
    crossing_mem := ht
    crossing_outside := htout
    crossing_normalizes := htn
    crossing_square := htsq
    crossing_core := htcore }⟩

/-- The exact configuration-constructor consumer of the remaining component
selection. This is conditional; the rank-one 4.2.12/C.4.8 input must still be proved. -/
theorem exists_sourceConfiguration_of_component_selection
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hcomponent : ∀ c : OutsideChoice T L,
      ∃ K : Subgroup c.H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        L ≤ K.map c.H.subtype ∧ ¬ K.map c.H.subtype ≤ normalizer (L : Set G) ∧
        K.Normal ∧ c.H = normalizer (K.map c.H.subtype : Set G))
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    Nonempty (SourceConfiguration T L) := by
  obtain ⟨c⟩ := exists_outside_choice D h hnot
  obtain ⟨K,hK,hq,hLK,hout,hKN,hNK⟩ := hcomponent c
  exact c.source_configuration_of_component D h hpsl K hK hq hLK hout hKN hNK

/-- Literal 4.3.2 assembly with only the component selection and three independent
source exclusions still explicit. No existing source branch is used circularly. -/
theorem uniqueness_of_component_selection_and_source_exclusions
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hcomponent : ∀ c : OutsideChoice T L,
      ∃ K : Subgroup c.H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        L ≤ K.map c.H.subtype ∧ ¬ K.map c.H.subtype ≤ normalizer (L : Set G) ∧
        K.Normal ∧ c.H = normalizer (K.map c.H.subtype : Set G))
    (hordinary : ∀ c : SourceConfiguration T L, IsComponent c.H c.K → False)
    (hblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ChapterC.IsBlock c.K → False)
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False) :
    ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G) :=
  uniqueness_of_source_exclusions
    (exists_sourceConfiguration_of_component_selection D h hpsl hcomponent)
    hordinary hblock hnonblock

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
