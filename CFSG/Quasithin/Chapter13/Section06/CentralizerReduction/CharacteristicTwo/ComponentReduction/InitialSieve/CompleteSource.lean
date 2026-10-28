module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.OddLinear
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.Sporadic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.Sporadic.Rudvalis
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application

/-!
# The full initial component sieve in 13.6.6

The original marked local configuration constructs all inputs at C_G(v).
The involution product eliminates its odd core using the proved 1.1.5
inversion theorem. The source component-orbit bound then constructs the
literal central four-group in N(K)/C(K), without a four-model callback.
The complete known-simple 1.1.5 theorem and intrinsic alternating, odd,
sporadic and binary fixer calculations reduce every component to a larger
characteristic-two field with E* inside K*, or the whole S6 quotient.

The final application constructs this data from the earlier unaligned flag,
local source statements and fusion. The S6 block contradiction and subsequent
Suzuki/Borel exclusions are separate steps; characteristic two and 13.6.7
are not asserted here.

Source: Aschbacher--Smith, combined manuscript, 13.6.6, pp.926--927.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve
open Subgroup Theory.GroupTheory A5Module
open Chapter15.Section03.Candidates.ComponentStructure
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
  {T : Sylow 2 G} {s : Marking L V}

/-- The local odd core is trivial by the marked triple and the actual 1.1.5 input. -/
theorem Setup.oddCore_eq_bot (d : Setup KnownSimple.IsKnownSimple T s) :
    pPrimeCore 2 (Gv (markedV s)) = ⊥ :=
  oddCore_eq_bot_of_marked_module s (fun x hx => d.local115.inverts_oddCore x hx)

/-- The actual component has at most two ambient conjugates. -/
theorem Setup.component_orbit (d : Setup KnownSimple.IsKnownSimple T s)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K) :
    K.Normal ∨ (normalizer (K : Set (Gv (markedV s)))).index = 2 := by
  let := pCore_isNilpotent (p := 2) (G := Gv (markedV s))
  apply cComponent_normal_or_index_two_of_quotient hK.isCComponent
    (pCore 2 (Gv (markedV s)))
  exact ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
    (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
    (Chapter1.Section02.uniqueness_local_quotient_sqtk d.ambient d.local115.mem_H)
    (pCore_quotient_pCore_eq_bot 2) (hK.isCComponent.map_quotient _)

omit [Finite G] in
private theorem residual_normalizes_of_orbit (K : Subgroup (Gv (markedV s)))
    (hindex : K.Normal ∨ (normalizer (K : Set (Gv (markedV s)))).index = 2) :
    residual s ≤ X K := by
  rcases hindex with hn | hi
  · let := hn
    simp only [X, normalizer_eq_top]
    exact le_top
  · let N := normalizer (K : Set (Gv (markedV s)))
    let : N.Normal := N.normal_of_index_eq_two hi
    have hp : IsPGroup 2 (Gv (markedV s) ⧸ N) :=
      IsPGroup.of_card (n := 1) (by simpa only [pow_one, ← index_eq_card] using hi)
    have hle : pResidual 2 (Gv (markedV s)) ≤ N := sInf_le ⟨inferInstance, hp⟩
    let f : ↥(L ⊓ Gv (markedV s)) →* Gv (markedV s) := inclusion inf_le_right
    intro x hx
    obtain ⟨y, hy, he⟩ := hx
    have he' : f y = x := Subtype.ext he
    exact hle (he' ▸ map_pResidual_le 2 f (mem_map_of_mem f hy))

/-- Construct the actual component action using only the proved orbit bound;
no universal four-model classification is needed for this normalization. -/
theorem source_action_data_knownSimple (d : Setup KnownSimple.IsKnownSimple T s)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K) :
    ActionData s (T : Subgroup G) K := by
  have hodd := d.oddCore_eq_bot
  obtain ⟨hacore, hzcore⟩ := d.centralizer_cores
  have hnoncentral : ¬ K ⊓ localT (T : Subgroup G) (markedV s) ≤
      centralizer (K : Set (Gv (markedV s))) :=
    SetLike.not_le_iff_exists.mpr (d.exists_noncentral_sylow_element hodd K hK)
  have haN := normalizes_of_checked_center _ _ K hK (aLocal s) d.a_checked hnoncentral
  have hzC : zLocal s ∈ centralizer
      (localT (T : Subgroup G) (markedV s) : Set (Gv (markedV s))) := by
    intro t ht
    exact Subtype.ext (d.z_central t ht)
  have hzN := normalizes_of_checked_center _ _ K hK (zLocal s)
    (checked_center_of_centralizes _ _ _ (d.mark_mem_T _) hzC) hnoncentral
  have hindex := d.component_orbit K hK
  have hDN := residual_normalizes_of_orbit K hindex
  have hKz := component_commutator_z s K hK hzN hzcore
  have hKa := hK.commutator_eq_self_of_twoCore_centralizer _ haN hacore
  have hKD := component_commutator_residual s K hDN
    (z_mem_central_supplement s d.V_le_L) hKz
  have haD : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))) := by
    intro x hx
    exact Subtype.ext (mem_centralizer_iff.mp d.a_centralizes x hx)
  obtain ⟨hf, hc⟩ := marked_central_four s (T : Subgroup G) K hK haN hzN hDN
    (d.mark_mem_T _) (d.mark_mem_T _) haD hzC d.a_checked hacore hzcore
  refine ⟨haN, hzN, hDN, hKa, hKz, hKD, hf, hc, ?_⟩
  have hn : (X K).Normal := by
    rcases hindex with hn | hi
    · let := hn
      change (normalizer (K : Set (Gv (markedV s)))).Normal
      rw [normalizer_eq_top]
      infer_instance
    · exact (X K).normal_of_index_eq_two hi
  let := hn
  obtain ⟨P, hP⟩ := d.sylow.exists_subgroupOf_eq_of_normal (X K)
  refine ⟨P.mapSurjective (QuotientGroup.mk'_surjective (NormalizerAction.C K)), ?_⟩
  change (P : Subgroup (X K)).map (NormalizerAction.quotient K) = _
  rw [hP, ← localT_eq_sylow _ _ d.sylow d.sylow_image]
  rfl

/-- Both positive binary source alternatives, with all odd and sporadic cases excluded. -/
theorem source_binary_component (d : Setup KnownSimple.IsKnownSimple T s)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) : ModelExclusions.BinaryComponentModel K := by
  have hm := source_model_action d
    (fun hG H P M z h D hD => Chapter1.lemma_1_1_5_three_knownSimple hG H P M z h D hD)
    K hK a
  have hodd := d.oddCore_eq_bot
  cases hm with
  | lie hs hm _ => exact .simple hs hm
  | two_cover hn hc hm _ => exact .cover hn hc hm
  | six σ hs ha => exact (ModelExclusions.not_six d K hK hodd a σ hs ha).elim
  | seven σ hs ha => exact (ModelExclusions.not_seven d K hK hodd a σ hs ha).elim
  | odd hm _ => exact (ModelExclusions.OddLinear.not_odd_linear d K hK a hm).elim
  | sporadic name hn hm ha =>
    obtain ⟨e⟩ := hm
    exact (ModelExclusions.Sporadic.not_sporadic_quotient_of_remaining
      (ModelExclusions.Sporadic.ru_smallSylowFixers_of_stabilizers
        (by intro _ _ f; exact Rudvalis.outer_stabilizer_map_eq f))
      (by intro _ _; exact Held.Realization.normalizer_surjective)
      d K hK hodd a name hn e ha).elim

/-- The complete initial source sieve on the same marked centralizer and action quotient. -/
theorem source_model_sieve (d : Setup KnownSimple.IsKnownSimple T s)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K) :
    ∃ a : ActionData s (T : Subgroup G) K, ModelSieveAlternatives K a := by
  let a := source_action_data_knownSimple d K hK
  exact ⟨a, ModelExclusions.BinarySieve.alternatives_of_binary_component K hK a
    (source_binary_component d K hK a)⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open Subgroup Theory.GroupTheory A5Module ComponentReduction InitialSieve Stellmacher
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V V₁ V₂ : Subgroup G} {f : FlagMarking T L V V₁ V₂}

/-- The same marked local configuration supplies every applicability field. -/
noncomputable def LocalConfiguration.initialSetup (c : LocalConfiguration M f)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hVL : V ≤ L) (hVT : V ≤ (T : Subgroup G)) :
    Setup KnownSimple.IsKnownSimple T f.module where
  ambient := hG
  V_le_L := hVL
  V_le_T := hVT
  z_central := fun t ht =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp f.z_central).2.2 t ht
  sylow := c.reductions.centralizerSylow
  sylow_image := c.reductions.sylow_image
  a_centralizes := c.a_centralizes.2
  a_checked := by
    rw [localT_eq_sylow _ _ c.reductions.centralizerSylow c.reductions.sylow_image,
      c.reductions.checked_sylow_image]
    refine ⟨_, c.a_checked_central, ?_⟩
    change checkedSylowMap (T : Subgroup G) (markedV f.module) c.aPoint =
      QuotientGroup.mk' (vLine (markedV f.module)) (aLocal f.module)
    apply congrArg (QuotientGroup.mk' (vLine (markedV f.module)))
    exact Subtype.ext c.aPoint_val

/-- Failure of characteristic two selects an actual component in the marked
centralizer, and its entire action quotient satisfies the completed initial sieve. -/
theorem LocalConfiguration.initial_component_of_not_characteristic_two
    (c : LocalConfiguration M f) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hVL : V ≤ L) (hVT : V ≤ (T : Subgroup G))
    (hnot : generalizedFitting (Gv (markedV f.module)) ≠ pCore 2 (Gv (markedV f.module))) :
    ∃ K : Subgroup (Gv (markedV f.module)), IsComponent (Gv (markedV f.module)) K ∧
      ∃ a : ActionData f.module (T : Subgroup G) K, ModelSieveAlternatives K a := by
  let d := c.initialSetup hG hVL hVT
  obtain ⟨K, hK⟩ := exists_component_of_not_characteristic_two f.module
    (fun x hx => d.local115.inverts_oddCore x hx) hnot
  exact ⟨K, hK, source_model_sieve d K hK⟩

/-- Literal earlier-source consumer: the unaligned flag and earlier local
statements construct all marked action, odd-core and model-sieve data. -/
theorem initial_component_of_earlier_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (e : EarlierLocal T L M V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hVL : V ≤ L)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (hnot : generalizedFitting (Gv (markedV d.flag.module)) ≠
      pCore 2 (Gv (markedV d.flag.module))) :
    ∃ K : Subgroup (Gv (markedV d.flag.module)),
      IsComponent (Gv (markedV d.flag.module)) K ∧
      ∃ a : ActionData d.flag.module (T : Subgroup G) K, ModelSieveAlternatives K a := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d M V₃ e hcounter hfusion
  exact c.initial_component_of_not_characteristic_two hG hVL d.V_le_T hnot

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
