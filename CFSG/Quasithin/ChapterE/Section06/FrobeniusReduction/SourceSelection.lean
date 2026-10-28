module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.BlockSections
public import Theory.GroupTheory.GeneralizedFitting.NoComponentInverter
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source.RankOne
/-!
# E.6.11 selection at the original global minimum

Local odd-core vanishing and absence of ordinary components make the actual
centralizer C_G(U) characteristic two. Its E.6.7 product then supplies an
escaping factor. Both alternating block rows force globalR = 1, so the
chosen factor is an even-field rank-one block and a genuine C-component.
The source rank-one torus theorem recovers its original regular action and
normalization from the Borel already supplied by E.6.7.

Together with ComponentSections this constructs the literal section and local
model consumed by E.6.24–25. Only the earlier E.6.7 decomposition and component
sieve remain explicit; no selected-section, normal torus image, regularity,
maximality, or local odd-core conclusion is assumed.
Source: Aschbacher–Smith, E.6.11 and E.6.25, printed pp.249–250 and255.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
open Components LocalFactors InvariantSubspaces.BlockSelection
open Hyperplanes.Enlargement.BlockInspection
open Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U : Subgroup G}

/-- Without an ordinary component, the original minimum has characteristic two. -/
theorem minimum_component_or_characteristicTwo
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hmin : (subgroupCorank V U : ℕ∞) = globalR V) (hr : 1 < subgroupCorank V U) :
    (∃ L : Subgroup G, ComponentIn (centralizer (U : Set G)) L) ∨
      HasCharacteristicTwo (centralizer (U : Set G)) := by
  let H := centralizer (U : Set G)
  by_cases hc : ∃ L : Subgroup G, ComponentIn H L
  · exact Or.inl hc
  right
  have ho := h.oddCore_eq_bot_of_maximal_escape (source_earlierLocalFacts h) hU
    (h.maximal_escape_of_minimum hmin) hr
  have hnc : ∀ J : Subgroup H, ¬ IsComponent H J := by
    intro J hJ
    apply hc
    refine ⟨J.map H.subtype,map_subtype_le J,?_⟩
    have he : (J.map H.subtype).subgroupOf H = J :=
      comap_map_eq_self_of_injective H.subtype_injective J
    rwa [he]
  have hh := centralizer_core_product_le_of_no_components 2 hnc
  change pPrimeCore 2 H = ⊥ at ho
  change HasCharacteristicTwo H
  simpa only [HasCharacteristicTwo,ho,sup_bot_eq] using hh

/-- The characteristic-two source decomposition contains an escaping even-field block. -/
theorem exists_minimum_rankOne_factor
    (hU : U ∈ obstructionFamily M V)
    (hmin : (subgroupCorank V U : ℕ∞) = globalR V) (hr : 1 < subgroupCorank V U)
    (d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V U
      (centralizer (U : Set G))) :
    ∃ i, ¬ d.block i ≤ M ∧ ∃ n, ChapterC.IsL2EvenBlock (d.block i) n ∧
      d.block i ∈ Chapter1.cComponentsIn (centralizer (U : Set G)) ∧
      CentralizerBlock U (d.block i) := by
  classical
  have hex : ∃ i, ¬ d.block i ≤ M := by
    by_contra! hall
    exact hU.2.2.1 (d.generated.le.trans (sup_le inf_le_right (iSup_le hall)))
  obtain ⟨i,hi⟩ := hex
  have hone : globalR V ≠ 1 := by
    intro he
    have hh : subgroupCorank V U = 1 := by exact_mod_cast hmin.trans he
    omega
  have hthree : ¬ ChapterC.IsAlternatingBlock (d.block i) 3 :=
    fun ha => hone (d.alternating i 3 ha).2.2
  have htype : ∃ n, ChapterC.IsL2EvenBlock (d.block i) n := by
    rcases d.type i with hn | ha | ha
    · exact hn
    · exact (hthree ha).elim
    · exact (hone (d.alternating i 5 ha).2.2).elim
  obtain ⟨n,hn⟩ := htype
  have hLC := factor_cComponent (d.le i) (d.type i) (d.subnormal i) hthree
  have hblock : ChapterC.IsBlock ((d.block i).subgroupOf (centralizer (U : Set G))) :=
    ⟨inferInstance,hn.2.1.of_mulEquiv (subgroupOfEquivOfLe (d.le i)).symm,d.subnormal i⟩
  exact ⟨i,hi,n,hn,⟨d.le i,hLC⟩,d.le i,hblock⟩

/-- The actual E.6.7 family supplies a nonsolvable block whenever there is no component. -/
theorem minimum_source_seed
    (h : HypothesisE61 K T M V) (h67 : E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hmin : (subgroupCorank V U : ℕ∞) = globalR V) (hr : 1 < subgroupCorank V U) :
    (∃ L : Subgroup G, ComponentIn (centralizer (U : Set G)) L) ∨
      ∃ d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V U
        (centralizer (U : Set G)),
        HasCharacteristicTwo (centralizer (U : Set G)) ∧
        ∃ i, ¬ d.block i ≤ M ∧ ∃ n, ChapterC.IsL2EvenBlock (d.block i) n ∧
          d.block i ∈ Chapter1.cComponentsIn (centralizer (U : Set G)) ∧
          CentralizerBlock U (d.block i) := by
  rcases minimum_component_or_characteristicTwo h hU hmin hr with hc | hc
  · exact Or.inl hc
  · obtain ⟨d⟩ := h67 U hU (centralizer (U : Set G))
      (inf_le_right.trans (Subgroup.centralizer_le hU.1)) le_rfl hc
    exact Or.inr ⟨d,hc,exists_minimum_rankOne_factor hU hmin hr d⟩


/-- E.6.11 constructs the actual minimal section from its two earlier source families. -/
theorem minimalRegularSection_of_source_models
    (h : HypothesisE61 K T M V) (h67 : E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hmin : (subgroupCorank V U : ℕ∞) = globalR V) (hr : 1 < subgroupCorank V U)
    (hsieve : ∀ L : Subgroup G, ComponentIn (centralizer (U : Set G)) L →
      (∃ n, BorelAlternative M V U L n) ∨
        (∃ n, SymplecticAlternative M V U L n) ∨ globalR V = 1) :
    Nonempty (MinimalRegularSection T M V U) := by
  rcases minimum_source_seed h h67 hU hmin hr with ⟨L,hL⟩ | ⟨d,hc,i,hi,n,hn,hLC,hb⟩
  · exact component_regularSection_of_minimum h hU hmin hr hL (hsieve L hL)
  · obtain ⟨_,_,_,_,_,_,_,_,hB,_⟩ := d.rankOne i n hn
    obtain ⟨hVL,X,hXP,hcyc,hcard,hgen,hdis,hWcard,hprod,hB,_,hreg⟩ :=
      source_rankOne_of_borel h hU
        (inf_le_right.trans (Subgroup.centralizer_le hU.1)) le_rfl hc (d.le i) hb.2 hi hn hB
    exact block_regularSection_of_minimum h hU hmin hr hLC hb hi hVL hn
      hXP hcyc hcard hgen hdis hWcard hprod hB hreg

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
