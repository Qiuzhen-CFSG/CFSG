module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalA7Exclusion
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.ExceptionalModelsSource

/-!
# The actual Cartan component in the whole omega-centralizer

Enlarge the witnessed component in the local family, carrying along the
original escaping cubic and inverter. The proved exceptional-overcomponent
theorem preserves the genuine two-core quotient model. Applying the universal
centralization theorem to this enlarged witness shows that the maximal
component still centralizes the original Sylow omega-center.

Source 1.2.7 gives componenthood in the whole omega-centralizer, and 1.2.4
proves relative normality there. The same maximal-local uniqueness places
the normalizer of omega and every nonidentity omega-point centralizer in
the normalizer of this single component. Thus relocation is constructed
from one actual witness, with no second component-sieve invocation.

At degree two the existing whole-module proof completes the exceptional
conclusion. Deriving that degree from the original inputs, and constructing
the initial component-and-cubic witness, remain source obligations.
Source: Aschbacher–Smith 5.1.13, printed pp.637–638, using 1.2.4 and 1.2.7,
printed pp.505–506, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- Enlarge the actual component and retain the original escaping cubic. -/
theorem LocalCartanWitness.maximal_join_witness
    {T : Sylow 2 G} {H A Y X D K : Subgroup G}
    (d : LocalCartanWitness T H A Y X D)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hK : K ∈ Chapter1.LStar G (T : Subgroup G)) (hXK : X ≤ K) :
    K ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (H : Set G) ∧
      LocalCartanWitness T H A (K ⊔ (T : Subgroup G)) K D := by
  have hn := d.overcomponent_sylow_normalizes hG hTH hY hK.1 hXK
  have hm := exceptionalLocalOvercomponentModels_source hG T X K
    (d.mem_localFamily hTH hY) (d.sylow_normalizes hTH hY.2) hK hXK d.component_model
  have hHJ : H ≤ K ⊔ (T : Subgroup G) := by
    rw [←residual_sup_sylow T H hTH]
    exact sup_le ((d.residual_le.trans hXK).trans le_sup_left) le_sup_right
  refine ⟨⟨hK.1.2.2,hHJ⟩,⟨le_sup_left,hK.1.1,?_,
    d.residual_le.trans hXK,d.residual_linear,hm,?_,d.cubic_card,d.cubic_escape,?_⟩⟩
  · exact normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  · exact le_inf (d.cubic_le.trans inf_le_left) ((d.cubic_le.trans inf_le_right).trans hXK)
  · obtain ⟨t,ht,hi⟩ := d.cubic_inverted
    exact ⟨t,⟨ht.1,hXK ht.2⟩,hi⟩

/-- The maximal local component containing the source witness also centralizes omega. -/
theorem localCartan_maximal_centralizing_witness
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) :
    ∃ K : Subgroup G, X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      K ≤ omegaCentralizer T ∧
      LocalCartanWitness T H A (K ⊔ (T : Subgroup G)) K D := by
  obtain ⟨K,hK,hXK⟩ := d.exists_maximal_local hH.1.1.2 hY
  obtain ⟨hJ,dK⟩ := d.maximal_join_witness h.qtke hH.1.1.2 hY hK hXK
  exact ⟨K,hXK,hK,localCartan_centralizes h hH hgen c hJ dK,dK⟩

/-- Every nonidentity central involution has its full centralizer inside
one normalizer, that of the same maximal local component. -/
theorem LocalCartanWitness.point_centralizer_le_normalizer
    {T : Sylow 2 G} {H A Y K D : Subgroup G}
    (d : LocalCartanWitness T H A Y K D)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hK : K ∈ Chapter1.LStar G (T : Subgroup G))
    (hKC : K ≤ omegaCentralizer T)
    {z : G} (hz : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) (hne : z ≠ 1) :
    centralizer ({z} : Set G) ≤ normalizer (K : Set G) := by
  have hn := d.sylow_normalizes hTH hY.2
  have horbit : componentOrbit K (T : Subgroup G) = K :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer K T K le_rfl hn) (le_componentOrbit K T)
  have htwo := ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1
  obtain ⟨N,hCN,hN⟩ := Finite.exists_le_maximal
    (isTwoLocal_involution_centralizer (orderOf_eq_prime htwo hne))
  have hC : omegaCentralizer T ≤ centralizer ({z} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr hz)
  have he := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple hG T hK).normalizer_unique
    N hN ((sup_le hKC sylow_le_omegaCentralizer).trans (hC.trans hCN))
  rw [horbit] at he
  exact he ▸ hCN

/-- The normalizer of the whole central omega also normalizes the maximal
component. This is the normalizer needed by the postcentralization torus argument. -/
theorem LocalCartanWitness.omega_normalizer_le_normalizer
    {T : Sylow 2 G} {H A Y K D : Subgroup G}
    (d : LocalCartanWitness T H A Y K D)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hK : K ∈ Chapter1.LStar G (T : Subgroup G))
    (hKC : K ≤ omegaCentralizer T) :
    normalizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      normalizer (K : Set G) := by
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  have hT : (T : Subgroup G) ≠ ⊥ := by
    intro he
    have hc := pCoreIn_le_sylow (K ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] at hc
    exact hK.1.2.2 (bot_unique (hc.trans_eq he))
  let : Nontrivial (T : Subgroup G) := (nontrivial_iff_ne_bot _).mpr hT
  have hZ : Z ≠ ⊥ := by
    intro he
    exact omega_center_ne_bot T.isPGroup'
      ((Subgroup.map_eq_bot_iff_of_injective _ (f := (T : Subgroup G).subtype)
        (T : Subgroup G).subtype_injective).mp he)
  have hc : Z ≤ (normalizer (Z : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      (Stellmacher.omegaOneCenterAmbient_elementaryAbelian _).isPGroup Z.le_normalizer le_rfl
  have hcore : (normalizer (Z : Set G)).pCoreIn 2 ≠ ⊥ :=
    fun he => hZ (bot_unique (hc.trans_eq he))
  have hcore' : pCore 2 (normalizer (Z : Set G)) ≠ ⊥ := by
    intro he
    apply hcore
    simp only [Subgroup.pCoreIn,he,Subgroup.map_bot]
  obtain ⟨N,hN,hZN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot _ hcore'
  have hn := d.sylow_normalizes hTH hY.2
  have horbit : componentOrbit K (T : Subgroup G) = K :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer K T K le_rfl hn) (le_componentOrbit K T)
  have hJZ : K ⊔ (T : Subgroup G) ≤ normalizer (Z : Set G) :=
    (sup_le hKC sylow_le_omegaCentralizer).trans (Subgroup.centralizer_le_normalizer _)
  have he := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple hG T hK).normalizer_unique
    N hN (hJZ.trans hZN)
  rw [horbit] at he
  exact he ▸ hZN

/-- Maximality gives componenthood and normality in the whole omega-centralizer. -/
theorem LocalCartanWitness.relocate_maximal
    {T : Sylow 2 G} {H A K D : Subgroup G}
    (d : LocalCartanWitness T H A (K ⊔ (T : Subgroup G)) K D)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hK : K ∈ Chapter1.LStar G (T : Subgroup G))
    (hKC : K ≤ omegaCentralizer T) :
    LocalCartanWitness T H A (omegaCentralizer T) K D := by
  let C := omegaCentralizer T
  have hC := omegaCentralizer_mem_HOver_of_residual hH (d.residual_le.trans hKC)
  have hJC : K ⊔ (T : Subgroup G) ≤ C := sup_le hKC sylow_le_omegaCentralizer
  have hcomp : (K.subgroupOf C).IsCComponent :=
    (Chapter1.Section02.nonsolvable_uniqueness_knownSimple hG T hK).component C ⟨hC.1,hJC⟩
  let S := T.subtype (show (T : Subgroup G) ≤ C from sylow_le_omegaCentralizer)
  have hlocal : K.subgroupOf C ∈ Chapter1.L C (S : Subgroup C) :=
    (Chapter1.mem_LIn_iff_subgroupOf sylow_le_omegaCentralizer hKC).mp ⟨hKC,hK.1⟩
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) := by
    exact (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right).trans
      ((normal_subgroupOf_iff_le_normalizer (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).mp
        d.component_normal)
  have hn : (S : Subgroup C) ≤ normalizer (K.subgroupOf C : Set C) := by
    intro t ht
    exact mem_normalizer_iff.mpr (fun x => mem_normalizer_iff.mp (hTK ht) (x : G))
  obtain ⟨J,⟨hJ,hKJ,hJn⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hC.1) S hlocal hn
  have he := hcomp.eq_of_le hJ hKJ
  exact ⟨hKC,hcomp,he.symm ▸ hJn,d.residual_le,d.residual_linear,d.component_model,
    d.cubic_le,d.cubic_card,d.cubic_escape,d.cubic_inverted⟩

/-- The original witness gives an actual component in the full centralizer,
without a second invocation of the escaping-component sieve. -/
theorem localCartan_centralizer_witness
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) :
    ∃ K : Subgroup G, X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      LocalCartanWitness T H A (omegaCentralizer T) K D ∧
      normalizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
        normalizer (K : Set G) ∧
      (∀ z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G), z ≠ 1 →
        centralizer ({z} : Set G) ≤ normalizer (K : Set G)) := by
  obtain ⟨K,hXK,hK,hKC,dK⟩ := localCartan_maximal_centralizing_witness h hH hgen c hY d
  have dC := dK.relocate_maximal h.qtke hH.1.1 hK hKC
  have hJ : K ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (H : Set G) := by
    refine ⟨hK.1.2.2,?_⟩
    rw [←residual_sup_sylow T H hH.1.1.2]
    exact sup_le (dK.residual_le.trans le_sup_left) le_sup_right
  exact ⟨K,hXK,hK,dC,dK.omega_normalizer_le_normalizer h.qtke hH.1.1.2 hJ hK hKC,
    fun _ hz hne => dK.point_centralizer_le_normalizer h.qtke hH.1.1.2 hJ hK hKC hz hne⟩

/-- With the original field degree two, a single actual witness now gives
all of the source conclusion, including the full relative component. -/
theorem localCartan_escape_of_witness_degree_two
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) :
    CartanExceptionalConclusion T L W H := by
  obtain ⟨K,_,_,dK,_⟩ := localCartan_centralizer_witness h hH hgen c hY d
  exact ⟨dK.module_of_exponent_eq_two h hH c dK.component_le rfl,
    dK.residual_linear,K,dK.residual_le,dK.component_le,dK.component,dK.component_model⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
