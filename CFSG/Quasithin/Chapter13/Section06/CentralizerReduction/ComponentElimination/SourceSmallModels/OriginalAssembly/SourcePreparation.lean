module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.OriginalSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.SelectedSeed
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PairedSetup
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingIntrinsic
/-!
# Original inputs to the alternating-seven selection step

The original flag and 13.6.6,14,16,20 conclusions put the reduced seed
module on the literal component--Sylow join. Characteristic two passes to
that join and its component, and normalization gives the actual product.
Characteristicity of the Baumann subgroup transports 13.6.16's strict
normalizer obstruction to the exact characteristic alternatives in C.1.24.

For an A₇ plus image the complete A.3.6 source theorem also constructs the
intrinsic quasisimple quotient and its A₇ central quotient. No minimal
replacement, block, shortness, module marking or A.3.6 callback is assumed.
The remaining C.1.24 local-seed argument must still produce shortness.

Source: Aschbacher--Smith, C.1.24, pp.130--131, and 13.6.22, p.932.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
open SourceTransferFields.HigherFieldParabolics
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) [C.Characteristic] :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro α x hx
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨e.symm (α (e c)), ?_, e.apply_symm_apply _⟩
  exact characteristic_iff_le_comap.mp inferInstance ((e.trans α).trans e.symm) hc

omit [Finite G] in
private theorem baumann_characteristic_exclusion (S : Subgroup G)
    (h : ∀ C : Subgroup S, C.Characteristic → C ≠ ⊥ → ¬ (C.map S.subtype).Normal) :
    ∀ C : Subgroup (ChapterB.baumann S), C.Characteristic → C ≠ ⊥ →
      ¬ (C.map (ChapterB.baumann S).subtype).Normal := by
  intro C hC hne hn
  let := hC
  let B := ChapterB.baumann S
  have hBS : B ≤ S := inf_le_left
  have hB : B.subgroupOf S = ChapterB.baumann (⊤ : Subgroup S) := by
    apply map_injective S.subtype_injective
    rw [map_subgroupOf_eq_of_le hBS]
    change ChapterB.baumann S = (ChapterB.baumann (⊤ : Subgroup S)).map S.subtype
    rw [ChapterC.RankOne.SymmetricSix.baumann_map S S.subtype S.subtype_injective,
      ← MonoidHom.range_eq_map, range_subtype]
  let : (B.subgroupOf S).Characteristic := hB ▸ ChapterB.baumann_characteristic
  let e : B ≃* B.subgroupOf S := (subgroupOfEquivOfLe hBS).symm
  let C' := C.map e.toMonoidHom
  let : C'.Characteristic := characteristic_map_equiv e C
  let D := C'.map (B.subgroupOf S).subtype
  let : D.Characteristic := inferInstance
  have hmap : D.map S.subtype = C.map B.subtype := by
    rw [map_map, map_map]
    rfl
  have hDne : D ≠ ⊥ := by
    intro hb
    have hC0 : C.map B.subtype = ⊥ := by rw [← hmap, hb, Subgroup.map_bot]
    exact hne ((C.map_eq_bot_iff_of_injective B.subtype_injective).mp hC0)
  exact h D inferInstance hDne (hmap.symm ▸ hn)

omit [Finite G] in
private theorem baumann_characteristic_exclusion_of_obstruction (S K : Subgroup G)
    (h : CharacteristicNormalizerObstruction S K)
    (P : Sylow 2 (K ⊔ S : Subgroup G))
    (hP : (P : Subgroup (K ⊔ S : Subgroup G)).map (K ⊔ S).subtype = S) :
    ∀ C : Subgroup (ChapterB.baumann (P : Subgroup (K ⊔ S : Subgroup G))),
      C.Characteristic → C ≠ ⊥ →
        ¬ (C.map (ChapterB.baumann (P : Subgroup (K ⊔ S : Subgroup G))).subtype).Normal := by
  exact baumann_characteristic_exclusion _
    (Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp.characteristic_exclusion_transport
      P hP (characteristic_exclusion S K h))

/-- The original reduced action lives on the literal component--Sylow join. -/
private theorem c124_join_preparation {κ : GroupClass.{u}}
    (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K)
    (hlocal : IsSQTK κ (Gv v))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hzOmega : z ∈ omegaOneCenterAmbient (Tv T v)) :
    ∃ P : Sylow 2 (K ⊔ Tv T v : Subgroup G),
      (P : Subgroup (K ⊔ Tv T v : Subgroup G)).map (K ⊔ Tv T v).subtype = Tv T v ∧
      IsSQTK κ (K ⊔ Tv T v : Subgroup G) ∧
      generalizedFitting (K ⊔ Tv T v : Subgroup G) = pCore 2 (K ⊔ Tv T v : Subgroup G) ∧
      generalizedFitting (K.subgroupOf (K ⊔ Tv T v)) = pCore 2 (K.subgroupOf (K ⊔ Tv T v)) ∧
      IsPReduced 2 ((WK K L T z v).subgroupOf (K ⊔ Tv T v)) ∧
      ⁅(WK K L T z v).subgroupOf (K ⊔ Tv T v), K.subgroupOf (K ⊔ Tv T v)⁆ ≠ ⊥ ∧
      (∀ g : (K ⊔ Tv T v : Subgroup G),
        ∃ k ∈ K.subgroupOf (K ⊔ Tv T v), ∃ t ∈ (P : Subgroup _), k * t = g) := by
  let H := K ⊔ Tv T v
  have hH : H ≤ Gv v := sup_le hK.1.1 inf_le_right
  have hsqH : IsSQTK κ H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hH)).mp (hlocal.subgroup (H.subgroupOf (Gv v)))
  obtain ⟨S, hS⟩ := hSylow
  have hSH : (S : Subgroup (Gv v)).map (Gv v).subtype ≤ H := hS ▸ le_sup_right
  have hchar : HasCharacteristicTwo (Gv v) := by
    change centralizer (pCore 2 (Gv v) : Set (Gv v)) ≤ pCore 2 (Gv v)
    rw [← hf]
    exact centralizer_generalizedFitting_le (Gv v)
  have hc : HasCharacteristicTwo (H.subgroupOf (Gv v)) :=
    centralizer_pCore_le_of_sylow_le S (H.subgroupOf (Gv v))
      (map_le_iff_le_comap.mp hSH) hchar
  have hfH : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (hc.of_equiv (subgroupOfEquivOfLe hH))
  have hfB : generalizedFitting (K.subgroupOf H) = pCore 2 (K.subgroupOf H) :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (subnormal_core_selfCentralizing ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfH)
        _ hK.1.2.1.subnormal)
  have hA : plusActor K L T v = H := by
    rw [plusActor, Kminus_eq_of_invariant K T v hn, sup_eq_left.mpr hLK]
  have hred : IsPReduced 2 ((WK K L T z v).subgroupOf H) := by
    exact (congrArg (fun A : Subgroup G => IsPReduced 2 ((WK K L T z v).subgroupOf A)) hA).mp
      (internalWK_reduced_source K L T z v hK.1.1 hL hz ⟨S,hS⟩ hzOmega hf)
  have hWH : WK K L T z v ≤ H := by
    have hh := (WK_mem_reducedFamily_source K L T z v hK.1.1 hL hz ⟨S,hS⟩ hzOmega hf).1
    exact hA ▸ hh
  have hm : ⁅(WK K L T z v).subgroupOf H, K.subgroupOf H⁆ ≠ ⊥ := by
    intro he
    have hm := congrArg (map H.subtype) he
    rw [map_commutator, map_subgroupOf_eq_of_le hWH,
      map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left), Subgroup.map_bot] at hm
    have hc : K ≤ centralizer (WK K L T z v : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hm)
    have hseed : K ≤ centralizer ({z} : Set G) := hc.trans
      (centralizer_le (Set.singleton_subset_iff.mpr (le_conjugateSpanBy _ _ (mem_zpowers z))))
    exact (invariant_component_consequences K L T z v hK hn).1.2
      ((starPreimage_starImage_centralizes_seed_iff z v K hK.1.1).mpr hseed)
  obtain ⟨P,hP⟩ := hK.1.2.2.1
  have hTP : (P : Subgroup H) = (Tv T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le (show Tv T v ≤ H from le_sup_right)]
  refine ⟨P,hP,hsqH,hfH,hfB,hred,hm,?_⟩
  intro g
  have hg : (g : G) ∈ (K : Set G) * (Tv T v : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left K (Tv T v) hn]
    exact g.property
  obtain ⟨k,hk,t,ht,hkt⟩ := Set.mem_mul.mp hg
  refine ⟨⟨k,(show K ≤ H from le_sup_left) hk⟩,hk,
    ⟨t,(show Tv T v ≤ H from le_sup_right) ht⟩,?_,Subtype.ext hkt⟩
  rw [hTP]
  exact ht

variable {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- The original strict normalizer theorem excludes C.1.24's nontrivial
characteristic Baumann subgroup on the literal selected Sylow carrier. -/
theorem baumann_characteristic_exclusion_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (P : Sylow 2 (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module) : Subgroup G))
    (hP : (P : Subgroup (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module) : Subgroup G)).map
      (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module)).subtype =
        Tv (T : Subgroup G) (markedV d.flag.module)) :
    ∀ C : Subgroup (ChapterB.baumann (P : Subgroup (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module) : Subgroup G))), C.Characteristic → C ≠ ⊥ →
      ¬ (C.map (ChapterB.baumann (P : Subgroup (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module) : Subgroup G))).subtype).Normal := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.flag.module))
      (Gv (markedV d.flag.module)) := ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  have hf := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hvT := d.V_le_T (map_mem d.flag.module
    (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v))
  have hv := (marked_orders d.flag.module).2
  have hv2 : markedV d.flag.module ^ 2 = 1 := by
    rw [← hv]
    exact pow_orderOf_eq_one _
  have hmove : ¬ K ≤ centralizer ({markedZ d.flag.module} : Set G) := by
    intro hc
    exact (invariant_component_consequences K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hK hn).1.2
      ((starPreimage_starImage_centralizes_seed_iff _ _ K hK.1.1).mpr hc)
  have h16 := (component_control_of_replacement_source T L standing h1332 h63
    (markedZ d.flag.module) (markedV d.flag.module) d.flag.z_central hvT
    (markedV_ne_one d.flag.module) hv2 hSylow d.flag_centralizer_index hf K hK.1 hn hmove).2.1
  exact baumann_characteristic_exclusion_of_obstruction _ _ h16 P hP

/-- The actual original reduced-module, characteristic-two and product
inputs of C.1.24, on the component--Sylow join. -/
theorem c124_join_preparation_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (model : RankTwo.ReducedModel (plusImage K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hL hz K)) :
    let s := d.flag.module
    let H := K ⊔ Tv (T : Subgroup G) (markedV s)
    let B := K.subgroupOf H
    let W := (WK K L (T : Subgroup G) (markedZ s) (markedV s)).subgroupOf H
    ∃ P : Sylow 2 H,
      (P : Subgroup H).map H.subtype = Tv (T : Subgroup G) (markedV s) ∧
      IsSQTK KnownSimple.IsKnownSimple H ∧
      generalizedFitting H = pCore 2 H ∧ generalizedFitting B = pCore 2 B ∧
      IsPReduced 2 W ∧ ⁅W,B⁆ ≠ ⊥ ∧
      (∀ g : H, ∃ k ∈ B, ∃ t ∈ (P : Subgroup H), k*t=g) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.flag.module))
      (Gv (markedV d.flag.module)) := ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  have hf := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hLK := (containment_and_noncontainment_original_source d V₃ earlier standing hm
    hfusion h1332 h63 hK hL hz model).1
  exact c124_join_preparation K L (T : Subgroup G) _ _ hK hn hLK
    (standing.qtke.involution_centralizer_sqtk (marked_orders d.flag.module).2)
    hSylow hf hL hz (markedZ_mem_Tv_omega d)

/-- The A₇ intrinsic quotient follows from the original plus marking;
the A.3.6 source input and the actual plus two-core are discharged. -/
theorem alternating_intrinsic_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (e : plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* alternatingGroup (Fin 7)) :
    IsQuasisimple (K ⧸ pCore 2 K) ∧
      Nonempty (((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃*
        alternatingGroup (Fin 7)) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.flag.module))
      (Gv (markedV d.flag.module)) := ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  have hR := SourceContainment.LinearThree.CentralAction.ModuleAlternatives.plus_twoCore_eq_bot
    K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)
    hK.1.1 hL hz hSylow
  exact AlternatingIntrinsic.intrinsic_quasisimple_and_central_quotient
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    K L (T : Subgroup G) _ _
    (standing.qtke.involution_centralizer_sqtk (marked_orders d.flag.module).2)
    hL hz hK hR e

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
