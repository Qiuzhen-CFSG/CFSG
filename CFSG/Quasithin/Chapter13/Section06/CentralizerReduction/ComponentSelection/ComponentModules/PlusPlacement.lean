module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PlusRank
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitComparison
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.LocalFacts
public import Theory.GroupTheory.TwoOrbitThree.Normalizer
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168

/-!
# The cubic residual in the actual component-pair image

The two conjugate plus components form a normal pair. The original source
models and the descended rank at three imply that this pair has index prime
to three. The cubic prime-to residual therefore maps into the pair. The final
theorem supplies every model and residual premise from the original 13.6.14
hypotheses, keeping the literal plus quotient and its quotient map.

Source: Aschbacher--Smith, 13.6.14, printed p.929, using the two-orbit
argument of 1.2.2(a), printed p.504.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem pslThreeTwo_outer_coprime {D : Type*} [Group D]
    (hm : ClassicalGroup.IsPSL D 3 2) :
    Nat.Coprime 3 (MulAut.innerSubgroup D).index := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let fe : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  let j := (e.trans (Atlas.fieldEquivPSL 3 fe)).trans
    Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.symm
  change Nat.Coprime 3 (Nat.card (MulAut.Outer D))
  rw [Nat.card_congr (MulAut.outerCongr j).toEquiv,Matrix.PSL3Two.Automorphisms.card_outer_sl]
  decide

/-- Source 1.2.2 on the actual plus pair requires only rank at three,
which is descended through the proved three-prime kernel. -/
theorem plus_pair_index_coprime_three_source
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G))
    (hd : 3 ∣ Nat.card (plusImage K L T z v hL hz K))
    (hm : (∃ F : ChapterB.QuasisimpleSource.BinaryField,
      Nonempty (plusImage K L T z v hL hz K ≃* SL(2,F.Carrier))) ∨
      ClassicalGroup.IsPSL (plusImage K L T z v hL hz K) 3 2) :
    Nat.Coprime 3 (plusImage K L T z v hL hz (Kminus K T v)).index := by
  obtain ⟨t,ht,htN,hpair,hdis,e,he⟩ := exists_plus_pair_coordinates_source
    K L T z v hlocal hL hz hSylow hK hn
  let A := plusImage K L T z v hL hz K
  let B := plusImage K L T z v hL hz (K.conjBy t)
  let P := plusImage K L T z v hL hz (Kminus K T v)
  let tA : plusActor K L T v := ⟨t,(show Tv T v ≤ plusActor K L T v from le_sup_right) ht⟩
  let tplus := plusMk K L T z v hL hz tA
  have hB : B = A.conjBy tplus :=
    plusImage_conjBy_source K L T K z v hL hz (K_le_plusActor K L T v) tA
  have hAcomp : IsComponent (Gplus K L T z v hL hz) A :=
    ⟨plusImage_K_subnormal K L T z v hL hz hK,
      plusImage_K_quasisimple_source K L T z v hL hz hK hSylow⟩
  have hBcomp : IsComponent (Gplus K L T z v hL hz) B := hB.symm ▸ hAcomp.map_conj tplus
  have hne : A ≠ B := plusImage_pair_ne_source K L T z v hlocal hL hz hK hn t ht htN
  have hcomm : ⁅A,A.conjBy tplus⁆ = ⊥ := by
    rw [← hB]
    exact hAcomp.commutator_eq_bot_of_ne hBcomp hne
  have hKmA : Kminus K T v ≤ plusActor K L T v := le_sup_left.trans le_sup_left
  have hCtA : K.conjBy t ≤ plusActor K L T v := (le_sup_right.trans hpair.ge).trans hKmA
  have hAP : A ⊔ A.conjBy tplus = P := by
    rw [← hB]
    dsimp only [P]
    rw [hpair,plusImage,subgroupOf_sup (K_le_plusActor K L T v) hCtA,Subgroup.map_sup]
    rfl
  let : P.Normal := plusImage_Kminus_normal_source K L T z v hL hz hK
  let : (A ⊔ A.conjBy tplus).Normal := hAP.symm ▸ inferInstance
  have hi := ComponentPairRankDescent.component_normalizer_index_two_of_normal_pair
    A hAcomp tplus (by rwa [← hB])
  let : IsSimpleGroup (K ⧸ pCore 2 K) :=
    noninvariant_component_core_simple_source K L T z v hlocal hK hn
  let : IsSimpleGroup A := (componentCoreEquivPlus K L T z v hlocal hL hz hSylow hK hn).symm.isSimpleGroup
  let := hAcomp.2
  have hZA : center A = ⊥ := by
    rcases (inferInstance : (center A).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp h)).elim
  have hr := plus_primeRank_three_le_two_of_pair K L T z v hlocal hL hz hSylow hK hn hd
  have hjoin : Nat.Coprime 3 (A ⊔ A.conjBy tplus).index := by
    rcases hm with ⟨F,⟨ef⟩⟩ | hm
    · exact TwoOrbitThree.binary_pair_index_coprime_three A hi tplus hcomm hZA hd hr F.Carrier
        (ef.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL)
    · exact TwoOrbitThree.outer_pair_index_coprime_three A hi tplus hcomm hZA hd hr
        (pslThreeTwo_outer_coprime hm)
  simpa only [hAP] using hjoin

omit [Finite G] in
/-- The source cubic residual lies in the literal component-pair image. -/
theorem plusLv_le_pair_of_index_coprime (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hindex : Nat.Coprime 3 (plusImage K L T z v hL hz (Kminus K T v)).index)
    (hc : primeToResidual 3 (Lv L v) = ⊤) :
    plusImage K L T z v hL hz (Lv L v) ≤ plusImage K L T z v hL hz (Kminus K T v) := by
  let P := plusImage K L T z v hL hz (Kminus K T v)
  let : P.Normal := plusImage_Kminus_normal_source K L T z v hL hz hK
  let f : Lv L v →* Gplus K L T z v hL hz :=
    (plusMk K L T z v hL hz).comp (inclusion (show Lv L v ≤ plusActor K L T v from le_sup_right.trans le_sup_left))
  have hk := primeToResidual_le_ker ((QuotientGroup.mk' P).comp f)
    (p := 3) (by rwa [← P.index_eq_card])
  rw [hc] at hk
  rintro x ⟨a,ha,rfl⟩
  have hh := hk (show (⟨a,ha⟩ : Lv L v) ∈ ⊤ from mem_top _)
  exact (QuotientGroup.eq_one_iff (f ⟨a,ha⟩)).mp hh

open A5Module ComponentReduction InitialSieve
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The original 13.6.14 source hypotheses imply the required placement in
the actual plus quotient, with no model or containment premise. -/
theorem plusLv_le_Kminus_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : ¬ Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G)) :
    plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz
      (Lv L (markedV d.flag.module)) ≤
    plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz
      (Kminus K (T : Subgroup G) (markedV d.flag.module)) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃ earlier hcounter hfusion
  have hmodels := noninvariant_component_models_original_source d V₃ earlier hG hm hcounter hfusion K hK hn hL hz
  have hmodel : (∃ F : ChapterB.QuasisimpleSource.BinaryField,
      Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz K ≃* SL(2,F.Carrier))) ∨
      ClassicalGroup.IsPSL (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz K) 3 2 := by
    rcases hmodels with ⟨F,_,_,he⟩ | ⟨_,he⟩
    · exact Or.inl ⟨F,he⟩
    · exact Or.inr he
  have hd := (orbit_plus_ff_model_original_source d V₃ earlier hG hm hcounter hfusion K hK hL hz).2
  have hi := plus_pair_index_coprime_three_source K L (T : Subgroup G) _ _
    (hG.involution_centralizer_sqtk (marked_orders d.flag.module).2) hL hz
    ⟨c.reductions.centralizerSylow,c.reductions.sylow_image⟩ hK hn hd hmodel
  exact plusLv_le_pair_of_index_coprime K L (T : Subgroup G) _ _ hL hz hK hi
    (SymmetricSix.lv_primeToResidual_eq_top d.flag.module c.residual_card)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
