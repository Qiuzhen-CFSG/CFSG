module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SourcePreparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixIntrinsic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.SourceClassifications

/-!
# The original nonlinear small quotients satisfy C.1.31

For the literal A₆, G₂(2)′ and covered-A₆ plus images, the three-rank
argument and A.3.6 make K/O₂(K) quasisimple. Its central quotient is
identified through the original K → K⁺ map, retaining the triple cover
in the covered-six case. Original 13.6.6 and 13.6.16 supply characteristic
two and MS3 in K Tᵥ. The Sylow subgroup supplies the proper odd-index
radical, and 13.6.14 supplies the literal product.

Thus the same complete C.1.32 input used in Chapter 15 applies to these
original Chapter 13 components. No whole-core or block assertion is
assumed here. Source: Aschbacher--Smith C.1.31--32 and 13.6.22, pp.135--136
and 932.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
open SourceTransferFields.HigherFieldParabolics
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The three nonlinear small plus quotients in original 13.6.22. -/
def NonlinearSmallQuotient (Q : Type*) [Group Q] : Prop :=
  Nonempty (Q ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) ∨
  Nonempty (Q ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
  Nonempty (Q ≃* Atlas.Codes.HexEvenAutomorphisms)

theorem NonlinearSmallQuotient.reduced {Q : Type*} [Group Q]
    (h : NonlinearSmallQuotient Q) : RankTwo.ReducedModel Q := by
  rcases h with h | h | h
  · exact .symplectic h
  · exact .g2 h
  · exact .ahat6 h

private theorem nonlinear_rank {Q : Type*} [Group Q] [Finite Q]
    (h : NonlinearSmallQuotient Q) : 2 ≤ primeRank 3 Q := by
  rcases h with h | h | h <;> obtain ⟨e⟩ := h
  · rw [primeRank_equiv 3 e]
    exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic
  · rw [primeRank_equiv 3 e]
    exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2
  · rw [primeRank_equiv 3 e]
    exact Representation.Hexacode.two_le_primeRank_even

private noncomputable def centerQuotientCongr {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro x hx
      exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)

/-- The covered-six row has the same central quotient as the six row,
without identifying either original full quotient with the other. -/
theorem NonlinearSmallQuotient.central_models {Q : Type*} [Group Q]
    (h : NonlinearSmallQuotient Q) :
    Nonempty ((Q ⧸ center Q) ≃* alternatingGroup (Fin 6)) ∨
    Nonempty ((Q ⧸ center Q) ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  rcases h with h | h | h <;> obtain ⟨e⟩ := h
  · let a := e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (by simp))
    exact Or.inl ⟨(centerQuotientCongr a).trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
        QuotientGroup.quotientBot)⟩
  · exact Or.inr ⟨(centerQuotientCongr e).trans
      ((QuotientGroup.quotientMulEquivOfEq Theory.SpecificGroups.g2_derived_two_center_eq_bot).trans
        QuotientGroup.quotientBot)⟩
  · exact Or.inl ⟨(centerQuotientCongr e).trans Representation.Hexacode.even_quotient_center_equiv⟩

variable {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- C.1.31 on the original component and its actual centralizer Sylow.
The central-core quotient is also returned, for comparison with every
outcome of C.1.32. -/
theorem smallMSPair_original_source
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
    (hmodel : NonlinearSmallQuotient (plusImage K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hL hz K)) :
    SmallMSPair KnownSimple.IsKnownSimple K (Tv (T : Subgroup G) (markedV d.flag.module)) ∧
      (Nonempty ((K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6)) ∨
       Nonempty ((K ⧸ centralPreimage (pCore 2 K)) ≃* commutator (Atlas.G2.Model (ZMod 2)))) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.flag.module))
      (Gv (markedV d.flag.module)) := ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  have hf := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hR := LinearThree.CentralAction.ModuleAlternatives.plus_twoCore_eq_bot
    K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)
    hK.1.1 hL hz hSylow
  have hr : primeRank 3 K = 2 := by
    have hu := (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hK.1.1)
      (inclusion_injective hK.1.1)).trans
        ((standing.qtke.involution_centralizer_sqtk (marked_orders d.flag.module).2).stronglyQuasithin
          3 (by decide) (by decide))
    by_contra hne
    let P : Sylow 3 K := Classical.choice inferInstance
    have hl := P.primeRank_le_one_of_surjective
      (P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega))
      (RankTwo.LocalApplication.toPlusImage K L (T : Subgroup G) _ _ hK.1.1 hL hz)
      (RankTwo.LocalApplication.toPlusImage_surjective K L (T : Subgroup G) _ _ hK.1.1 hL hz)
    have := nonlinear_rank hmodel
    omega
  let E := (centralPreimageQuotientEquiv (pCore 2 K)).trans
    (RankTwo.LocalApplication.intrinsicPlusCentralQuotientEquiv standing.qtke
      (ChapterA.SQTKStructure.a36Input_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
      K L (T : Subgroup G) _ _ (marked_orders d.flag.module).2 hK hr hL hz hR)
  have hcentral :
      Nonempty ((K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((K ⧸ centralPreimage (pCore 2 K)) ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
    rcases hmodel.central_models with h | h <;> obtain ⟨e⟩ := h
    · exact Or.inl ⟨E.trans e⟩
    · exact Or.inr ⟨E.trans e⟩
  obtain ⟨P,hP,hsq,hfit,_hfitK,_hred,_hmove,hprod⟩ :=
    c124_join_preparation_original_source d V₃ earlier standing hm hfusion h1332 h63
      hK hL hz hmodel.reduced
  have hvT := d.V_le_T (map_mem d.flag.module
    (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v))
  have hv := (marked_orders d.flag.module).2
  have hv2 : markedV d.flag.module ^ 2 = 1 := by
    rw [← hv]; exact pow_orderOf_eq_one _
  have hmove : ¬ K ≤ centralizer ({markedZ d.flag.module} : Set G) := by
    intro hc
    exact (invariant_component_consequences K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hK hn).1.2
      ((starPreimage_starImage_centralizes_seed_iff _ _ K hK.1.1).mpr hc)
  have h16 := (component_control_of_replacement_source T L standing h1332 h63
    (markedZ d.flag.module) (markedV d.flag.module) d.flag.z_central hvT
    (markedV_ne_one d.flag.module) hv2 hSylow d.flag_centralizer_index hf K hK.1 hn hmove).2.1
  refine ⟨{
    finite := inferInstance
    sqtk := hsq
    fitting := hfit
    product := ?_
    component := hK.1.2.1
    rankTwo := ?_
    radical := ?_
    characteristic := ?_ }, hcentral⟩
  · intro g hg
    obtain ⟨k,hk,t,ht,he⟩ := hprod ⟨g,hg⟩
    have ht' : (t : G) ∈ Tv (T : Subgroup G) (markedV d.flag.module) := by
      exact hP.le (mem_map_of_mem _ ht)
    exact ⟨k,hk,t,ht',congrArg Subtype.val he⟩
  · rcases hcentral with h | h
    · obtain ⟨e⟩ := h
      exact Or.inr (Or.inl ⟨e.trans
        (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)).symm⟩)
    · exact Or.inr (Or.inr h)
  · apply sylow_msOddIndex hK.1.2.2.1
    apply lt_of_le_not_ge le_sup_right
    intro hle
    have hp := (Chapter1.isSylowIn_iff.mp hK.1.2.2.1).1
    have hk : IsPGroup 2 (K.subgroupOf (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module))) :=
      (hp.to_le (le_sup_left.trans hle)).comap_subtype
    let := hk.isNilpotent
    exact hK.1.2.1.not_isSolvable inferInstance
  · intro C hC hnormal
    by_contra hne
    exact characteristic_exclusion _ _ h16 C hC hne hnormal

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132
