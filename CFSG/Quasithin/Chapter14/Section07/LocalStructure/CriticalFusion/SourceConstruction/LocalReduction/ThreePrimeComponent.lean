module
public import Theory.GroupTheory.CComponent.PrimeComplement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeExclusion
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.ThreeFree
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# A three-free component in the original local quotient

If O₃′(I/O₂(I)) is nontrivial, the already proved Fitting equality
extracts a genuine C-component there. The full known-simple A.3.6
classification identifies its actual carrier as a Suzuki group. Lift it
through the original quotient, retaining the intrinsic two-core kernel.
The normal-or-index-two component theorem also gives normality of its
Sylow conjugate span.

Source: Aschbacher–Smith, 14.7.7, printed p.1045, refs/quasithin.pdf;
1.2.1(3) and A.3.6 supply the component classification.
-/

public section
open Subgroup Theory.GroupTheory



namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

theorem local_star_sqtk
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    IsSQTK KnownSimple.IsKnownSimple (HStar I) := by
  have hne : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H :=
    ⟨F.Vi 1,hne,IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  have hIs := (IsSQTK.equiv (subgroupOfEquivOfLe hI.2.1)).mp
    ((h.source.simpleQTKE.twoLocal_sqtk hH).subgroup (I.subgroupOf F.H))
  exact ChapterE.Structure.sqtk_two_quotient hIs (pCore 2 I) pCore_isPGroup

theorem local_threePrime_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pPrimeCore 3 (HStar I) ≠ ⊥) :
    ∃ K : Subgroup I, K.IsCComponent ∧
      K.map (QuotientGroup.mk' (pCore 2 I)) ≤ pPrimeCore 3 (HStar I) ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp K.subtype).ker = pCore 2 K ∧
      ∃ m, 1 ≤ m ∧ Nonempty ((K ⧸ pCore 2 K) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  obtain ⟨B,hB,hBcore⟩ := exists_cComponent_le_primeComplement_of_fitting_isPGroup 3
    (local_fitting_isThreeGroup h hab structural previous faithful I hI) hne
  have h3 : ¬ 3 ∣ Nat.card B := by
    intro hd
    exact (Nat.prime_three.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)
      (hd.trans (card_dvd_of_le hBcore))
  have hc := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    (HStar I) (local_star_sqtk h I hI) (pCore_quotient_pCore_eq_bot 2) B hB
  obtain ⟨m,hm,⟨e⟩⟩ := hc.suzuki_of_three_free h3
  let : Group.IsNilpotent (pCore 2 I) := pCore_isPGroup.isNilpotent
  obtain ⟨K,hK,hKB⟩ := hB.exists_map_quotient_eq (pCore 2 I)
  refine ⟨K,hK,hKB.symm ▸ hBcore,?_,m,hm,?_⟩
  · rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hK.subnormal).symm
  · exact ⟨(cComponentTwoCoreQuotientEquiv hK).trans
      ((MulEquiv.subgroupCongr hKB).trans e)⟩

theorem local_component_sylow_span_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) :
    (conjugateSpanBy K ((T : Subgroup G).subgroupOf I)).Normal := by
  have hi := Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    (local_star_sqtk h I hI) hK
  have ho : K.Normal ∨ (normalizer (K : Set I)).index = 2 :=
    hi.imp_right And.left
  exact conjugateSpanBy_sylow_normal K (T.subtype (F.sylow_le_of_mem_Hz hI)) ho

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
