module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.NaturalRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.ExtraspecialCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSylowIrreducibility
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Source.Complete
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction
public import CFSG.Quasithin.Chapter1.Section03
public import Theory.GroupAction.NormalizerFrattiniTransport
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerPoint
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSixteenExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerKernel
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.GroupTheory.SylowNormalRestriction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerRanks
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.SpecificGroups.HeisenbergPrime.ElementaryPlane
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerComplement
public import Theory.GroupTheory.CentralSectionNormalComplement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerFrattini
public import Theory.SpecificGroups.HeisenbergPrime.TernaryOuterAction
public import Theory.SpecificGroups.GL2.ThreeQuaternionPullback
public import Theory.GroupTheory.RelativeSylowFrattini
public import Stellmacher.BaumannNormalizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerSylow
public import Theory.GroupTheory.NormalComplementSylowFactorization
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerSplit
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.SylowThreeCubic
public import Theory.GroupTheory.PCoreNormalizerAction.SylowKernel
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.GroupTheory.DetectedNormalCubic
public import Theory.GroupTheory.PPrimeCoreSubgroup
public import FeitThompson.BGsection1.PLengthLemmas
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerCubic
public import Theory.GroupTheory.Extraspecial27CubicRank
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.ConjugateSpanSupplement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerBaumann
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ThreeFree
public import Stellmacher.BaumannIntermediate
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerEquality
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms
public import Theory.SpecificGroups.PSL3Two.Parabolics.ResidualCommutator
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCentralFour
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.ExtraspecialSpan
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCentralCompletion
public import CFSG.Quasithin.ChapterI.Section06To08.Uniqueness
public import CFSG.Quasithin.ChapterI.Section06To08.TightPGroup.CyclicSpan
public import Theory.GroupAction.SmallQuotientCentralization
public import Theory.GroupTheory.FourGroupDisplacement

/-!
# Guarded extraspecial normalizer

This unit collects the indicated original source arguments at the same G,T.
Each constituent overview records its proof and source; the universal exports
remain unchanged. The larger unit avoids repeated loading of the common source
imports. Public mathematical statements and literal subgroup maps are retained.
-/

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The maximal-local overgroup of the original extraspecial residual

Transport the already proved irreducible Sylow action through the literal
K/O₂(K) comparison and its Frattini quotient. This puts K in the source
solvable uniqueness family Ξ. The complete intrinsic embedding theorem,
including its Held alternative, forces K to be normal in every maximal
two-local overgroup of H: every nonnormal alternative has an elementary
complement of order nine, whereas the original complement has order 27.
Local characteristic two and normalizer uniqueness then give N_G(K) as
the unique maximal two-local overgroup of H.

This proves 14.7.15(4), the first input to 14.7.21(1), with the original
quotient maps and relative normality. It does not yet identify N_G(K)
with H. The genuine earlier structural and faithful-classification inputs
retain their existing producers and final discharge at qt-d-14775-source.
Source: Aschbacher–Smith, refs/quasithin.pdf, printed pp.1047,1049–1050;
the embedding step uses 1.3.4 and the maximality argument of 1.3.7.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private def ExtraspecialNormalizer_residualFrattiniEquiv (F : InvariantFlag T V 3) :
    XiFrattiniQuotient (K F) ≃*
      ((pResidual 2 (HStar F.H)) ⧸ frattini (pResidual 2 (HStar F.H))) :=
  QuotientGroup.congr _ _ (residualStarEquiv F) (frattini_map_mulEquiv _)

private theorem ExtraspecialNormalizer_residualFrattiniEquiv_action
    (hn : (T : Subgroup G) ≤ normalizer (K F : Set G))
    (t : T) (x : XiFrattiniQuotient (K F)) :
    ExtraspecialNormalizer_residualFrattiniEquiv F (xiFrattiniAction (T : Subgroup G) (K F) hn t x) =
      quotientAut (frattini (pResidual 2 (HStar F.H)))
        (MulAut.conjNormal (starMap F ⟨t,F.invariant 1 t.property⟩))
        (ExtraspecialNormalizer_residualFrattiniEquiv F x) := by
  induction x using QuotientGroup.induction_on with | H x =>
    induction x using QuotientGroup.induction_on with | H k =>
      change ExtraspecialNormalizer_residualFrattiniEquiv F (xiFrattiniAction (T : Subgroup G) (K F) hn t
        (QuotientGroup.mk' _ (QuotientGroup.mk' _ k))) =
          quotientAut (frattini (pResidual 2 (HStar F.H)))
            (MulAut.conjNormal (starMap F ⟨t,F.invariant 1 t.property⟩))
            (ExtraspecialNormalizer_residualFrattiniEquiv F (QuotientGroup.mk' _ (QuotientGroup.mk' _ k)))
      simp only [xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk,
        ExtraspecialNormalizer_residualFrattiniEquiv,QuotientGroup.congr_mk']
      apply congrArg (QuotientGroup.mk' _)
      apply Subtype.ext
      rw [residualStarEquiv_mk]
      change starMap F _ = starMap F _ * (residualStarEquiv F _) * (starMap F _)⁻¹
      rw [residualStarEquiv_mk,←map_inv,←map_mul,←map_mul]
      congr 1

/-- The actual extraspecial residual belongs to the solvable uniqueness family. -/
theorem extraspecial_residual_mem_Xi
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    K F ∈ Xi G (T : Subgroup G) := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn : (T : Subgroup G) ≤ normalizer (K F : Set G) :=
    (F.invariant 1).trans (H_normalizes_K F)
  refine ⟨isPPerfect_embedded_pResidual 2 F.H,hn,?_,
    ⟨3,by decide,by decide,Or.inr ⟨hex,hcard,hexp⟩⟩,?_⟩
  · rw [←residual_product F]
    exact (F.H_mem_Hz (by decide) L (normalizer (L : Set G)) (h.flag_escape_at F previous)).1.1
  · intro A hA
    let eF := ExtraspecialNormalizer_residualFrattiniEquiv F
    have hinv : ∀ a : star F (T : Subgroup G), ∀ x ∈ A.map eF.toMonoidHom,
        quotientAut (frattini (pResidual 2 (HStar F.H)))
          (MulAut.conjNormal (a : HStar F.H)) x ∈ A.map eF.toMonoidHom := by
      intro a x hx
      obtain ⟨t,ht,heq⟩ := a.property
      obtain ⟨y,hy,rfl⟩ := hx
      have htT : (t : G) ∈ (T : Subgroup G) := ht
      rw [←heq]
      change quotientAut (frattini (pResidual 2 (HStar F.H)))
        (MulAut.conjNormal (starMap F ⟨(⟨t,htT⟩ : T),F.invariant 1 htT⟩))
        (ExtraspecialNormalizer_residualFrattiniEquiv F y) ∈ A.map eF.toMonoidHom
      rw [←ExtraspecialNormalizer_residualFrattiniEquiv_action hn ⟨t,htT⟩]
      exact mem_map_of_mem eF.toMonoidHom (hA ⟨t,htT⟩ y hy)
    rcases extraspecial_star_sylow_frattini_irreducible h hab structural previous faithful
        hex hcard hexp (A.map eF.toMonoidHom) hinv with hb | ht
    · left
      exact (map_eq_bot_iff_of_injective A eF.injective).mp hb
    · right
      have hh := congrArg (Subgroup.comap eF.toMonoidHom) ht
      simpa only [comap_map_eq_self_of_injective (f := eF.toMonoidHom) eF.injective,comap_top] using hh

/-- K is normal in every actual maximal two-local overgroup of H. -/
theorem extraspecial_residual_normal_in_maximal
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (M : Subgroup G) (hM : IsMaximalTwoLocal M) (hHM : F.H ≤ M) :
    ((K F).subgroupOf M).Normal := by
  have hX := extraspecial_residual_mem_Xi h hab structural previous faithful he
  have hTM := (F.invariant 1).trans hHM
  have hT : IsSylowIn 2 (T : Subgroup G) M := by
    refine ⟨T.subtype hTM,?_⟩
    simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]
  obtain ⟨e⟩ := he
  have hq : XiOddQuotient 3 (XiQuotient (K F)) := Or.inr
    ⟨(HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm,
      (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)),
      (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))⟩
  let b := XiEmbedding.localInput_of_mem_Xi hX hT
    ((residual_product F).symm.le.trans hHM) (by decide : Odd 3) hq (default : Sylow 3 (K F))
  rcases b.adequate_knownSimple (d.qtke.twoLocal_sqtk hM.1) hT with hn | ⟨J,_,_,_,ha⟩
  · exact hn
  · have hplane : Nonempty (((default : Sylow 3 (K F)) : Subgroup (K F)).map (K F).subtype ≃*
        XiEmbedding.Plane 3) := by
      rcases ha with ha | ha
      · exact ha.1
      · exact ha.2.1
    obtain ⟨ep⟩ := hplane
    have h27 : Nat.card (((default : Sylow 3 (K F)) : Subgroup (K F)).map (K F).subtype) = 27 :=
      (Nat.card_congr b.complementQuotientEquiv.toEquiv).trans
        ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
    have h9 := (Nat.card_congr ep.toEquiv).trans (XiEmbedding.plane_card 3)
    omega

/-- Source 14.7.15(4): N_G(K) is the unique maximal two-local containing H. -/
theorem extraspecial_residual_normalizer_unique
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    IsMaximalTwoLocal (normalizer (K F : Set G)) ∧
      {M : Subgroup G | IsMaximalTwoLocal M ∧ F.H ≤ M} = {normalizer (K F : Set G)} := by
  have hX := extraspecial_residual_mem_Xi h hab structural previous faithful he
  have hcore : (K F).pCoreIn 2 ≠ ⊥ := hX.pCoreIn_ne_bot
    (fun _ hM _ hN hNM hn => lemma_1_1_3_1 hM hN hNM hn)
    (lemma_1_1_4_6 T (d.qtke.evenCharacteristic T))
  have hh := Chapter1.Section03.normalizer_unique_of_normal_in_maximalTwoLocals
    (K F) (T : Subgroup G) hX.invariant
    (fun he => hcore (by change (pCore 2 (K F)).map (K F).subtype = ⊥; rw [he,Subgroup.map_bot]))
    (fun M hM hXM => extraspecial_residual_normal_in_maximal d h hab structural previous faithful
      he M hM ((residual_product F).le.trans hXM))
  simpa only [←residual_product F] using hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The point residual inside the maximal normalizer

The actual point image is the center of the star residual. Because
O₂(L₁) = O₂(K), it lifts to the full preimage of Z(K/O₂(K)) in K.
Consequently L₁ is characteristic in K, so N_G(K) normalizes L₁.
The maximal-local normalizer theorem and the nontrivial common two-core
then identify N_G(O₂(K)) = N_G(L₁) = N_G(K).

These are original-group inputs to the maximal-normalizer argument of
Aschbacher–Smith 14.7.21(1), printed pp.1049–1050, refs/quasithin.pdf.
No equality N_G(K) = H or final residual classification is asserted.
Every earlier source premise is retained for its existing assembly owner.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- L₁ is exactly the full central preimage in the original K/O₂(K). -/
theorem extraspecial_point_eq_central_preimage
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (F.Li L 1).subgroupOf (K F) =
      (center ((K F) ⧸ pCore 2 (K F))).comap (QuotientGroup.mk' (pCore 2 (K F))) := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hs := point_star_eq_center_of_extraspecial_residual h hab structural previous hex hcard hexp
  let A := (F.Li L 1).subgroupOf (K F)
  let q := QuotientGroup.mk' (pCore 2 (K F))
  let P := pResidual 2 (HStar F.H)
  let eK := residualStarEquiv F
  have himage : (A.map q).map eK.toMonoidHom = center P := by
    apply le_antisymm
    · rintro x ⟨y,⟨a,ha,rfl⟩,rfl⟩
      have hm : (eK (q a) : HStar F.H) ∈ star F (F.Li L 1) := by
        rw [residualStarEquiv_mk]
        exact mem_map_of_mem (starMap F) ha
      rw [hs] at hm
      obtain ⟨z,hz,hzx⟩ := hm
      exact (Subtype.ext hzx : z = eK (q a)) ▸ hz
    · intro x hx
      have hm : (x : HStar F.H) ∈ star F (F.Li L 1) := by
        rw [hs]
        exact mem_map_of_mem P.subtype hx
      obtain ⟨a,ha,haq⟩ := hm
      let k : K F := ⟨a,pointResidual_le F ha⟩
      refine ⟨q k,mem_map_of_mem q ha,?_⟩
      apply Subtype.ext
      change (residualStarEquiv F (QuotientGroup.mk' (pCore 2 (K F)) k) : HStar F.H) = x
      rw [residualStarEquiv_mk]
      exact haq
  have himageq : A.map q = center ((K F) ⧸ pCore 2 (K F)) := by
    apply map_injective (f := eK.toMonoidHom) eK.injective
    rw [himage]
    exact (Subgroup.center_map_equiv eK).symm
  have hker : q.ker ≤ A := by
    rw [QuotientGroup.ker_mk']
    intro k hk
    have hkP : (k : G) ∈ (K F).pCoreIn 2 := mem_map_of_mem (K F).subtype hk
    have hP : (F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2 :=
      (extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful ⟨e⟩).1
    exact pCoreIn_le 2 (F.Li L 1) (hP.symm ▸ hkP)
  have hh := congrArg (Subgroup.comap q) himageq
  simpa only [comap_map_eq,sup_eq_left.mpr hker] using hh

/-- The point residual is characteristic in K, hence normal in its full normalizer. -/
theorem extraspecial_point_characteristic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ((F.Li L 1).subgroupOf (K F)).Characteristic := by
  rw [extraspecial_point_eq_central_preimage h hab structural previous faithful he]
  exact Characteristic.comap_quotient_mk inferInstance

/-- The literal N_G(K) normalizes L₁ and its two-core. -/
theorem extraspecial_normalizer_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizer (K F : Set G) ≤ normalizer (F.Li L 1 : Set G) := by
  let := extraspecial_point_characteristic h hab structural previous faithful he
  simpa only [map_subgroupOf_eq_of_le (pointResidual_le F)] using
    normalizer_le_normalizer_characteristic_image (K F) ((F.Li L 1).subgroupOf (K F))

/-- The full residual, point residual and their common two-core have the
same maximal-local normalizer. -/
theorem extraspecial_core_normalizer_eq
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizer ((K F).pCoreIn 2 : Set G) = normalizer (K F : Set G) ∧
      normalizer (F.Li L 1 : Set G) = normalizer (K F : Set G) := by
  have hX := extraspecial_residual_mem_Xi h hab structural previous faithful he
  have hcore : (K F).pCoreIn 2 ≠ ⊥ := hX.pCoreIn_ne_bot
    (fun _ hM _ hN hNM hn => lemma_1_1_3_1 hM hN hNM hn)
    (lemma_1_1_4_6 T (d.qtke.evenCharacteristic T))
  have hmax := (extraspecial_residual_normalizer_unique d h hab structural previous faithful he).1
  have hNP : normalizer (K F : Set G) ≤ normalizer ((K F).pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F))
  have heq : normalizer ((K F).pCoreIn 2 : Set G) = normalizer (K F : Set G) :=
    (hmax.eq_of_le ⟨(K F).pCoreIn 2,hcore,isPGroup_pCoreIn 2 (K F),rfl⟩ hNP).symm
  refine ⟨heq,le_antisymm ?_ (extraspecial_normalizer_normalizes_point h hab structural previous faithful he)⟩
  have hP := (extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he).1
  rw [←heq,←hP]
  exact normalizer_le_normalizer_characteristic_image (F.Li L 1) (pCore 2 (F.Li L 1))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The literal point-centralizer kernel in the maximal normalizer

Write N = N_G(K), Y_K = C_N(L₁/O₂(L₁)), and C_K = C_N(K/O₂(K)).
These centralizers are kernels of the actual normalizer conjugation actions,
with their embedded images and relative normality retained. Comparing the
point action with the original star map gives T ∩ Y_K = R₁. The cubic
quotient has automorphism group of order two; the known index in T
therefore makes Y_K normal of index two in N, with Y_K T = N. Normal
Sylow restriction identifies the original R₁ as a Sylow subgroup of Y_K.
Finally O₂(L₁) = O₂(K) gives C_K ≤ Y_K.

The final theorem applies these deductions together with the maximal-local
normalizer and characteristic-point results to the original group and flag.
It supplies the opening inputs of Aschbacher–Smith 14.7.21(1), printed
pp.1049–1050, refs/quasithin.pdf. The proof that N_G(K) = H, the later
solvable/component exclusions and the final four-input assembly remain open.
Every genuine earlier source premise is retained for its existing producer.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem ExtraspecialNormalizerKernel_normalizerCore_le_sylow (H : Subgroup G) (hT : (T : Subgroup G) ≤ H) :
    H.pCoreIn 2 ≤ (T : Subgroup G) :=
  (pCoreIn_le_sylow H (T.subtype hT)).trans_eq (map_subgroupOf_eq_of_le hT)

omit [Finite G] in
private theorem ExtraspecialNormalizerKernel_pointAction_eq_one_iff_star
    (hn : F.H ≤ normalizer (F.Li L 1 : Set G)) (t : F.H) :
    pCoreNormalizerAction 2 (F.Li L 1) ⟨t,hn t.property⟩ = 1 ↔
      starMap F t ∈ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  let A := F.Li L 1
  have hAH : A ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hcore : A.pCoreIn 2 ≤ F.H.pCoreIn 2 := pCoreIn_mono_of_normalizes hAH hn
  rw [pCoreNormalizerAction_eq_one_iff]
  constructor
  · intro hfix x hx
    obtain ⟨a,ha,rfl⟩ := hx
    let aA : A := ⟨a,ha⟩
    have hh := hfix aA
    have hc : (t : G) * (a : G) * (t : G)⁻¹ / (a : G) ∈ F.H.pCoreIn 2 :=
      hcore (mem_map_of_mem A.subtype hh)
    have hc' : t * a * t⁻¹ / a ∈ pCore 2 F.H := by
      have hm : ((F.H.pCoreIn 2).subgroupOf F.H) = pCore 2 F.H :=
        comap_map_eq_self_of_injective F.H.subtype_injective _
      exact hm ▸ hc
    have hq : starMap F (t*a*t⁻¹/a) = 1 := (QuotientGroup.eq_one_iff _).mpr hc'
    rw [map_div,map_mul,map_mul,map_inv,div_eq_one] at hq
    have heq : starMap F t * starMap F a = starMap F a * starMap F t := by
      have hh := congrArg (fun z => z * starMap F t) hq
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
    exact heq.symm
  · intro hc a
    let aH : F.H := ⟨a,hAH a.property⟩
    have heq := hc (starMap F aH) (mem_map_of_mem (starMap F) a.property)
    have hq : starMap F (t*aH*t⁻¹/aH) = 1 := by
      rw [map_div,map_mul,map_mul,map_inv,←heq,mul_inv_cancel_right,div_self']
    have hk : t*aH*t⁻¹/aH ∈ pCore 2 F.H := (QuotientGroup.eq_one_iff _).mp hq
    let z := (F.Li L 1).normalizerMonoidHom ⟨t,hn t.property⟩ a / a
    have hz : (z : G) ∈ A.pCoreIn 2 :=
      inf_pCoreIn_le_of_le 2 hAH ⟨z.property,mem_map_of_mem F.H.subtype hk⟩
    have hm : (A.pCoreIn 2).subgroupOf A = pCore 2 A :=
      comap_map_eq_self_of_injective A.subtype_injective _
    exact hm ▸ hz

/-- Centralization of the literal point quotient inside N_G(K). -/
@[expose] def normalizerPointCentralizer (F : InvariantFlag T V 3) (L : Subgroup G) : Subgroup G :=
  normalizer (K F : Set G) ⊓
    (pCoreNormalizerAction 2 (F.Li L 1)).ker.map (normalizer (F.Li L 1 : Set G)).subtype

omit [Finite G] in
private theorem ExtraspecialNormalizerKernel_pointCentralizer_kernel
    (hn : normalizer (K F : Set G) ≤ normalizer (F.Li L 1 : Set G)) :
    normalizerPointCentralizer F L =
      ((pCoreNormalizerAction 2 (F.Li L 1)).comp (inclusion hn)).ker.map
        (normalizer (K F : Set G)).subtype := by
  ext x
  constructor
  · rintro ⟨hx,⟨a,ha,he⟩⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    change pCoreNormalizerAction 2 (F.Li L 1) (inclusion hn ⟨x,hx⟩) = 1
    have he' : a = inclusion hn ⟨x,hx⟩ := Subtype.ext he
    exact he' ▸ ha
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.property,⟨inclusion hn x,hx,rfl⟩⟩

/-- The point-centralizing normalizer meets the original T in precisely R₁. -/
theorem extraspecial_normalizer_point_sylow_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (T : Subgroup G) ⊓ normalizerPointCentralizer F L = F.Ri L 1 := by
  have hn := extraspecial_normalizer_normalizes_point h hab structural previous faithful he
  have hHN := H_normalizes_K F
  have hHA := hHN.trans hn
  have hnA : ((F.Li L 1).subgroupOf F.H).Normal := normal_subgroupOf_of_le_normalizer hHA
  have hstar := point_core_star_eq_centralizer_of_normal h structural hnA
  have hRH : F.Ri L 1 ≤ F.H := (pCoreIn_le 2 _).trans Rechoice.group_le_H
  have hRT : F.Ri L 1 ≤ (T : Subgroup G) := ExtraspecialNormalizerKernel_normalizerCore_le_sylow _ le_sup_right
  have hcore : F.H.pCoreIn 2 ≤ F.Ri L 1 := by
    have hQT := ExtraspecialNormalizerKernel_normalizerCore_le_sylow F.H (F.invariant 1)
    exact (le_inf (hQT.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 Rechoice.group_le_H)
  have hpre : (star F (F.Ri L 1)).comap (starMap F) = (F.Ri L 1).subgroupOf F.H := by
    change (((F.Ri L 1).subgroupOf F.H).map (starMap F)).comap (starMap F) = _
    rw [comap_map_eq,starMap,QuotientGroup.ker_mk']
    apply sup_eq_left.mpr
    intro x hx
    exact hcore (mem_map_of_mem F.H.subtype hx)
  rw [ExtraspecialNormalizerKernel_pointCentralizer_kernel hn]
  ext t
  constructor
  · rintro ⟨ht,⟨a,ha,heq⟩⟩
    let tH : F.H := ⟨t,F.invariant 1 ht⟩
    have htfix : pCoreNormalizerAction 2 (F.Li L 1) ⟨tH,hHA tH.property⟩ = 1 := by
      have hae : inclusion hn a = ⟨tH,hHA tH.property⟩ := Subtype.ext heq
      exact hae ▸ ha
    have hm : starMap F tH ∈ star F (F.Ri L 1) := by
      rw [hstar]
      exact ⟨mem_map_of_mem (starMap F) ht,(ExtraspecialNormalizerKernel_pointAction_eq_one_iff_star hHA tH).mp htfix⟩
    have hh : tH ∈ (star F (F.Ri L 1)).comap (starMap F) := hm
    rw [hpre] at hh
    exact hh
  · intro ht
    have htT := hRT ht
    let tH : F.H := ⟨t,hRH ht⟩
    have hm : starMap F tH ∈ star F (F.Ri L 1) := mem_map_of_mem (starMap F) ht
    have hc : starMap F tH ∈ centralizer (star F (F.Li L 1) : Set (HStar F.H)) :=
      (hstar ▸ hm).2
    exact ⟨htT,⟨⟨t,hHN tH.property⟩,(ExtraspecialNormalizerKernel_pointAction_eq_one_iff_star hHA tH).mpr hc,rfl⟩⟩

/-- Source 14.7.21: Y_K is normal of index two in N_G(K), and T supplements it. -/
theorem extraspecial_normalizer_point_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ((normalizerPointCentralizer F L).subgroupOf (normalizer (K F : Set G))).Normal ∧
      (normalizerPointCentralizer F L).relIndex (normalizer (K F : Set G)) = 2 ∧
      normalizerPointCentralizer F L ⊔ (T : Subgroup G) = normalizer (K F : Set G) := by
  let N := normalizer (K F : Set G)
  let Y := normalizerPointCentralizer F L
  have hn := extraspecial_normalizer_normalizes_point h hab structural previous faithful he
  let f := (pCoreNormalizerAction 2 (F.Li L 1)).comp (inclusion hn)
  have hY : Y = f.ker.map N.subtype := ExtraspecialNormalizerKernel_pointCentralizer_kernel hn
  have hYN : Y.subgroupOf N = f.ker := by
    rw [hY]
    exact comap_map_eq_self_of_injective N.subtype_injective _
  have hTN : (T : Subgroup G) ≤ N := (F.invariant 1).trans (H_normalizes_K F)
  have hnA : ((F.Li L 1).subgroupOf F.H).Normal :=
    normal_subgroupOf_of_le_normalizer ((H_normalizes_K F).trans hn)
  have hR : (F.Ri L 1).relIndex (T : Subgroup G) = 2 := by
    have hcore : pCore 2 F.H ≤ (F.Ri L 1).subgroupOf F.H := by
      intro x hx
      have hQT := ExtraspecialNormalizerKernel_normalizerCore_le_sylow F.H (F.invariant 1)
      exact inf_pCoreIn_le_of_le 2 Rechoice.group_le_H
        ⟨mem_sup_right (hQT (mem_map_of_mem F.H.subtype hx)),mem_map_of_mem F.H.subtype hx⟩
    have hcoreT : pCore 2 F.H ≤ (T : Subgroup G).subgroupOf F.H := by
      intro x hx
      exact ExtraspecialNormalizerKernel_normalizerCore_le_sylow F.H (F.invariant 1) (mem_map_of_mem F.H.subtype hx)
    have hh := point_core_star_index_two_of_normal h structural hnA
    change (((F.Ri L 1).subgroupOf F.H).map (starMap F)).relIndex
      (((T : Subgroup G).subgroupOf F.H).map (starMap F)) = 2 at hh
    rw [relIndex_map_map,starMap,QuotientGroup.ker_mk',sup_eq_left.mpr hcore,
      sup_eq_left.mpr hcoreT,relIndex_subgroupOf (show (T : Subgroup G) ≤ F.H from F.invariant 1)] at hh
    exact hh
  have hYT : Y.relIndex (T : Subgroup G) = 2 := by
    rw [←inf_relIndex_left,extraspecial_normalizer_point_sylow_intersection h hab structural previous faithful he]
    exact hR
  have hkt : f.ker.relIndex ((T : Subgroup G).subgroupOf N) = 2 := by
    rw [←hYN,relIndex_subgroupOf hTN]
    exact hYT
  have hc := pointResidual_core_quotient_card h structural (F := F)
  let : IsCyclic ((F.Li L 1) ⧸ pCore 2 (F.Li L 1)) := isCyclic_of_prime_card hc
  have hAut : Nat.card (MulAut ((F.Li L 1) ⧸ pCore 2 (F.Li L 1))) = 2 := by
    rw [IsCyclic.card_mulAut,hc]
    decide
  have hd : f.ker.index ∣ 2 := by
    rw [index_ker]
    simpa only [hAut] using f.range.card_subgroup_dvd_card
  have htwo : 2 ∣ f.ker.index := by
    simpa only [hkt] using relIndex_dvd_index_of_normal f.ker ((T : Subgroup G).subgroupOf N)
  have hi : f.ker.index = 2 := Nat.dvd_antisymm hd htwo
  have hindex : Y.relIndex N = 2 := by
    change (Y.subgroupOf N).index = 2
    rwa [hYN]
  have hnY : (Y.subgroupOf N).Normal := hYN ▸ inferInstanceAs f.ker.Normal
  refine ⟨hnY,hindex,?_⟩
  let := hnY
  have hYNle : Y ≤ N := inf_le_left
  have hjoin : Y ⊔ (T : Subgroup G) ≤ N := sup_le hYNle hTN
  have hrel : Y.relIndex (Y ⊔ (T : Subgroup G)) = 2 := by
    rw [←relIndex_subgroupOf hjoin,subgroupOf_sup hYNle hTN,relIndex_sup_left,
      relIndex_subgroupOf hTN,hYT]
  have hm := relIndex_mul_relIndex Y (Y ⊔ (T : Subgroup G)) N le_sup_left hjoin
  rw [hrel,hindex] at hm
  have h1 : (Y ⊔ (T : Subgroup G)).relIndex N = 1 := by omega
  exact le_antisymm hjoin (relIndex_eq_one.mp h1)

/-- R₁ is the literal Sylow two-subgroup in the point-centralizing normalizer. -/
theorem extraspecial_normalizer_point_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    IsSylowIn 2 (F.Ri L 1) (normalizerPointCentralizer F L) := by
  let N := normalizer (K F : Set G)
  let Y := normalizerPointCentralizer F L
  have hTN : (T : Subgroup G) ≤ N := (F.invariant 1).trans (H_normalizes_K F)
  have hYN : Y ≤ N := inf_le_left
  let := (extraspecial_normalizer_point_index h hab structural previous faithful he).1
  obtain ⟨S,hS⟩ := (T.subtype hTN).exists_sylow_map_eq_inf_of_normal (Y.subgroupOf N)
  let e := subgroupOfEquivOfLe hYN
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((S : Subgroup (Y.subgroupOf N)).map e.toMonoidHom).map Y.subtype = F.Ri L 1
  rw [map_map]
  have heq : Y.subtype.comp e.toMonoidHom = N.subtype.comp (Y.subgroupOf N).subtype := rfl
  rw [heq,←map_map,hS,Subgroup.map_inf _ _ N.subtype N.subtype_injective]
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN,map_subgroupOf_eq_of_le hYN]
  exact extraspecial_normalizer_point_sylow_intersection h hab structural previous faithful he

/-- The literal centralizer of K/O₂(K) in N_G(K). -/
@[expose] def normalizerResidualCentralizer (F : InvariantFlag T V 3) : Subgroup G :=
  (pCoreNormalizerAction 2 (K F)).ker.map (normalizer (K F : Set G)).subtype

/-- Centralization of the residual quotient implies centralization of the
point quotient, with the common two-core retained. -/
theorem extraspecial_normalizer_residualCentralizer_le_pointCentralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizerResidualCentralizer F ≤ normalizerPointCentralizer F L := by
  have hn := extraspecial_normalizer_normalizes_point h hab structural previous faithful he
  have hP := (extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he).1
  rintro x ⟨n,hnker,rfl⟩
  refine ⟨n.property,⟨inclusion hn n,?_,rfl⟩⟩
  change pCoreNormalizerAction 2 (F.Li L 1) (inclusion hn n) = 1
  rw [pCoreNormalizerAction_eq_one_iff]
  intro a
  let aK : K F := ⟨a,pointResidual_le F a.property⟩
  have hk := (pCoreNormalizerAction_eq_one_iff 2 (K F) n).mp hnker aK
  let z := (F.Li L 1).normalizerMonoidHom (inclusion hn n) a / a
  have hz : (z : G) ∈ (K F).pCoreIn 2 := mem_map_of_mem (K F).subtype hk
  rw [←hP] at hz
  have hc : ((F.Li L 1).pCoreIn 2).subgroupOf (F.Li L 1) = pCore 2 (F.Li L 1) :=
    comap_map_eq_self_of_injective (F.Li L 1).subtype_injective _
  exact hc ▸ hz

/-- Apply the normalizer construction to the original group and flag.
These are the opening normalizer inputs to 14.7.21(1), not its final equality H=N_G(K). -/
theorem extraspecial_normalizer_source_setup
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let N := normalizer (K F : Set G)
    let Y := normalizerPointCentralizer F L
    IsMaximalTwoLocal N ∧
      {M : Subgroup G | IsMaximalTwoLocal M ∧ F.H ≤ M} = {N} ∧
      normalizer ((K F).pCoreIn 2 : Set G) = N ∧
      normalizer (F.Li L 1 : Set G) = N ∧
      (Y.subgroupOf N).Normal ∧ Y.relIndex N = 2 ∧ Y ⊔ (T : Subgroup G) = N ∧
      (T : Subgroup G) ⊓ Y = F.Ri L 1 ∧ IsSylowIn 2 (F.Ri L 1) Y ∧
      normalizerResidualCentralizer F ≤ Y := by
  obtain ⟨hm,hu⟩ := extraspecial_residual_normalizer_unique d h hab structural previous faithful he
  obtain ⟨hp,ha⟩ := extraspecial_core_normalizer_eq d h hab structural previous faithful he
  obtain ⟨hn,hi,hgen⟩ := extraspecial_normalizer_point_index h hab structural previous faithful he
  exact ⟨hm,hu,hp,ha,hn,hi,hgen,
    extraspecial_normalizer_point_sylow_intersection h hab structural previous faithful he,
    extraspecial_normalizer_point_sylow h hab structural previous faithful he,
    extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Three-ranks in the original extraspecial normalizer

The elementary plane of K/O₂(K) lifts across its two-core, giving
m₃(K) ≥ 2. The original maximal two-local bound gives m₃(N_G(K)) = 2.
The literal action kernel C centralizes this quotient with cubic center,
so the residual-centralizer rank theorem bounds m₃(C) by one. Thus its
Sylow three-subgroups are cyclic.

Source: Aschbacher–Smith 14.7.21(1), printed p.1049. These are the
rank inputs for the subsequent normal-three-complement argument.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original extraspecial residual supplies two independent cubic directions. -/
theorem extraspecial_residual_threeRank_lower
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    2 ≤ primeRank 3 (K F) := by
  obtain ⟨e⟩ := he
  rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 (K F)) pCore_isPGroup,
    primeRank_congr 3 e]
  obtain ⟨E,hE,hc⟩ := HeisenbergPrime.exists_elementary_plane (by decide : 3 ≠ 2)
  let := hE
  exact IsElementaryAbelian.primeRank_ge_of_card E hc

/-- The maximal two-local has three-rank two, and its literal quotient-action
centralizer has three-rank at most one. No quotient-rank monotonicity is assumed. -/
theorem extraspecial_normalizer_threeRanks
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    primeRank 3 (normalizer (K F : Set G)) = 2 ∧
      primeRank 3 (normalizerResidualCentralizer F) ≤ 1 := by
  let N := normalizer (K F : Set G)
  let C := normalizerResidualCentralizer F
  have hn := (extraspecial_residual_normalizer_unique d h hab structural previous faithful he).1
  have hr : primeRank 3 N ≤ 2 := (d.qtke.twoLocal_sqtk hn.1).stronglyQuasithin 3 (by decide) (by decide)
  have hK := extraspecial_residual_threeRank_lower he
  have hlo := (primeRank_le_of_injective 3 (inclusion (K F).le_normalizer)
    (inclusion_injective (K F).le_normalizer))
  change primeRank 3 (K F) ≤ primeRank 3 N at hlo
  have hrN : primeRank 3 N = 2 := by omega
  refine ⟨hrN,?_⟩
  have hCN : C ≤ N := map_subtype_le _
  have hc : ⁅K F,C⁆ ≤ (K F).pCoreIn 2 := by
    apply commutator_le_core_of_pCoreNormalizerAction_eq_one 2 (K F) C hCN
    rintro ⟨c,⟨n,hn,rfl⟩⟩
    exact hn
  have hcomm : ⁅(pResidual 2 C).map C.subtype,K F⁆ ≤ (K F).pCoreIn 2 := by
    rw [commutator_comm] at hc
    exact (commutator_mono (map_subtype_le _) le_rfl).trans hc
  obtain ⟨e⟩ := he
  have hz : Nat.card (center ((K F) ⧸ pCore 2 (K F))) ≤ 3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv,HeisenbergPrime.card_center]
  have hCK : C ⊔ K F ≤ N := sup_le hCN (K F).le_normalizer
  exact Theory.GroupTheory.ResidualCentralizerRank.three_rank_le_one_of_normalized_factor_cubic_center
    C (K F) hCN hcomm hz hK
    ((primeRank_le_of_injective 3 (inclusion hCK) (inclusion_injective hCK)).trans hr)

/-- Every three-Sylow of the actual residual centralizer is cyclic. -/
theorem extraspecial_normalizer_centralizer_sylow_cyclic
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (S : Sylow 3 (normalizerResidualCentralizer F)) : IsCyclic S :=
  S.isCyclic_of_odd_of_primeRank_le_one (by decide)
    (extraspecial_normalizer_threeRanks d h hab structural previous faithful he).2

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The normal three-complement in the original centralizer product

For C = C_N(K/O₂(K)), the central preimage L₁ lies in C. Every three-Sylow
of C R₁ lies in C because the quotient by C is a two-group; the previously
proved three-rank bound therefore makes it cyclic. The literal point-action
kernel gives [L₁,C R₁] ≤ O₂(L₁), and L₁/O₂(L₁) has order three.
Burnside transfer supplies a normal three-complement in C R₁.

All subgroups and quotient maps belong to the original group and flag.
No normality of C R₁ in N_G(K) is used or asserted.
Source: Aschbacher–Smith 14.7.21(1), printed p.1049, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The central preimage L₁ acts trivially on the original residual quotient. -/
theorem extraspecial_point_le_residualCentralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    F.Li L 1 ≤ normalizerResidualCentralizer F := by
  intro a ha
  let k : K F := ⟨a,pointResidual_le F ha⟩
  have hz : QuotientGroup.mk' (pCore 2 (K F)) k ∈ center _ := by
    change k ∈ (center _).comap (QuotientGroup.mk' (pCore 2 (K F)))
    rw [←extraspecial_point_eq_central_preimage h hab structural previous faithful he]
    exact ha
  refine ⟨⟨a,(K F).le_normalizer k.property⟩,?_,rfl⟩
  change pCoreNormalizerAction 2 (K F) ⟨k,(K F).le_normalizer k.property⟩ = 1
  rw [pCoreNormalizerAction_on_component]
  apply MulEquiv.ext
  intro x
  change QuotientGroup.mk' (pCore 2 (K F)) k * x * _ = x
  rw [←(mem_center_iff.mp hz x),mul_assoc,mul_inv_cancel,mul_one]

omit [Finite G] in
/-- The literal residual kernel is normal in its full normalizer. -/
theorem normalizerResidualCentralizer_normalizes :
    normalizer (K F : Set G) ≤ normalizer (normalizerResidualCentralizer F : Set G) := by
  let N := normalizer (K F : Set G)
  have hn : ((normalizerResidualCentralizer F).subgroupOf N).Normal := by
    change (((pCoreNormalizerAction 2 (K F)).ker.map N.subtype).comap N.subtype).Normal
    rw [comap_map_eq_self_of_injective N.subtype_injective]
    infer_instance
  exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp hn

/-- A three-Sylow of C_K R₁ is cyclic, with its literal containment in C_K. -/
theorem extraspecial_centralizer_point_sylow_cyclic
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (S : Sylow 3 (normalizerResidualCentralizer F ⊔ F.Ri L 1 : Subgroup G)) :
    (S : Subgroup _).map (normalizerResidualCentralizer F ⊔ F.Ri L 1).subtype ≤
      normalizerResidualCentralizer F ∧ IsCyclic S := by
  let C := normalizerResidualCentralizer F
  let R := F.Ri L 1
  let D := C ⊔ R
  have hRY := (isSylowIn_iff.mp (extraspecial_normalizer_point_sylow h hab structural previous faithful he)).2.1
  have hDY : D ≤ normalizerPointCentralizer F L := sup_le
    (extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he) hRY
  let C' := C.subgroupOf D
  let R' := R.subgroupOf D
  have hDC : D ≤ normalizer (C : Set G) :=
    (hDY.trans inf_le_left).trans normalizerResidualCentralizer_normalizes
  let : C'.Normal := normal_subgroupOf_of_le_normalizer hDC
  have hgen : C' ⊔ R' = ⊤ := by
    rw [←subgroupOf_sup (show C ≤ D from le_sup_left) (show R ≤ D from le_sup_right)]
    exact subgroupOf_self D
  have hidx : ¬ 3 ∣ C'.index := by
    have hi : C'.index ∣ Nat.card R' := by
      rw [←relIndex_top_right (H := C'),←hgen,relIndex_sup_left]
      exact relIndex_dvd_card _ _
    have hR2 : IsPGroup 2 R' :=
      (isPGroup_pCoreIn 2 _).of_equiv (subgroupOfEquivOfLe (show R ≤ D from le_sup_right)).symm
    obtain ⟨k,hk⟩ := hR2.exists_card_eq
    intro hh
    have hh' : 3 ∣ 2^k := hk ▸ hh.trans hi
    exact ((show Nat.Prime 3 by decide).coprime_iff_not_dvd.mp
      ((by decide : Nat.Coprime 3 2).pow_right k)) hh'
  have hSC : (S : Subgroup D) ≤ C' := by
    rw [←relIndex_eq_one]
    obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
    have hcop : Nat.Coprime C'.index (Nat.card S) := hk ▸
      ((show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr hidx).symm.pow_right k
    exact Nat.eq_one_of_dvd_coprimes hcop (C'.relIndex_dvd_index_of_normal _)
      (relIndex_dvd_card _ _)
  refine ⟨?_,?_⟩
  · rintro x ⟨s,hs,rfl⟩
    exact hSC hs
  · have hr : primeRank 3 C' ≤ 1 := by
      rw [primeRank_congr 3 (subgroupOfEquivOfLe (show C ≤ D from le_sup_left))]
      exact (extraspecial_normalizer_threeRanks d h hab structural previous faithful he).2
    have hc : IsCyclic (S.subtype hSC) :=
      (S.subtype hSC).isCyclic_of_odd_of_primeRank_le_one (by decide) hr
    exact (subgroupOfEquivOfLe hSC).isCyclic.mp hc

/-- Burnside's normal three-complement conclusion for the actual C_K R₁. -/
theorem extraspecial_centralizer_point_normal_complement
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    HasNormalPComplement 3 (normalizerResidualCentralizer F ⊔ F.Ri L 1 : Subgroup G) := by
  let C := normalizerResidualCentralizer F
  let R := F.Ri L 1
  let D := C ⊔ R
  let A := F.Li L 1
  let Q := A.pCoreIn 2
  have hAD : A ≤ D :=
    (extraspecial_point_le_residualCentralizer h hab structural previous faithful he).trans le_sup_left
  have hDY : D ≤ normalizerPointCentralizer F L := sup_le
    (extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he)
    (isSylowIn_iff.mp (extraspecial_normalizer_point_sylow h hab structural previous faithful he)).2.1
  have hDA : D ≤ normalizer (A : Set G) := (hDY.trans inf_le_left).trans
    (extraspecial_normalizer_normalizes_point h hab structural previous faithful he)
  let : (A.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer hDA
  have hpA : 3 ∣ Nat.card (A.subgroupOf D) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv]
    exact (pointResidual_core_quotient_card h structural).symm ▸
      (pCore 2 A).index_dvd_card
  have hpQ : Nat.Coprime 3 (Nat.card (Q.subgroupOf D)) := by
    have hQ2 : IsPGroup 2 (Q.subgroupOf D) := (isPGroup_pCoreIn 2 A).of_equiv
      (subgroupOfEquivOfLe ((pCoreIn_le 2 A).trans hAD)).symm
    obtain ⟨k,hk⟩ := hQ2.exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hcomm : ⁅A,D⁆ ≤ Q := by
    apply commutator_le_core_of_pCoreNormalizerAction_eq_one 2 A D hDA
    intro x
    obtain ⟨a,ha,heq⟩ := (hDY x.property).2
    exact (show a = inclusion hDA x from Subtype.ext heq) ▸ ha
  have hcomm' : ⁅A.subgroupOf D,(⊤ : Subgroup D)⁆ ≤ Q.subgroupOf D := by
    apply (map_le_map_iff_of_injective D.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hAD,←MonoidHom.range_eq_map,D.range_subtype,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 A).trans hAD)]
    exact hcomm
  obtain ⟨S⟩ := Sylow.nonempty (p := 3) (G := D)
  let := (extraspecial_centralizer_point_sylow_cyclic d h hab structural previous faithful he S).2
  exact S.hasNormalPComplement_of_cyclic_of_central_section
    (A.subgroupOf D) (Q.subgroupOf D) hpA hpQ hcomm'

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end



/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The inner kernel in the extraspecial normalizer

The original residual action on its Heisenberg quotient induces a GL₂(3)
action. Its determinant-one preimage is the literal point centralizer.
Pulling back the normal quaternion subgroup gives K C R₁, retaining the
inner automorphisms in the kernel. Relative Frattini then gives
N_G(K) = K C N_{N_G(K)}(R₁); original 14.7.16(7) places the last
factor in N_G(L).

Source: Aschbacher–Smith 14.7.21(1), printed pp.1049–1050. This repairs
the outer-action normality step; it does not assert normality of C R₁,
a normal three-complement, or the final equality N_G(K) = H.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem ExtraspecialNormalizerFrattini_point_center_action_iff
    (hn : normalizer (K F : Set G) ≤ normalizer (F.Li L 1 : Set G))
    (hP : (F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2)
    (hZ : (F.Li L 1).subgroupOf (K F) =
      (center ((K F) ⧸ pCore 2 (K F))).comap (QuotientGroup.mk' (pCore 2 (K F))))
    (n : normalizer (K F : Set G)) :
    pCoreNormalizerAction 2 (F.Li L 1) (inclusion hn n) = 1 ↔
      ∀ z ∈ center ((K F) ⧸ pCore 2 (K F)), pCoreNormalizerAction 2 (K F) n z = z := by
  rw [pCoreNormalizerAction_eq_one_iff]
  let q := QuotientGroup.mk' (pCore 2 (K F))
  have hmemA (a : F.Li L 1) : q ⟨a,pointResidual_le F a.property⟩ ∈ center _ := by
    change (⟨a,pointResidual_le F a.property⟩ : K F) ∈ (center _).comap q
    rw [←hZ]
    exact a.property
  constructor
  · intro hh z hz
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (K F)) z
    have hk : (k : G) ∈ F.Li L 1 := by
      change k ∈ (F.Li L 1).subgroupOf (K F)
      rw [hZ]
      exact hz
    let a : F.Li L 1 := ⟨k,hk⟩
    rw [pCoreNormalizerAction_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hd : ((F.Li L 1).normalizerMonoidHom (inclusion hn n) a / a : G) ∈
        (K F).pCoreIn 2 := hP ▸ mem_map_of_mem (F.Li L 1).subtype (hh a)
    have he : ((K F).pCoreIn 2).subgroupOf (K F) = pCore 2 (K F) :=
      comap_map_eq_self_of_injective (K F).subtype_injective _
    exact he ▸ hd
  · intro hh a
    let k : K F := ⟨a,pointResidual_le F a.property⟩
    have he := hh (q k) (hmemA a)
    rw [pCoreNormalizerAction_mk] at he
    have hd := QuotientGroup.eq_iff_div_mem.mp he
    have hd' : ((K F).normalizerMonoidHom n k / k : G) ∈ (F.Li L 1).pCoreIn 2 :=
      hP.symm ▸ mem_map_of_mem (K F).subtype hd
    have he' : ((F.Li L 1).pCoreIn 2).subgroupOf (F.Li L 1) = pCore 2 (F.Li L 1) :=
      comap_map_eq_self_of_injective (F.Li L 1).subtype_injective _
    exact he' ▸ hd'

/-- The point centralizer is exactly the determinant-one preimage for the
marked outer action on the original residual. -/
theorem extraspecial_normalizer_point_outer_preimage
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : ((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3) :
    (normalizerPointCentralizer F L).subgroupOf (normalizer (K F : Set G)) =
      Matrix.GeneralLinearGroup.threeSpecialLinear.comap
        ((HeisenbergPrime.TernaryOuterAction.markedAction e).comp
          (pCoreNormalizerAction 2 (K F))) := by
  have hn := extraspecial_normalizer_normalizes_point h hab structural previous faithful ⟨e⟩
  have hP := (extraspecial_centralizer_core_reduction_no_small_intervals
    h hab structural previous faithful ⟨e⟩).1
  have hZ := extraspecial_point_eq_central_preimage h hab structural previous faithful ⟨e⟩
  ext n
  change (n : G) ∈ normalizerPointCentralizer F L ↔ _
  rw [mem_comap,MonoidHom.comp_apply,HeisenbergPrime.TernaryOuterAction.markedAction_mem_special_iff,
    ←ExtraspecialNormalizerFrattini_point_center_action_iff hn hP hZ n]
  constructor
  · rintro ⟨_,⟨a,ha,he⟩⟩
    exact (show a = inclusion hn n from Subtype.ext he) ▸ ha
  · intro hh
    exact ⟨n.property,⟨inclusion hn n,hh,rfl⟩⟩

/-- The exact quaternion preimage in the original normalizer includes both K and C_K. -/
theorem extraspecial_normalizer_quaternion_preimage
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : ((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3) :
    (Matrix.GeneralLinearGroup.threeQuaternion.comap
      ((HeisenbergPrime.TernaryOuterAction.markedAction e).comp
        (pCoreNormalizerAction 2 (K F)))).map (normalizer (K F : Set G)).subtype =
      K F ⊔ normalizerResidualCentralizer F ⊔ F.Ri L 1 := by
  let N := normalizer (K F : Set G)
  let Y := normalizerPointCentralizer F L
  let a := pCoreNormalizerAction 2 (K F)
  let f := (HeisenbergPrime.TernaryOuterAction.markedAction e).comp a
  have hY := extraspecial_normalizer_point_outer_preimage h hab structural previous faithful e
  have hk : f.ker = (K F).subgroupOf N ⊔ a.ker := by
    rw [show f.ker = (HeisenbergPrime.TernaryOuterAction.markedAction e).ker.comap a from rfl,
      HeisenbergPrime.TernaryOuterAction.markedAction_ker,
      ←pCoreNormalizerAction_component_image,comap_map_eq]
  have hYN : Y ≤ N := inf_le_left
  obtain ⟨S,hS⟩ := extraspecial_normalizer_point_sylow h hab structural previous faithful ⟨e⟩
  let ey : Y ≃* Matrix.GeneralLinearGroup.threeSpecialLinear.comap f :=
    (subgroupOfEquivOfLe hYN).symm.trans (MulEquiv.subgroupCongr hY)
  let S' := S.mapSurjective (f := ey.toMonoidHom) ey.surjective
  have hD := Matrix.GeneralLinearGroup.quaternion_preimage_eq_sylow_sup_kernel f S'
  have hDm := congrArg (Subgroup.map N.subtype) hD
  have hSm : (((S' : Subgroup (Matrix.GeneralLinearGroup.threeSpecialLinear.comap f)).map
      (Matrix.GeneralLinearGroup.threeSpecialLinear.comap f).subtype).map N.subtype) = F.Ri L 1 := by
    change (((S : Subgroup Y).map ey.toMonoidHom).map _).map _ = _
    rw [map_map,map_map]
    exact hS
  rw [Subgroup.map_sup,hSm,hk,Subgroup.map_sup,map_subgroupOf_eq_of_le (K F).le_normalizer] at hDm
  simpa only [normalizerResidualCentralizer,sup_assoc,sup_comm,sup_left_comm] using hDm

/-- The corrected normal subgroup lies in the original point centralizer,
and R₁ is its Sylow two-subgroup. -/
theorem extraspecial_normalizer_inner_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let B := K F ⊔ normalizerResidualCentralizer F ⊔ F.Ri L 1
    (B.subgroupOf (normalizer (K F : Set G))).Normal ∧
      B ≤ normalizerPointCentralizer F L ∧ IsSylowIn 2 (F.Ri L 1) B := by
  obtain ⟨e⟩ := he
  let N := normalizer (K F : Set G)
  let f := (HeisenbergPrime.TernaryOuterAction.markedAction e).comp
    (pCoreNormalizerAction 2 (K F))
  let D := Matrix.GeneralLinearGroup.threeQuaternion.comap f
  have hd := extraspecial_normalizer_quaternion_preimage h hab structural previous faithful e
  have hn : ((D.map N.subtype).subgroupOf N).Normal := by
    rw [show (D.map N.subtype).subgroupOf N = D from
      comap_map_eq_self_of_injective N.subtype_injective D]
    infer_instance
  have hle : D.map N.subtype ≤ normalizerPointCentralizer F L := by
    have hm := map_mono (f := N.subtype)
      (comap_mono (f := f) Matrix.GeneralLinearGroup.threeQuaternion_le_specialLinear)
    rw [←extraspecial_normalizer_point_outer_preimage h hab structural previous faithful e,
      map_subgroupOf_eq_of_le (show normalizerPointCentralizer F L ≤ N from inf_le_left)] at hm
    exact hm
  rw [hd] at hn hle
  exact ⟨hn,hle,(extraspecial_normalizer_point_sylow h hab structural previous faithful ⟨e⟩).restrict
    le_sup_right hle⟩

/-- Frattini factorization in the original normalizer with the full inner kernel retained. -/
theorem extraspecial_normalizer_inner_frattini
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    K F ⊔ normalizerResidualCentralizer F ⊔
      (normalizer (K F : Set G) ⊓ normalizer (F.Ri L 1 : Set G)) =
        normalizer (K F : Set G) := by
  let N := normalizer (K F : Set G)
  let B := K F ⊔ normalizerResidualCentralizer F ⊔ F.Ri L 1
  obtain ⟨hn,hBY,hs⟩ := extraspecial_normalizer_inner_sylow h hab structural previous faithful he
  have hBN : B ≤ N := hBY.trans inf_le_left
  have hNB : N ≤ normalizer (B : Set G) := (normal_subgroupOf_iff_le_normalizer hBN).mp hn
  obtain ⟨S,hS⟩ := hs
  have hgen := relative_sylow_frattini B N hBN hNB S
  rw [hS] at hgen
  have hR : F.Ri L 1 ≤ N ⊓ normalizer (F.Ri L 1 : Set G) :=
    le_inf (le_sup_right.trans hBN) (F.Ri L 1).le_normalizer
  change (K F ⊔ normalizerResidualCentralizer F ⊔ F.Ri L 1) ⊔ _ = N at hgen
  rwa [sup_assoc (K F ⊔ normalizerResidualCentralizer F),sup_eq_right.mpr hR] at hgen

/-- The normalizer factor in the repaired Frattini product is controlled by
original 14.7.16(7), via the characteristic Baumann subgroup of R₁. -/
theorem extraspecial_normalizer_inner_frattini_source
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let N := normalizer (K F : Set G)
    let M₁ := N ⊓ normalizer (F.Ri L 1 : Set G)
    K F ⊔ normalizerResidualCentralizer F ⊔ M₁ = N ∧
      M₁ ≤ normalizer (L : Set G) := by
  refine ⟨extraspecial_normalizer_inner_frattini h hab structural previous faithful he,?_⟩
  exact inf_le_right.trans ((Stellmacher.normalizer_le_normalizer_baumann _).trans
    (extraspecial_baumann_normalizer d h hab structural previous earlier he))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original Sylow factorization with the inner kernel retained

The normal three-complement of C_K R₁ allows a three-Sylow of C_K to
be chosen inside N_{C_K R₁}(R₁). Extend it inside M₁ = N_N(R₁), where
N = N_G(K). Since K and C_K are normal in N and N = K C_K M₁,
normal-product Sylow indices give a Sylow B of N with the exact product
B = B_K B_M, where B_K = B ∩ K and B_M = N_B(R₁). Moreover
B ∩ C_K ≤ B_M. The original Baumann-normalizer theorem places B_M
in N_G(L).

This proves the normal-complement/Frattini step in Aschbacher–Smith
14.7.21(1), printed pp.1049–1050, with the full inner-action kernel
retained. The later m₃ contradiction, centralizer control and N = H
remain separate source obligations; no conclusion record is assumed.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Choose a three-Sylow of C_K in the literal R₁ normalizer. -/
theorem extraspecial_centralizer_sylow_in_point_normalizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ S : Sylow 3 (normalizerResidualCentralizer F),
      (S : Subgroup _).map (normalizerResidualCentralizer F).subtype ≤
        normalizer (K F : Set G) ⊓ normalizer (F.Ri L 1 : Set G) := by
  let C := normalizerResidualCentralizer F
  let D := C ⊔ F.Ri L 1
  have hDY : D ≤ normalizerPointCentralizer F L := sup_le
    (extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he)
    (isSylowIn_iff.mp (extraspecial_normalizer_point_sylow h hab structural previous faithful he)).2.1
  obtain ⟨R,hR⟩ := (extraspecial_normalizer_point_sylow h hab structural previous faithful he).restrict
    (show F.Ri L 1 ≤ D from le_sup_right) hDY
  obtain ⟨S,hS⟩ := R.exists_le_normalizer_of_normal_complement (by decide : 3 ≠ 2)
    (extraspecial_centralizer_point_normal_complement d h hab structural previous faithful he)
  have hSC := (extraspecial_centralizer_point_sylow_cyclic d h hab structural previous faithful he S).1
  obtain ⟨S',hS'⟩ := (show IsSylowIn 3 ((S : Subgroup D).map D.subtype) D from ⟨S,rfl⟩).restrict
    hSC le_sup_left
  refine ⟨S',?_⟩
  rw [hS']
  refine le_inf ((map_subtype_le _).trans (hDY.trans inf_le_left)) ?_
  have hn := (map_mono hS).trans ((R : Subgroup D).le_normalizer_map D.subtype)
  rwa [hR] at hn

/-- The repaired Sylow factorization in the original normalizer, together
with the actual Baumann-normalizer containment of its second factor. -/
theorem extraspecial_normalizer_three_sylow_factorization
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ B : Sylow 3 (normalizer (K F : Set G)),
      let B₀ := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
      let B_K := B₀ ⊓ K F
      let B_M := B₀ ⊓ normalizer (F.Ri L 1 : Set G)
      B₀ = B_K ⊔ B_M ∧ (B₀ : Set G) = (B_K : Set G) * (B_M : Set G) ∧
        B₀ ⊓ normalizerResidualCentralizer F ≤ B_M ∧
        B_M ≤ normalizer (L : Set G) := by
  let N := normalizer (K F : Set G)
  let C := normalizerResidualCentralizer F
  let M := N ⊓ normalizer (F.Ri L 1 : Set G)
  have hKN : K F ≤ N := (K F).le_normalizer
  have hCN : C ≤ N := map_subtype_le _
  have hMN : M ≤ N := inf_le_left
  let K' := (K F).subgroupOf N
  let C' := C.subgroupOf N
  let M' := M.subgroupOf N
  let : K'.Normal := normal_subgroupOf_of_le_normalizer (le_rfl : N ≤ normalizer (K F : Set G))
  let : C'.Normal := normal_subgroupOf_of_le_normalizer normalizerResidualCentralizer_normalizes
  obtain ⟨hgen,hML⟩ := extraspecial_normalizer_inner_frattini_source d h hab structural previous faithful earlier he
  have hgen' : K' ⊔ C' ⊔ M' = ⊤ := by
    rw [←subgroupOf_sup hKN hCN,←subgroupOf_sup (sup_le hKN hCN) hMN,hgen,subgroupOf_self]
  obtain ⟨S,hS⟩ := extraspecial_centralizer_sylow_in_point_normalizer d h hab structural previous faithful he
  let e := (subgroupOfEquivOfLe hCN).symm
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hSM : (S' : Subgroup C').map C'.subtype ≤ M' := by
    rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact hS (mem_map_of_mem C.subtype hz)
  obtain ⟨B,hB,hBC⟩ := Sylow.exists_factor_of_normal_sylow_containment K' C' M' hgen' S' hSM
  let B₀ := (B : Subgroup N).map N.subtype
  have hBN : B₀ ≤ N := map_subtype_le _
  have hBM : B₀ ⊓ M = B₀ ⊓ normalizer (F.Ri L 1 : Set G) := by
    dsimp [M]
    rw [←inf_assoc,inf_of_le_left hBN]
  have hf : B₀ = (B₀ ⊓ K F) ⊔ (B₀ ⊓ normalizer (F.Ri L 1 : Set G)) := by
    have hm := congrArg (Subgroup.map N.subtype) hB
    rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ N.subtype_injective,
      Subgroup.map_inf _ _ _ N.subtype_injective,map_subgroupOf_eq_of_le hKN,
      map_subgroupOf_eq_of_le hMN] at hm
    exact hm.trans (congrArg (fun A => (B₀ ⊓ K F) ⊔ A) hBM)
  have hbc : B₀ ⊓ C ≤ B₀ ⊓ normalizer (F.Ri L 1 : Set G) := by
    have hm := map_mono (f := N.subtype) hBC
    rw [Subgroup.map_inf _ _ _ N.subtype_injective,Subgroup.map_inf _ _ _ N.subtype_injective,
      map_subgroupOf_eq_of_le hCN,map_subgroupOf_eq_of_le hMN] at hm
    exact hm.trans hBM.le
  refine ⟨B,hf,?_,hbc,?_⟩
  · rw [←coe_mul_of_right_le_normalizer_left,←hf]
    exact (le_inf (inf_le_left.trans B₀.le_normalizer) (inf_le_left.trans hBN)).trans
      (inf_normalizer_le_normalizer_inf)
  · exact (le_inf (inf_le_left.trans hBN) inf_le_right).trans hML

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Splitting the original three-Sylow normalizer factor

For the chosen B in N_G(K), the intersection B₁ = B ∩ L₁ is a normal
cubic in B_M = N_B(R₁). Its action on L/O₂(L) is faithful. The automorphism
group of that quotient has three-part three, so B₁ splits off the literal
kernel B₂ = C_{B_M}(L/O₂(L)). The ambient three-rank bound makes B₂ cyclic.
Since B ∩ C_N(K/O₂(K)) is cyclic and contains B₁, the same detection proves
that intersection is exactly B₁. Consequently the original residual
centralizer C is L₁ O_{3′}(C), with quotient of order three.

The source application constructs B using the repaired inner-kernel Frattini
factorization and retains the original group, flag and quotient actions.
It does not assume Data. The rank argument excluding B₂ and the subsequent
Baumann centralizer control remain necessary for N_G(K) = H.

Source: Aschbacher–Smith 14.7.21(1), printed pp.1049–1050,
refs/quasithin.pdf. The literal product is proved without claiming C R₁
normal in N_G(K).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The literal intersection of any original normalizer three-Sylow with
L₁ is a Sylow of L₁ and has order three. -/
theorem extraspecial_normalizer_point_three_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (B : Sylow 3 (normalizer (K F : Set G))) :
    let B₀ := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
    IsSylowIn 3 (B₀ ⊓ F.Li L 1) (F.Li L 1) ∧
      Nat.card (B₀ ⊓ F.Li L 1 : Subgroup G) = 3 := by
  obtain ⟨S,hS⟩ := B.exists_map_subtype_eq_inf_of_normalizes
    ((pointResidual_le F).trans (K F).le_normalizer)
    (extraspecial_normalizer_normalizes_point h hab structural previous faithful he)
  refine ⟨⟨S,hS⟩,?_⟩
  rw [←hS,card_map_of_injective (F.Li L 1).subtype_injective]
  exact card_sylow_three_of_two_group_index_three (pCore 2 (F.Li L 1)) pCore_isPGroup
    (pointResidual_core_quotient_card h structural) S

private theorem ExtraspecialNormalizerSplit_original_quotient_aut_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 := by
  let := h.chosen.elementary
  let e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL :=
    h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  rw [Nat.card_congr (MulAut.congr (e.trans Matrix.PSL3Two.equiv)).toEquiv]
  exact Matrix.PSL3Two.Automorphisms.card_aut

private theorem ExtraspecialNormalizerSplit_original_quotient_center
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    center (L ⧸ pCore 2 L) = ⊥ := by
  let := h.chosen.elementary
  let e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL :=
    h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  apply bot_unique
  intro x hx
  have hz : e x ∈ center Matrix.PSL3Two.SL := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)
  rw [Matrix.PSL3Two.center_eq_bot] at hz
  exact e.injective (hz.trans e.map_one.symm)

private theorem ExtraspecialNormalizerSplit_original_three_action_image_bound
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (X : Subgroup G) (hX : IsPGroup 3 X) (hXL : X ≤ normalizer (L : Set G)) :
    Nat.card ((pCoreNormalizerAction 2 L).comp (inclusion hXL)).range ≤ 3 := by
  let f := (pCoreNormalizerAction 2 L).comp (inclusion hXL)
  obtain ⟨S,hS⟩ := (hX.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  have hc : Nat.card S = 3 := by
    rw [S.card_eq_multiplicity,ExtraspecialNormalizerSplit_original_quotient_aut_card h]
    decide +kernel
  exact (Nat.card_le_card_of_injective (inclusion hS) (inclusion_injective hS)).trans_eq hc

private theorem ExtraspecialNormalizerSplit_original_three_action_detects
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (X A : Subgroup G) (hX : IsPGroup 3 X) (hXL : X ≤ normalizer (L : Set G))
    (hAL : A ≤ L) :
    Function.Injective (((pCoreNormalizerAction 2 L).comp (inclusion hXL)).comp
      (A.subgroupOf X).subtype) := by
  let f := (pCoreNormalizerAction 2 L).comp (inclusion hXL)
  have hd : Disjoint X (L.pCoreIn 2) :=
    hX.disjoint_of_coprime (isPGroup_pCoreIn 2 L) (by decide)
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hm : ((x : X) : G) ∈ pCoreActionKernelIn 2 L (normalizer (L : Set G)) ⊓ L := by
    exact ⟨⟨hXL x.val.property,inclusion hXL x.val,hx,rfl⟩,hAL x.property⟩
  rw [pCoreActionKernelIn_inf_eq_core L (normalizer (L : Set G)) L.le_normalizer
    (ExtraspecialNormalizerSplit_original_quotient_center h)] at hm
  exact Subtype.ext (Subtype.ext (hd.le_bot ⟨x.val.property,hm⟩))

/-- The original normalizer factor splits over the detected point cubic;
the cyclic residual-centralizer Sylow is exactly that cubic. -/
theorem extraspecial_normalizer_three_sylow_split
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (B : Sylow 3 (normalizer (K F : Set G)))
    (hBCM : ((B : Subgroup _).map (normalizer (K F : Set G)).subtype) ⊓
      normalizerResidualCentralizer F ≤
      ((B : Subgroup _).map (normalizer (K F : Set G)).subtype) ⊓
        normalizer (F.Ri L 1 : Set G))
    (hBML : ((B : Subgroup _).map (normalizer (K F : Set G)).subtype) ⊓
      normalizer (F.Ri L 1 : Set G) ≤ normalizer (L : Set G)) :
    let B₀ := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
    let B₁ := B₀ ⊓ F.Li L 1
    let B_M := B₀ ⊓ normalizer (F.Ri L 1 : Set G)
    let B₂ := pCoreActionKernelIn 2 L B_M
    Nat.card B₁ = 3 ∧ B₀ ⊓ normalizerResidualCentralizer F = B₁ ∧
      B_M = B₁ ⊔ B₂ ∧ Disjoint B₁ B₂ ∧
      B₁ ≤ centralizer (B₂ : Set G) ∧ IsCyclic B₂ := by
  let N := normalizer (K F : Set G)
  let C := normalizerResidualCentralizer F
  let B₀ := (B : Subgroup N).map N.subtype
  let A := B₀ ⊓ F.Li L 1
  let X := B₀ ⊓ normalizer (F.Ri L 1 : Set G)
  let D := pCoreActionKernelIn 2 L X
  have hB : IsPGroup 3 B₀ := B.isPGroup'.map N.subtype
  have hX : IsPGroup 3 X := hB.to_le inf_le_left
  have hXN : X ≤ N := inf_le_left.trans (map_subtype_le _)
  have hAC : A ≤ B₀ ⊓ C := inf_le_inf_left _
    (extraspecial_point_le_residualCentralizer h hab structural previous faithful he)
  have hAX : A ≤ X := hAC.trans hBCM
  have hAc : Nat.card A = 3 :=
    (extraspecial_normalizer_point_three_sylow h hab structural previous faithful he B).2
  have hXA : X ≤ normalizer (A : Set G) :=
    (le_inf (inf_le_left.trans B₀.le_normalizer)
      (hXN.trans (extraspecial_normalizer_normalizes_point h hab structural previous faithful he))).trans
      inf_normalizer_le_normalizer_inf
  let A' := A.subgroupOf X
  let : A'.Normal := normal_subgroupOf_of_le_normalizer hXA
  have hA'c : Nat.card A' = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAX).toEquiv).trans hAc
  let f := (pCoreNormalizerAction 2 L).comp (inclusion hBML)
  have hi : Function.Injective (f.comp A'.subtype) :=
    ExtraspecialNormalizerSplit_original_three_action_detects h X A hX hBML
      (inf_le_right.trans ((F.Li_le L 1).trans inf_le_left))
  have hr : Nat.card f.range ≤ 3 := ExtraspecialNormalizerSplit_original_three_action_image_bound h X hX hBML
  obtain ⟨hgen,hd,hz⟩ := detected_normal_cubic_product hX A' hA'c f hi hr
  have hD : D = f.ker.map X.subtype := pCoreActionKernelIn_eq_map_ker 2 L X hBML
  have hsplit : X = A ⊔ D := by
    have hh := congrArg (Subgroup.map X.subtype) hgen
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAX,←hD,
      ←MonoidHom.range_eq_map,X.range_subtype] at hh
    exact hh.symm
  have hdis : Disjoint A D := by
    rw [hD,←map_subgroupOf_eq_of_le hAX]
    exact disjoint_map X.subtype_injective hd
  have hcentral : A ≤ centralizer (D : Set G) := by
    intro a ha c hc
    rw [hD] at hc
    obtain ⟨x,hx,rfl⟩ := hc
    exact congrArg Subtype.val (mem_center_iff.mp (hz (show (⟨a,hAX ha⟩ : X) ∈ A' from ha)) x)
  have hrX : primeRank 3 X ≤ 2 :=
    (primeRank_le_of_injective 3 (inclusion hXN) (inclusion_injective hXN)).trans
      (extraspecial_normalizer_threeRanks d h hab structural previous faithful he).1.le
  have hcyc : IsCyclic D := by
    rw [hD]
    let := detected_normal_cubic_kernel_cyclic hX hrX A' hA'c f hi hr
    exact isCyclic_of_surjective (X.subtype.subgroupMap f.ker) (X.subtype.subgroupMap_surjective f.ker)
  have hBC : B₀ ⊓ C = A := by
    obtain ⟨S,hS⟩ := B.exists_map_subtype_eq_inf_of_normalizes
      (show C ≤ N from map_subtype_le _) normalizerResidualCentralizer_normalizes
    have hc : IsCyclic (B₀ ⊓ C : Subgroup G) := by
      rw [←hS]
      let := extraspecial_normalizer_centralizer_sylow_cyclic d h hab structural previous faithful he S
      exact isCyclic_of_surjective (C.subtype.subgroupMap (S : Subgroup C))
        (C.subtype.subgroupMap_surjective (S : Subgroup C))
    let E := (B₀ ⊓ C).subgroupOf X
    let : IsCyclic E := (subgroupOfEquivOfLe hBCM).isCyclic.mpr hc
    have heq : E = A' := cyclic_eq_detected_cubic hX A' hA'c f hi hr E (comap_mono hAC)
    have hh := congrArg (Subgroup.map X.subtype) heq
    rwa [map_subgroupOf_eq_of_le hBCM,map_subgroupOf_eq_of_le hAX] at hh
  exact ⟨hAc,hBC,hsplit,hdis,hcentral,hcyc⟩

/-- The source Sylow choice, now with the exact split normalizer factor and
its residual-centralizer Sylow identified, under the original hypotheses. -/
theorem extraspecial_normalizer_three_sylow_split_source
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ B : Sylow 3 (normalizer (K F : Set G)),
      let B₀ := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
      let B_K := B₀ ⊓ K F
      let B₁ := B₀ ⊓ F.Li L 1
      let B_M := B₀ ⊓ normalizer (F.Ri L 1 : Set G)
      let B₂ := pCoreActionKernelIn 2 L B_M
      (B₀ : Set G) = (B_K : Set G) * (B_M : Set G) ∧
        B_M ≤ normalizer (L : Set G) ∧
        IsSylowIn 3 B₁ (F.Li L 1) ∧ Nat.card B₁ = 3 ∧
        B₀ ⊓ normalizerResidualCentralizer F = B₁ ∧
        B_M = B₁ ⊔ B₂ ∧ Disjoint B₁ B₂ ∧
        B₁ ≤ centralizer (B₂ : Set G) ∧ IsCyclic B₂ ∧
        Nonempty (B₁ × B₂ ≃* B_M) := by
  obtain ⟨B,_,hf,hBC,hML⟩ := extraspecial_normalizer_three_sylow_factorization
    d h hab structural previous faithful earlier he
  obtain ⟨hc,hC,hs,hd,hcent,hcyc⟩ := extraspecial_normalizer_three_sylow_split
    d h hab structural previous faithful he B hBC hML
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hcent
  exact ⟨B,hf,hML,
    (extraspecial_normalizer_point_three_sylow h hab structural previous faithful he B).1,
    hc,hC,hs,hd,hcent,hcyc,⟨e.trans (MulEquiv.subgroupCongr hs.symm)⟩⟩

/-- The original residual centralizer is L₁ times its normal three-complement;
its quotient by that complement has order exactly three. -/
theorem extraspecial_normalizer_centralizer_three_structure
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let C := normalizerResidualCentralizer F
    (∀ S : Sylow 3 C, Nat.card S = 3) ∧
      C = F.Li L 1 ⊔ (pPrimeCore 3 C).map C.subtype ∧
      Nat.card (C ⧸ pPrimeCore 3 C) = 3 := by
  let N := normalizer (K F : Set G)
  let C := normalizerResidualCentralizer F
  obtain ⟨B,_,_,_,hc,hBC,_,_,_,_,_⟩ :=
    extraspecial_normalizer_three_sylow_split_source d h hab structural previous faithful earlier he
  obtain ⟨S,hS⟩ := B.exists_map_subtype_eq_inf_of_normalizes
    (show C ≤ N from map_subtype_le _) normalizerResidualCentralizer_normalizes
  have hSc : Nat.card S = 3 := by
    have hh := congrArg (fun A : Subgroup G => Nat.card A) hS
    rw [card_map_of_injective C.subtype_injective,hBC] at hh
    exact hh.trans hc
  have hcomp : HasNormalPComplement 3 C := hasNormalPComplement_of_le 3 le_sup_left
    (extraspecial_centralizer_point_normal_complement d h hab structural previous faithful he)
  have hQ : IsPGroup 3 (C ⧸ pPrimeCore 3 C) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 3 C hcomp
  have hgen := S.sup_eq_top_of_quotient_isPGroup (pPrimeCore 3 C) hQ
  have hgen' : C = ((S : Subgroup C).map C.subtype) ⊔ (pPrimeCore 3 C).map C.subtype := by
    have hh := congrArg (Subgroup.map C.subtype) hgen
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,C.range_subtype] at hh
    exact hh.symm
  have hL : F.Li L 1 ≤ C := extraspecial_point_le_residualCentralizer
    h hab structural previous faithful he
  have hSL : (S : Subgroup C).map C.subtype ≤ F.Li L 1 :=
    hS.le.trans (hBC.le.trans inf_le_right)
  have hCL : C = F.Li L 1 ⊔ (pPrimeCore 3 C).map C.subtype :=
    le_antisymm (hgen'.le.trans (sup_le_sup hSL le_rfl))
      (sup_le hL (map_subtype_le _))
  let q := QuotientGroup.mk' (pPrimeCore 3 C)
  let S' := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hS' : (S' : Subgroup (C ⧸ pPrimeCore 3 C)) = ⊤ :=
    (S'.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  have honto : Function.Surjective (q.comp (S : Subgroup C).subtype) := by
    intro x
    obtain ⟨s,hs,hsx⟩ := (show x ∈ (S' : Subgroup (C ⧸ pPrimeCore 3 C)) from hS' ▸ mem_top x)
    exact ⟨⟨s,hs⟩,hsx⟩
  have hinj := IsPGroup.quotient_pPrimeCore_injective (S : Subgroup C) S.isPGroup'
  have hQc : Nat.card (C ⧸ pPrimeCore 3 C) = 3 :=
    (Nat.card_congr (Equiv.ofBijective (q.comp (S : Subgroup C).subtype) ⟨hinj,honto⟩)).symm.trans hSc
  exact ⟨fun S₀ => (Nat.card_congr (S₀.equiv S).toEquiv).trans hSc,hCL,hQc⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Excluding the remaining cubic normalizer kernel

The original R₁ action on K/O₂(K) is a nontrivial center-fixing two-group.
Its unique involution is fixed by every actor normalizing R₁. The actual
intersection of a three-Sylow B of N_G(K) with K maps isomorphically onto
K/O₂(K). Transporting that involution and the cubic action to this normal
subgroup of B makes the ambient three-rank obstruction applicable.

Every cubic in N_B(R₁) therefore acts trivially on K/O₂(K). In the source
split B_M = B₁ × B₂, this puts a hypothetical cubic of B₂ in B ∩ C = B₁,
contradicting disjointness. Thus B₂ = 1, B_M = B₁ and B lies wholly in K,
with its actual Heisenberg isomorphism retained. The marked outer image is
a two-group, giving N = H O₃′(N) and C = L₁ O₃′(N). The original orbit
W = ⟨V₁^C⟩ lies in Z(O₂(N)), is reduced in C R₁, and its faithful
C R₁-action has order prime to three.

Source: Aschbacher–Smith 14.7.21(1), printed pp.1049–1050,
refs/quasithin.pdf. The final Baumann-normalizer argument and N_G(K)=H
remain separate obligations. No normality of C R₁ is asserted here.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialNormalizerCubic_residual_quotient_action_star (n : F.H)
    (x : (K F) ⧸ pCore 2 (K F)) :
    residualStarEquiv F (pCoreNormalizerAction 2 (K F) (inclusion (H_normalizes_K F) n) x) =
      MulAut.conjNormal (starMap F n) (residualStarEquiv F x) := by
  induction x using QuotientGroup.induction_on with | H k =>
    change residualStarEquiv F (pCoreNormalizerAction 2 (K F) (inclusion (H_normalizes_K F) n) (QuotientGroup.mk' _ k)) = _
    apply Subtype.ext
    rw [pCoreNormalizerAction_mk,residualStarEquiv_mk]
    change starMap F _ = starMap F n *
      (residualStarEquiv F (QuotientGroup.mk' (pCore 2 (K F)) k) : HStar F.H) * (starMap F n)⁻¹
    rw [residualStarEquiv_mk,←map_inv,←map_mul,←map_mul]
    congr 1

/-- The actual point-core action has a center-fixing involution preserved by
its original normalizer. -/
theorem extraspecial_point_action_involution
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ a : MulAut ((K F) ⧸ pCore 2 (K F)), a^2=1 ∧ a≠1 ∧
      (∀ z ∈ center ((K F) ⧸ pCore 2 (K F)), a z=z) ∧
      ∀ n : normalizer (K F : Set G), (n : G) ∈ normalizer (F.Ri L 1 : Set G) →
        a * pCoreNormalizerAction 2 (K F) n = pCoreNormalizerAction 2 (K F) n * a := by
  obtain ⟨e⟩ := he
  let J := (K F) ⧸ pCore 2 (K F)
  let N := normalizer (K F : Set G)
  let f := pCoreNormalizerAction 2 (K F)
  let R := (F.Ri L 1).subgroupOf N
  let A := R.map f
  let : IsExtraspecial 3 J := (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hc : Nat.card J=27 := (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p:=3))
  have hR2 : IsPGroup 2 A := (isPGroup_pCoreIn 2 _).comap_subtype.map f
  have hRY : F.Ri L 1 ≤ normalizerPointCentralizer F L :=
    (isSylowIn_iff.mp (extraspecial_normalizer_point_sylow h hab structural previous faithful ⟨e⟩)).2.1
  have hZ : ∀ a ∈ A, ∀ z ∈ center J, a z=z := by
    rintro a ⟨r,hr,rfl⟩
    have hy : r ∈ (normalizerPointCentralizer F L).subgroupOf N := hRY hr
    rw [extraspecial_normalizer_point_outer_preimage h hab structural previous faithful e] at hy
    exact (HeisenbergPrime.TernaryOuterAction.markedAction_mem_special_iff e (f r)).mp hy
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous
    (inferInstanceAs (IsExtraspecial 3 J)) hc
    ((Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2)))
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨a,ha,_,_,hne,_⟩ := exists_extraspecial_critical_actor h hab structural previous
    (inferInstanceAs (IsExtraspecial 3 J)) hc
    ((Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))) c hs
  have hA : A ≠ ⊥ := by
    intro hh
    have hfa : f (inclusion (H_normalizes_K F) a) = 1 := by
      have hm : f (inclusion (H_normalizes_K F) a) ∈ A :=
        mem_map_of_mem f (critical_le_Ri_at h structural c ha)
      simpa only [hh,mem_bot] using hm
    apply hne
    ext x
    obtain ⟨y,rfl⟩ := (residualStarEquiv F).surjective x
    rw [←ExtraspecialNormalizerCubic_residual_quotient_action_star a y,hfa]
    rfl
  obtain ⟨a,ha,ha2,ha1,hfix⟩ :=
    MulAut.exists_involution_fixed_by_normalizer_of_extraspecial27 hc A hR2 hA hZ
  refine ⟨a,ha2,ha1,hZ a ha,?_⟩
  intro n hnR
  apply hfix
  apply le_normalizer_map f
  apply mem_map_of_mem
  apply mem_normalizer_fintype
  intro r hr
  exact (mem_normalizer_iff.mp hnR r).mp hr

/-- The quotient map identifies the actual intersection with K with its
Heisenberg quotient, retaining equivariance for the containing three-Sylow. -/
private theorem ExtraspecialNormalizerCubic_normalizer_three_sylow_residual_quotient_bijective
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (B : Sylow 3 (normalizer (K F : Set G))) :
    let B₀ := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
    Function.Bijective (fun x : (K F).subgroupOf B₀ =>
      QuotientGroup.mk' (pCore 2 (K F)) ⟨x.val.val,x.property⟩) := by
  let N := normalizer (K F : Set G)
  let B₀ := (B : Subgroup N).map N.subtype
  let P := (K F).subgroupOf B₀
  let i : P →* K F := {
    toFun x := ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let q := QuotientGroup.mk' (pCore 2 (K F))
  change Function.Bijective (q.comp i)
  have hB : IsPGroup 3 B₀ := B.isPGroup'.map N.subtype
  have hd := hB.disjoint_of_coprime (isPGroup_pCoreIn 2 (K F)) (by decide : Nat.Coprime 3 2)
  have hi : Function.Injective (q.comp i) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hm : (i x : G) ∈ (K F).pCoreIn 2 :=
      mem_map_of_mem (K F).subtype ((QuotientGroup.eq_one_iff _).mp hx)
    exact Subtype.ext (Subtype.ext (hd.le_bot ⟨x.val.property,hm⟩))
  refine ⟨hi,?_⟩
  obtain ⟨S,hS⟩ := B.exists_map_subtype_eq_inf_of_normalizes (K F).le_normalizer le_rfl
  obtain ⟨e⟩ := he
  have hQ : IsPGroup 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).isPGroup.of_equiv e.symm
  let S' := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hStop : (S' : Subgroup ((K F) ⧸ pCore 2 (K F))) = ⊤ :=
    (S'.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  intro y
  obtain ⟨k,hk,hky⟩ := (show y ∈ (S' : Subgroup ((K F) ⧸ pCore 2 (K F))) from hStop ▸ mem_top y)
  have hkB : (k : G) ∈ B₀ := (hS ▸ mem_map_of_mem (K F).subtype hk).1
  exact ⟨⟨⟨k,hkB⟩,k.property⟩,hky⟩

/-- Every cubic in the original point-core normalizer acts trivially on
K/O₂(K), using the actual ambient three-rank bound. -/
theorem extraspecial_normalizer_cubic_action_trivial
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (B : Sylow 3 (normalizer (K F : Set G)))
    (b : (B : Subgroup _).map (normalizer (K F : Set G)).subtype)
    (hb : b^3=1) (hbn : (b : G) ∈ normalizer (F.Ri L 1 : Set G)) :
    pCoreNormalizerAction 2 (K F) ⟨b,map_subtype_le _ b.property⟩ = 1 := by
  let N := normalizer (K F : Set G)
  let B₀ := (B : Subgroup N).map N.subtype
  let P := (K F).subgroupOf B₀
  have hBN : B₀ ≤ N := map_subtype_le _
  let : P.Normal := normal_subgroupOf_of_le_normalizer hBN
  let i : P →* K F := {
    toFun x := ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let q := QuotientGroup.mk' (pCore 2 (K F))
  let eP := MulEquiv.ofBijective (q.comp i) (ExtraspecialNormalizerCubic_normalizer_three_sylow_residual_quotient_bijective he B)
  obtain ⟨e⟩ := he
  obtain ⟨a,ha2,ha1,haZ,hcomm⟩ := extraspecial_point_action_involution h hab structural previous faithful ⟨e⟩
  let β := pCoreNormalizerAction 2 (K F) ⟨b,hBN b.property⟩
  have hβ3 : β^3=1 := by
    change pCoreNormalizerAction 2 (K F) (inclusion hBN b)^3=1
    rw [←map_pow,←map_pow,hb,map_one,map_one]
  have hc : Nat.card (center ((K F) ⧸ pCore 2 (K F)))=3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv,HeisenbergPrime.card_center]
  have hr : primeRank 3 B₀ ≤ 2 := (primeRank_mono 3 hBN).trans
    (extraspecial_normalizer_threeRanks d h hab structural previous faithful ⟨e⟩).1.le
  apply cubic_action_trivial_of_extraspecial27_marking P hr eP e a β ha2 ha1 haZ b hb
    (hcomm ⟨b,hBN b.property⟩ hbn) (MulAut.fixes_cubic_center_of_cube_eq_one hc β hβ3)
  intro x
  change q (i (MulAut.conjNormal b x)) =
    pCoreNormalizerAction 2 (K F) ⟨b,hBN b.property⟩ (q (i x))
  rw [pCoreNormalizerAction_mk]
  rfl

/-- The remaining literal L/O₂(L)-action kernel of B_M is trivial. -/
theorem extraspecial_normalizer_three_sylow_kernel_eq_bot
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (B : Sylow 3 (normalizer (K F : Set G)))
    (hBCM : ((B : Subgroup _).map (normalizer (K F : Set G)).subtype) ⊓
      normalizerResidualCentralizer F ≤
      ((B : Subgroup _).map (normalizer (K F : Set G)).subtype) ⊓
        normalizer (F.Ri L 1 : Set G))
    (hBML : ((B : Subgroup _).map (normalizer (K F : Set G)).subtype) ⊓
      normalizer (F.Ri L 1 : Set G) ≤ normalizer (L : Set G)) :
    pCoreActionKernelIn 2 L (((B : Subgroup _).map
      (normalizer (K F : Set G)).subtype) ⊓ normalizer (F.Ri L 1 : Set G)) = ⊥ := by
  let N := normalizer (K F : Set G)
  let B₀ := (B : Subgroup N).map N.subtype
  let B₁ := B₀ ⊓ F.Li L 1
  let B_M := B₀ ⊓ normalizer (F.Ri L 1 : Set G)
  let B₂ := pCoreActionKernelIn 2 L B_M
  obtain ⟨_,hC,_,hd,_,_⟩ := extraspecial_normalizer_three_sylow_split
    d h hab structural previous faithful he B hBCM hBML
  have hB : IsPGroup 3 B₀ := B.isPGroup'.map N.subtype
  have hDB : B₂ ≤ B₀ := inf_le_left.trans inf_le_left
  have hD : IsPGroup 3 B₂ := hB.to_le hDB
  change B₂ = ⊥
  by_contra hn
  have hdiv : 3 ∣ Nat.card B₂ := hD.card_eq_or_dvd.resolve_left
    (fun hh => hn (card_eq_one.mp hh))
  obtain ⟨b,hbo⟩ := exists_prime_orderOf_dvd_card' (G:=B₂) 3 hdiv
  let bB : B₀ := inclusion hDB b
  have hb3 : bB^3=1 := by
    change inclusion hDB b ^ 3=1
    rw [←map_pow,←hbo,pow_orderOf_eq_one,map_one]
  have ha := extraspecial_normalizer_cubic_action_trivial d h hab structural previous faithful he B
    bB hb3 b.property.1.2
  have hbC : (b : G) ∈ normalizerResidualCentralizer F :=
    ⟨⟨b,map_subtype_le _ (hDB b.property)⟩,ha,rfl⟩
  have hb1 : (b : G) ∈ B₁ := by
    change (b : G) ∈ B₀ ⊓ F.Li L 1
    rw [←hC]
    exact ⟨hDB b.property,hbC⟩
  have hbone : b=1 := Subtype.ext (hd.le_bot ⟨hb1,b.property⟩)
  have hh : (1 : ℕ)=3 := by simpa only [hbone,orderOf_one] using hbo
  omega

/-- In the original source choice the full three-Sylow lies in K and has
order 27, and its point-core normalizer is exactly its intersection with L₁. -/
theorem extraspecial_normalizer_three_sylow_in_residual
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ B : Sylow 3 (normalizer (K F : Set G)),
      let B₀ := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
      B₀ ≤ K F ∧ Nat.card B₀=27 ∧ Nonempty (B₀ ≃* HeisenbergPrime 3) ∧
        B₀ ⊓ normalizer (F.Ri L 1 : Set G) = B₀ ⊓ F.Li L 1 ∧
        pCoreActionKernelIn 2 L (B₀ ⊓ normalizer (F.Ri L 1 : Set G))=⊥ := by
  obtain ⟨B,hgen,hprod,hBCM,hBML⟩ := extraspecial_normalizer_three_sylow_factorization
    d h hab structural previous faithful earlier he
  have hbot := extraspecial_normalizer_three_sylow_kernel_eq_bot
    d h hab structural previous faithful he B hBCM hBML
  obtain ⟨_,_,hsplit,_,_,_⟩ := extraspecial_normalizer_three_sylow_split
    d h hab structural previous faithful he B hBCM hBML
  rw [hbot,sup_bot_eq] at hsplit
  have hBK : (B : Subgroup _).map (normalizer (K F : Set G)).subtype ≤ K F := by
    rw [hgen,hsplit]
    exact sup_le inf_le_right (inf_le_right.trans (pointResidual_le F))
  let B₀ := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
  let f : B₀ →* ((K F) ⧸ pCore 2 (K F)) :=
    (QuotientGroup.mk' (pCore 2 (K F))).comp (inclusion hBK)
  have htop : (K F).subgroupOf B₀ = ⊤ := (subgroupOf_eq_top).mpr hBK
  let j : B₀ ≃* (K F).subgroupOf B₀ :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
  have hj : Function.Bijective f :=
    (ExtraspecialNormalizerCubic_normalizer_three_sylow_residual_quotient_bijective he B).comp j.bijective
  obtain ⟨e⟩ := he
  let eB := (MulEquiv.ofBijective f hj).trans e
  exact ⟨B,hBK,(Nat.card_congr eB.toEquiv).trans (HeisenbergPrime.card (p:=3)),⟨eB⟩,hsplit,hbot⟩

private theorem ExtraspecialNormalizerCubic_outer_image_isTwoGroup_of_three_sylow_killed
    {X : Type*} [Group X] [Finite X]
    (f : X →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (B : Sylow 3 X)
    (hB : (B : Subgroup X) ≤ f.ker) : IsPGroup 2 f.range := by
  let S := B.mapSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  have hS : (S : Subgroup f.range)=⊥ := by
    apply bot_unique
    rintro x ⟨b,hb,rfl⟩
    exact Subtype.ext (hB hb)
  have hthree : ¬ 3 ∣ Nat.card f.range := by
    have hh := S.not_dvd_index
    rwa [hS,index_bot] at hh
  have hd : Nat.card f.range ∣ 48 := by
    have hc : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))=48 := by
      rw [Matrix.card_GL_field]; decide
    exact hc ▸ f.range.card_subgroup_dvd_card
  apply IsPGroup.of_card_dvd_pow (p:=2) (n:=4)
  have hcop : Nat.Coprime (Nat.card f.range) 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hthree).symm
  exact hcop.dvd_of_dvd_mul_left hd

/-- After the original cubic exclusion, H together with the literal
residual centralizer exhausts N_G(K). -/
theorem extraspecial_normalizer_eq_H_sup_centralizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizer (K F : Set G) = F.H ⊔ normalizerResidualCentralizer F := by
  obtain ⟨B,hBK,_,_,_,_⟩ := extraspecial_normalizer_three_sylow_in_residual
    d h hab structural previous faithful earlier he
  obtain ⟨e⟩ := he
  let N := normalizer (K F : Set G)
  let a := pCoreNormalizerAction 2 (K F)
  let f := (HeisenbergPrime.TernaryOuterAction.markedAction e).comp a
  have hk : f.ker = (K F).subgroupOf N ⊔ a.ker := by
    rw [show f.ker = (HeisenbergPrime.TernaryOuterAction.markedAction e).ker.comap a from rfl,
      HeisenbergPrime.TernaryOuterAction.markedAction_ker,
      ←pCoreNormalizerAction_component_image,comap_map_eq]
  have hBf : (B : Subgroup N) ≤ f.ker := by
    rw [hk]
    intro b hb
    exact mem_sup_left (hBK (mem_map_of_mem N.subtype hb))
  have himage := ExtraspecialNormalizerCubic_outer_image_isTwoGroup_of_three_sylow_killed f B hBf
  have hQ : IsPGroup 2 (N ⧸ f.ker) :=
    himage.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hTN : (T : Subgroup G) ≤ N := (F.invariant 1).trans (H_normalizes_K F)
  have hgen := congrArg (Subgroup.map N.subtype)
    ((T.subtype hTN).sup_eq_top_of_quotient_isPGroup f.ker hQ)
  rw [Subgroup.map_sup,hk,Subgroup.map_sup,map_subgroupOf_eq_of_le (K F).le_normalizer,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN,←MonoidHom.range_eq_map,N.range_subtype] at hgen
  have hH : K F ⊔ (T : Subgroup G) = F.H := (residual_product F).symm
  change _ = F.H ⊔ a.ker.map N.subtype
  rw [←hH]
  simpa only [sup_assoc,sup_comm,sup_left_comm] using hgen.symm

private theorem ExtraspecialNormalizerCubic_normalizer_threePrimeCore_le_centralizer
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (pPrimeCore 3 (normalizer (K F : Set G))).map (normalizer (K F : Set G)).subtype ≤
      normalizerResidualCentralizer F := by
  let N := normalizer (K F : Set G)
  let D := (pPrimeCore 3 N).map N.subtype
  let I := D.subgroupOf (K F)
  let q := QuotientGroup.mk' (pCore 2 (K F))
  have hcopD : Nat.Coprime 3 (Nat.card D) := by
    rw [card_map_of_injective N.subtype_injective]
    exact pPrimeCore_coprime_card
  have hcopI : Nat.Coprime 3 (Nat.card I) := hcopD.of_dvd_right
    (card_comap_dvd_of_injective D (K F).subtype (K F).subtype_injective)
  obtain ⟨e⟩ := he
  have hQ : IsPGroup 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).isPGroup.of_equiv e.symm
  have hI : I ≤ pCore 2 (K F) := by
    have hc : Nat.Coprime 3 (Nat.card (I.map q)) := hcopI.of_dvd_right (I.card_map_dvd q)
    have hi : I.map q=⊥ := card_eq_one.mp
      ((hQ.to_subgroup (I.map q)).card_eq_or_dvd.resolve_right
        (Nat.prime_three.coprime_iff_not_dvd.mp hc))
    simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff I).mp hi
  have hnD : N ≤ normalizer (D : Set G) := by
    have hh := (pPrimeCore 3 N).le_normalizer_map N.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,N.range_subtype] using hh
  rintro x ⟨n,hn,rfl⟩
  refine ⟨n,?_,rfl⟩
  change pCoreNormalizerAction 2 (K F) n = 1
  rw [pCoreNormalizerAction_eq_one_iff]
  intro k
  apply hI
  change (n : G) * (k : G) * (n : G)⁻¹ / (k : G) ∈ D
  rw [div_eq_mul_inv]
  exact le_normalizer_iff_commutator_le_left.mp ((K F).le_normalizer.trans hnD)
    (commutator_mem_commutator (mem_map_of_mem N.subtype hn) k.property)

/-- The source three-prime supplement is the core of the full normalizer,
not just an unspecified three-prime subgroup of C. -/
theorem extraspecial_normalizer_threePrime_supplement
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let N := normalizer (K F : Set G)
    let D := (pPrimeCore 3 N).map N.subtype
    normalizerResidualCentralizer F = F.Li L 1 ⊔ D ∧ N = F.H ⊔ D ∧
      (N : Set G) = (F.H : Set G) * (D : Set G) := by
  let N := normalizer (K F : Set G)
  let C := normalizerResidualCentralizer F
  let E := (pPrimeCore 3 C).map C.subtype
  let D := (pPrimeCore 3 N).map N.subtype
  have hCN : C ≤ N := map_subtype_le _
  have hEN : E ≤ N := (map_subtype_le _).trans hCN
  have hNE : N ≤ normalizer (E : Set G) :=
    normalizerResidualCentralizer_normalizes.trans
      (normalizer_le_normalizer_characteristic_image C (pPrimeCore 3 C))
  have hED : E ≤ D := by
    let : (E.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNE
    have hc : Nat.Coprime 3 (Nat.card (E.subgroupOf N)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv,
        card_map_of_injective C.subtype_injective]
      exact pPrimeCore_coprime_card
    have hh : E.subgroupOf N ≤ pPrimeCore 3 N := le_sSup ⟨inferInstance,hc⟩
    have hm := map_mono (f:=N.subtype) hh
    rwa [map_subgroupOf_eq_of_le hEN] at hm
  have hDC : D ≤ C := ExtraspecialNormalizerCubic_normalizer_threePrimeCore_le_centralizer he
  have hLC : F.Li L 1 ≤ C := extraspecial_point_le_residualCentralizer
    h hab structural previous faithful he
  have hC : C = F.Li L 1 ⊔ D := le_antisymm
    ((extraspecial_normalizer_centralizer_three_structure
      d h hab structural previous faithful earlier he).2.1.le.trans (sup_le_sup_left hED _))
    (sup_le hLC hDC)
  have hN : N = F.H ⊔ D := by
    change normalizer (K F : Set G) = F.H ⊔ D
    rw [extraspecial_normalizer_eq_H_sup_centralizer d h hab structural previous faithful earlier he]
    change F.H ⊔ C = F.H ⊔ D
    have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
    rw [hC,←sup_assoc,sup_eq_left.mpr hLH]
  refine ⟨hC,hN,?_⟩
  change (N : Set G) = (F.H : Set G) * (D : Set G)
  rw [hN]
  apply coe_mul_of_left_le_normalizer_right
  have hND : N ≤ normalizer (D : Set G) := by
    have hh := (pPrimeCore 3 N).le_normalizer_map N.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,N.range_subtype] using hh
  exact (H_normalizes_K F).trans hND

/-- The original central-seed orbit is reduced in C R₁, with a faithful
action quotient of order prime to three. -/
theorem extraspecial_normalizer_central_seed_reduced
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let N := normalizer (K F : Set G)
    let C := normalizerResidualCentralizer F
    let X := C ⊔ F.Ri L 1
    let W := conjugateSpanBy (F.Vi 1) C
    IsElementaryAbelian 2 W ∧ W ≤ N.pCoreIn 2 ∧
      W ≤ centralizer (N.pCoreIn 2 : Set G) ∧
      Theory.GroupTheory.IsPReduced 2 (W.subgroupOf X) ∧
      F.Li L 1 ≤ centralizer (W : Set G) ∧
      Nat.Coprime 3 ((centralizer (W : Set G)).relIndex X) := by
  let N := normalizer (K F : Set G)
  let C := normalizerResidualCentralizer F
  let X := C ⊔ F.Ri L 1
  let W := conjugateSpanBy (F.Vi 1) C
  have hTN : (T : Subgroup G) ≤ N := (F.invariant 1).trans (H_normalizes_K F)
  have hCN : C ≤ N := map_subtype_le _
  have hZT : F.Vi 1 ≤ (T : Subgroup G) := (F.le_seed 1).trans h.chosen.le_sylow
  have hZC : F.Vi 1 ≤ centralizer (T : Set G) :=
    le_centralizer_iff.mp ((F.invariant 1).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
  have hNmax := (extraspecial_residual_normalizer_unique d h hab structural previous faithful he).1
  have hNHe : N ∈ He G := mem_He_iff.mpr (d.qtke.evenCharacteristic T N hNmax hTN)
  have hQT : N.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN] using
      pCoreIn_le_sylow N (T.subtype hTN)
  have hWN : W ≤ N := conjugateSpanBy_le (hZT.trans hTN) (hCN.trans N.le_normalizer)
  have hWQcentral : W ≤ centralizer (N.pCoreIn 2 : Set G) :=
    conjugateSpanBy_le (hZC.trans (centralizer_le hQT))
      ((hCN.trans (N.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image N (pCore 2 N)))).trans
        (normalizer_le_normalizer_centralizer _))
  have hWQ : W ≤ N.pCoreIn 2 := (le_inf hWN hWQcentral).trans hNHe
  let : IsMulCommutative W := le_centralizer_iff_isMulCommutative.mp
    (hWQcentral.trans (centralizer_le hWQ))
  let := h.chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
  let : IsElementaryAbelian 2 W := conjugateSpanBy_elementary_of_commutative _ _
  have hZR : F.Vi 1 ≤ F.Ri L 1 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 (F.Vi 1)) (hZT.trans le_sup_right)
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))
  have hRT : F.Ri L 1 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow (F.Li L 1 ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hRY := (isSylowIn_iff.mp
    (extraspecial_normalizer_point_sylow h hab structural previous faithful he)).2.1
  have hXY : X ≤ normalizerPointCentralizer F L := sup_le
    (extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he) hRY
  have hXC : X ≤ normalizer (C : Set G) :=
    (hXY.trans inf_le_left).trans normalizerResidualCentralizer_normalizes
  have hspan : conjugateSpanBy (F.Vi 1) X = W :=
    conjugateSpanBy_sup_of_normalizes_seed _ _ _ (hRT.trans (F.invariant 1))
      (le_sup_right.trans hXC)
  have hZX : F.Vi 1 ≤ X := hZR.trans le_sup_right
  have hWX : W ≤ X := hspan ▸ conjugateSpanBy_le_self hZX
  have hclosure : normalClosure (F.Vi 1 |>.subgroupOf X : Set X) = W.subgroupOf X := by
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy _ _ hZX,hspan]
  have hred : Theory.GroupTheory.IsPReduced 2 (W.subgroupOf X) := by
    obtain ⟨S,hS⟩ := (extraspecial_normalizer_point_sylow
      h hab structural previous faithful he).restrict le_sup_right hXY
    have hS' : (S : Subgroup X) = (F.Ri L 1).subgroupOf X := by
      apply map_injective X.subtype_injective
      rw [hS,map_subgroupOf_eq_of_le le_sup_right]
    let : IsElementaryAbelian 2 ((F.Vi 1).subgroupOf X) := IsElementaryAbelian.subgroupOf hZX
    let : IsMulCommutative (normalClosure (F.Vi 1 |>.subgroupOf X : Set X)) := by
      rw [hclosure]
      infer_instance
    have hs : (F.Vi 1).subgroupOf X ≤ (S : Subgroup X) := by
      rw [hS']; exact comap_mono hZR
    have hc : (F.Vi 1).subgroupOf X ≤ centralizer (S : Set X) := by
      intro z hz s hs
      change s ∈ (S : Subgroup X) at hs
      rw [hS'] at hs
      exact Subtype.ext (hZC hz s (hRT hs))
    rw [←hclosure]
    exact Theory.GroupTheory.isPReduced_normalClosure_of_sylow_central S _ hs hc
  have hLZ : F.Li L 1 ≤ centralizer (F.Vi 1 : Set G) :=
    ((F.Li_le L 1).trans inf_le_right).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
  have hLW : F.Li L 1 ≤ centralizer (W : Set G) :=
    le_centralizer_conjugateSpanBy_of_normalizes _ _ _
      (hCN.trans (extraspecial_normalizer_normalizes_point h hab structural previous faithful he)) hLZ
  let D := (pPrimeCore 3 N).map N.subtype
  have hND : N ≤ normalizer (D : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,N.range_subtype] using
      (pPrimeCore 3 N).le_normalizer_map N.subtype
  have hCD : C = F.Li L 1 ⊔ D :=
    (extraspecial_normalizer_threePrime_supplement d h hab structural previous faithful earlier he).1
  have hcopD : Nat.Coprime 3 (Nat.card D) := by
    rw [card_map_of_injective N.subtype_injective]
    exact pPrimeCore_coprime_card
  have hcopC : Nat.Coprime 3 ((centralizer (W : Set G)).relIndex C) := by
    apply (hcopD.of_dvd_right ?_).of_dvd_right (relIndex_dvd_of_le_left C hLW)
    rw [hCD,sup_comm,relIndex_sup_of_normalizes D (F.Li L 1)
      (((F.Li_le L 1).trans inf_le_right).trans ((H_normalizes_K F).trans hND))]
    exact relIndex_dvd_card _ _
  have hcopR : Nat.Coprime 3 (Nat.card (F.Ri L 1)) := by
    obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 (F.Li L 1 ⊔ (T : Subgroup G))).exists_card_eq
    rw [show Nat.card (F.Ri L 1)=2^k from hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hcopX : Nat.Coprime 3 (C.relIndex X) := by
    let : (C.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer hXC
    have hi := relIndex_sup_left ((F.Ri L 1).subgroupOf X) (C.subgroupOf X)
    rw [←subgroupOf_sup (show C ≤ X from le_sup_left) (show F.Ri L 1 ≤ X from le_sup_right),
      relIndex_subgroupOf le_rfl,relIndex_subgroupOf (show F.Ri L 1 ≤ X from le_sup_right)] at hi
    rw [hi]
    exact hcopR.of_dvd_right (relIndex_dvd_card _ _)
  refine ⟨inferInstance,hWQ,hWQcentral,hred,hLW,?_⟩
  have hp := hcopC.mul_right hcopX
  have hm := relIndex_inf_mul_relIndex (centralizer (W : Set G)) C X
  rw [inf_eq_left.mpr (show C ≤ X from le_sup_left)] at hm
  rw [hm] at hp
  exact hp.of_dvd_right (relIndex_dvd_of_le_left X inf_le_left)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource


end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Baumann control of the extraspecial residual centralizer

For the original abelian flag, the orbit W = ⟨V₁^C⟩ is reduced in C R₁
and its faithful action has order prime to three. The three-free FF theorem
therefore makes J(R₁) centralize W. The exact seed centralizer is O₂(C R₁):
its full centralizer lies in H, and the literal residual action confines
C ∩ H to L₁ O₂(H). Baumann heredity now identifies Baum(R₁) with
Baum(O₂(C R₁)), putting C inside N_G(L).

No normality of C R₁ in N_G(K) is needed. All action kernels and subgroup
intersections are those of the original group and flag.

Source: Aschbacher–Smith, proof of 14.7.21(1), printed p.1050.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u

private theorem ExtraspecialNormalizerBaumann_thompson_centralizes_reduced_three_free_action
    {X : Type u} [Group X] [Finite X]
    (W : Subgroup X) (hr : IsPReduced 2 W)
    (hsq : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hthree : Nat.Coprime 3 (centralizer (W : Set X)).index) :
    elementaryAbelianMaxJ (S : Subgroup X) ≤ centralizer (W : Set X) := by
  let := hr.normal
  let := hr.elementary
  let q := QuotientGroup.mk' (centralizer (W : Set X))
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      (X ⧸ centralizer (W : Set X)) := {
    Cover := X
    kernel := centralizer (W : Set X)
    sqtk := hsq
    equiv := MulEquiv.refl _ }
  have hn := ChapterB.SourceInduction.no_ff_of_three_free (ρ := ρ)
    (NormalElementaryQuotient.representation_injective W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))
    hr.quotient_pCore_eq_bot c hthree
  by_contra hJ
  exact hn (NormalElementaryQuotient.isFFModule_of_thompson_not_le W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (S : Subgroup X)
    (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S))
    (by simpa only [q,QuotientGroup.ker_mk'] using hJ))

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem extraspecial_normalizer_thompson_centralizes_seed
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    elementaryAbelianMaxJ (F.Ri L 1) ≤
      centralizer (conjugateSpanBy (F.Vi 1) (normalizerResidualCentralizer F) : Set G) := by
  let N := normalizer (K F : Set G)
  let C := normalizerResidualCentralizer F
  let X := C ⊔ F.Ri L 1
  let W := conjugateSpanBy (F.Vi 1) C
  obtain ⟨hw,hwQ,hwC,hr,hLC,hthree⟩ :=
    extraspecial_normalizer_central_seed_reduced d h hab structural previous faithful earlier he
  have hRY := (isSylowIn_iff.mp
    (extraspecial_normalizer_point_sylow h hab structural previous faithful he)).2.1
  have hXY : X ≤ normalizerPointCentralizer F L := sup_le
    (extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he) hRY
  have hXN : X ≤ N := hXY.trans inf_le_left
  obtain ⟨S,hS⟩ := (extraspecial_normalizer_point_sylow
    h hab structural previous faithful he).restrict le_sup_right hXY
  have hS' : (S : Subgroup X) = (F.Ri L 1).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le le_sup_right]
  have hZX : F.Vi 1 ≤ X := by
    have hz : F.Vi 1 ≤ F.Ri L 1 := le_pCoreIn_of_normalizes
      (by let := h.chosen.elementary
          let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
          exact IsElementaryAbelian.isPGroup 2 (F.Vi 1))
      ((F.le_seed 1).trans (h.chosen.le_sylow.trans le_sup_right))
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))
    exact hz.trans le_sup_right
  have hWX : W ≤ X := conjugateSpanBy_le hZX
    ((show C ≤ X from le_sup_left).trans X.le_normalizer)
  have hsq : IsSQTK KnownSimple.IsKnownSimple X :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hXN)).mp
      ((d.qtke.twoLocal_sqtk
        (extraspecial_residual_normalizer_unique d h hab structural previous faithful he).1.1).subgroup
          (X.subgroupOf N))
  have hindex : Nat.Coprime 3 (centralizer (W.subgroupOf X : Set X)).index := by
    rw [← relIndex_top_right,← relIndex_map_map_of_injective
      (centralizer (W.subgroupOf X : Set X)) ⊤ X.subtype_injective,
      map_centralizer_subtype,map_subgroupOf_eq_of_le hWX,
      ←MonoidHom.range_eq_map,range_subtype,inf_relIndex_left]
    exact hthree
  have hh := ExtraspecialNormalizerBaumann_thompson_centralizes_reduced_three_free_action (W.subgroupOf X) hr hsq S hindex
  have hm := map_mono (f := X.subtype) hh
  rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hS,
    map_centralizer_subtype,map_subgroupOf_eq_of_le hWX] at hm
  exact hm.trans inf_le_right

private theorem ExtraspecialNormalizerBaumann_normalizer_action_on_star (n : F.H)
    (x : (K F) ⧸ pCore 2 (K F)) :
    residualStarEquiv F (pCoreNormalizerAction 2 (K F) (inclusion (H_normalizes_K F) n) x) =
      MulAut.conjNormal (starMap F n) (residualStarEquiv F x) := by
  induction x using QuotientGroup.induction_on with | H k =>
    change residualStarEquiv F (pCoreNormalizerAction 2 (K F) (inclusion (H_normalizes_K F) n) (QuotientGroup.mk' _ k)) = _
    apply Subtype.ext
    rw [pCoreNormalizerAction_mk,residualStarEquiv_mk]
    change starMap F _ = starMap F n *
      (residualStarEquiv F (QuotientGroup.mk' (pCore 2 (K F)) k) : HStar F.H) * (starMap F n)⁻¹
    rw [residualStarEquiv_mk,←map_inv,←map_mul,←map_mul]
    congr 1


theorem extraspecial_normalizer_centralizer_inter_H
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizerResidualCentralizer F ⊓ F.H ≤ F.Li L 1 ⊔ F.H.pCoreIn 2 := by
  obtain ⟨e⟩ := he
  have hs := point_star_eq_center_of_extraspecial_residual h hab structural previous
    ((HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm)
    ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
    ((Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2)))
  let P := pResidual 2 (HStar F.H)
  intro x hx
  let xH : F.H := ⟨x,hx.2⟩
  have hact : pCoreNormalizerAction 2 (K F) (inclusion (H_normalizes_K F) xH) = 1 := by
    obtain ⟨n,hn,hnx⟩ := hx.1
    have hn' : n = inclusion (H_normalizes_K F) xH := Subtype.ext hnx
    exact hn' ▸ hn
  have hc : starMap F xH ∈ centralizer (P : Set (HStar F.H)) := by
    intro y hy
    obtain ⟨z,hz⟩ := (residualStarEquiv F).surjective (⟨y,hy⟩ : P)
    have hfix := ExtraspecialNormalizerBaumann_normalizer_action_on_star xH z
    rw [hact] at hfix
    have hfix' : starMap F xH * y * (starMap F xH)⁻¹ = y := by
      have hh := congrArg Subtype.val hfix.symm
      change starMap F xH * (residualStarEquiv F z : HStar F.H) *
        (starMap F xH)⁻¹ = (residualStarEquiv F z : HStar F.H) at hh
      simpa only [hz] using hh
    exact (mul_inv_eq_iff_eq_mul.mp hfix').symm
  have hp : starMap F xH ∈ P :=
    centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2) hc
  have hz : starMap F xH ∈ star F (F.Li L 1) := by
    rw [hs]
    refine ⟨⟨starMap F xH,hp⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hc y y.property)
  have hl : xH ∈ ((F.Li L 1).subgroupOf F.H) ⊔ pCore 2 F.H := by
    have hm : xH ∈ ((star F (F.Li L 1)).comap (starMap F)) := hz
    simpa only [CriticalFusion.Source.star,comap_map_eq,starMap,QuotientGroup.ker_mk'] using hm
  have hh := mem_map_of_mem F.H.subtype hl
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hLH] at hh

/-- The source seed centralizer in R₁ is exactly the two-core of C R₁. -/
theorem extraspecial_normalizer_seed_centralizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let C := normalizerResidualCentralizer F
    let X := C ⊔ F.Ri L 1
    let W := conjugateSpanBy (F.Vi 1) C
    F.Ri L 1 ⊓ centralizer (W : Set G) = X.pCoreIn 2 := by
  let C := normalizerResidualCentralizer F
  let R := F.Ri L 1
  let X := C ⊔ R
  let W := conjugateSpanBy (F.Vi 1) C
  let D := X ⊓ centralizer (W : Set G)
  let Q := R ⊓ centralizer (W : Set G)
  have hRH : R ≤ F.H := (pCoreIn_le 2 _).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))
  have hRY := (isSylowIn_iff.mp
    (extraspecial_normalizer_point_sylow h hab structural previous faithful he)).2.1
  have hXY : X ≤ normalizerPointCentralizer F L := sup_le
    (extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he) hRY
  have hXC : X ≤ normalizer (C : Set G) :=
    (hXY.trans inf_le_left).trans normalizerResidualCentralizer_normalizes
  have hRT : R ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow (F.Li L 1 ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hspan : conjugateSpanBy (F.Vi 1) X = W :=
    conjugateSpanBy_sup_of_normalizes_seed _ _ _ (hRT.trans (F.invariant 1))
      (le_sup_right.trans hXC)
  have hXW : X ≤ normalizer (W : Set G) := hspan ▸ le_normalizer_conjugateSpanBy _ _
  have hXD : X ≤ normalizer (D : Set G) :=
    (le_inf X.le_normalizer (hXW.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hDH : D ≤ F.H := inf_le_right.trans
    ((centralizer_le (le_conjugateSpanBy _ _)).trans (Subgroup.centralizer_le_normalizer _))
  have hDpoint : D ≤ F.Li L 1 ⊔ R := by
    have hprod : (X : Set G) = (R : Set G) * (C : Set G) := by
      rw [show X = R ⊔ C from sup_comm C R]
      exact coe_mul_of_left_le_normalizer_right _ _ (le_sup_right.trans hXC)
    intro x hx
    obtain ⟨r,hr,c,hc,heq⟩ := hprod ▸ hx.1
    have hcH : c ∈ F.H := by
      have hh := F.H.mul_mem (F.H.inv_mem (hRH hr)) (hDH hx)
      simpa only [←heq,inv_mul_cancel_left] using hh
    have hcL := extraspecial_normalizer_centralizer_inter_H h hab structural previous he ⟨hc,hcH⟩
    exact heq ▸ (F.Li L 1 ⊔ R).mul_mem (mem_sup_right hr)
      ((sup_le_sup_left core_le_point_core _) hcL)
  have hpointR : F.Li L 1 ⊔ R ≤ normalizer (R : Set G) :=
    (sup_le le_sup_left (pCoreIn_le 2 _)).trans
      ((F.Li L 1 ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hDQ : D ≤ normalizer (Q : Set G) :=
    (le_inf (hDpoint.trans hpointR)
      (inf_le_right.trans (centralizer (W : Set G)).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  have hQX : Q ≤ X.pCoreIn 2 :=
    (le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 (F.Li L 1 ⊔ (T : Subgroup G))).to_le inf_le_left)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right) hDQ).trans
      (pCoreIn_mono_of_normalizes inf_le_left hXD)
  obtain ⟨_,_,_,hr,_,_⟩ := extraspecial_normalizer_central_seed_reduced
    d h hab structural previous faithful earlier he
  obtain ⟨S,hS⟩ := (extraspecial_normalizer_point_sylow
    h hab structural previous faithful he).restrict le_sup_right hXY
  have hXR : X.pCoreIn 2 ≤ R := (pCoreIn_le_sylow X S).trans_eq hS
  have hWX : W ≤ X := by
    have hZR : F.Vi 1 ≤ R := le_pCoreIn_of_normalizes
      (by let := h.chosen.elementary
          let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
          exact IsElementaryAbelian.isPGroup 2 (F.Vi 1))
      ((F.le_seed 1).trans (h.chosen.le_sylow.trans le_sup_right))
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))
    exact conjugateSpanBy_le (hZR.trans le_sup_right)
      ((show C ≤ X from le_sup_left).trans X.le_normalizer)
  have hXCW : X.pCoreIn 2 ≤ centralizer (W : Set G) := by
    have hh := map_mono (f := X.subtype) (le_centralizer_iff.mp hr.le_centralizer_pCore)
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hWX] at hh
    exact hh.trans inf_le_right
  exact le_antisymm hQX (le_inf hXR hXCW)

/-- Baumann heredity for the actual source seed orbit. -/
theorem extraspecial_normalizer_baumann_core
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ChapterB.baumann (F.Ri L 1) =
      ChapterB.baumann ((normalizerResidualCentralizer F ⊔ F.Ri L 1).pCoreIn 2) := by
  let C := normalizerResidualCentralizer F
  let R := F.Ri L 1
  let X := C ⊔ R
  let W := conjugateSpanBy (F.Vi 1) C
  have hRY := (isSylowIn_iff.mp
    (extraspecial_normalizer_point_sylow h hab structural previous faithful he)).2.1
  have hXY : X ≤ normalizerPointCentralizer F L := sup_le
    (extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he) hRY
  obtain ⟨S,hS⟩ := (extraspecial_normalizer_point_sylow
    h hab structural previous faithful he).restrict le_sup_right hXY
  have hQR : X.pCoreIn 2 ≤ R := (pCoreIn_le_sylow X S).trans_eq hS
  obtain ⟨hw,_,_,hr,_,_⟩ := extraspecial_normalizer_central_seed_reduced
    d h hab structural previous faithful earlier he
  let : IsElementaryAbelian 2 W := hw
  have hZR : F.Vi 1 ≤ R := le_pCoreIn_of_normalizes
    (by let := h.chosen.elementary
        let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
        exact IsElementaryAbelian.isPGroup 2 (F.Vi 1))
    ((F.le_seed 1).trans (h.chosen.le_sylow.trans le_sup_right))
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))
  have hWX : W ≤ X := conjugateSpanBy_le (hZR.trans le_sup_right)
    ((show C ≤ X from le_sup_left).trans X.le_normalizer)
  have hWQ : W ≤ X.pCoreIn 2 := by
    have hh : (W.subgroupOf X).map X.subtype ≤ X.pCoreIn 2 :=
      map_mono (f := X.subtype) hr.le_pCore
    rwa [map_subgroupOf_eq_of_le hWX] at hh
  have hJ : elementaryAbelianMaxJ R ≤ centralizer (W : Set G) :=
    extraspecial_normalizer_thompson_centralizes_seed d h hab structural previous faithful earlier he
  have hWZ := elementary_centralizer_maxJ_le_omegaCenter R W (hWQ.trans hQR)
    (le_centralizer_iff.mp hJ)
  have hBQ : ChapterB.baumann R ≤ X.pCoreIn 2 := by
    rw [← extraspecial_normalizer_seed_centralizer d h hab structural previous faithful earlier he]
    exact le_inf inf_le_left (inf_le_right.trans (centralizer_le hWZ))
  exact (baumann_eq_of_intermediate R (X.pCoreIn 2) hBQ hQR).symm

/-- The literal residual-quotient centralizer lies in the original L-normalizer. -/
theorem extraspecial_normalizer_centralizer_le_M
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizerResidualCentralizer F ≤ normalizer (L : Set G) := by
  apply le_trans ?_ (extraspecial_baumann_normalizer d h hab structural previous earlier he)
  rw [extraspecial_normalizer_baumann_core d h hab structural previous faithful earlier he]
  let X := normalizerResidualCentralizer F ⊔ F.Ri L 1
  exact (show normalizerResidualCentralizer F ≤ X from le_sup_left).trans
    ((X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))).trans
      (normalizer_le_normalizer_baumann _))
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original extraspecial normalizer is H

Baumann control places the residual-quotient centralizer in N_G(L). The
actual three-prime supplement D = O₃′(N_G(K)) therefore acts on L/O₂(L).
Recognize the original L₁ image as a parabolic residual A₄ in SL₃(2).
Fixing its cubic quotient forces D's action to be inner in this A₄, so the
three-free action image is a two-group. Consequently O²(D) centralizes the
literal L quotient.

The commutator containment makes L normalize O²(D). Uniqueness of the
maximal two-local over LT, together with characteristic two in N_G(K),
kills this normal residual. Thus D ≤ O₂(N_G(K)) ≤ T ≤ H, and the already
proved supplement N_G(K) = H D gives N_G(K) = H and maximality of H.

This uses the original natural marking, not any later Data record. The
small quotient-action transports follow the independent argument in
Source.ResidualNormalizer.SectionCentralization, with its Data premise
replaced by the original HigherRankHypothesis.

Source: Aschbacher–Smith, 14.7.21(1), printed p.1050; the final uniqueness
argument uses the original maximal-overgroup property of LT.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
universe u
section Model
variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)
private noncomputable def ExtraspecialNormalizerEquality_modelMap (e : (L ⧸ pCore 2 L) ≃* SL) : L →* SL :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

private noncomputable def ExtraspecialNormalizerEquality_modelAction (e : (L ⧸ pCore 2 L) ≃* SL) :
    normalizer (L : Set G) →* MulAut SL :=
  (MulAut.congr e).toMonoidHom.comp ((quotientAut (pCore 2 L)).comp L.normalizerMonoidHom)

omit [Finite G] in
private theorem ExtraspecialNormalizerEquality_modelAction_apply (e : (L ⧸ pCore 2 L) ≃* SL)
    (g : normalizer (L : Set G)) (l : L) :
    ExtraspecialNormalizerEquality_modelAction L e g (ExtraspecialNormalizerEquality_modelMap L e l) = ExtraspecialNormalizerEquality_modelMap L e (L.normalizerMonoidHom g l) := by
  change e (quotientAut (pCore 2 L) (L.normalizerMonoidHom g)
    (e.symm (e (QuotientGroup.mk' (pCore 2 L) l)))) = _
  rw [e.symm_apply_apply, quotientAut_apply_mk]
  rfl

omit [Finite G] in
private theorem ExtraspecialNormalizerEquality_modelAction_inner (e : (L ⧸ pCore 2 L) ≃* SL) (l : L) :
    ExtraspecialNormalizerEquality_modelAction L e ⟨l,L.le_normalizer l.property⟩ = MulAut.conj (ExtraspecialNormalizerEquality_modelMap L e l) := by
  apply MulEquiv.ext
  intro y
  obtain ⟨a,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) y
  change ExtraspecialNormalizerEquality_modelAction L e ⟨l,L.le_normalizer l.property⟩ (ExtraspecialNormalizerEquality_modelMap L e a) =
    MulAut.conj (ExtraspecialNormalizerEquality_modelMap L e l) (ExtraspecialNormalizerEquality_modelMap L e a)
  rw [ExtraspecialNormalizerEquality_modelAction_apply]
  change ExtraspecialNormalizerEquality_modelMap L e (l * a * l⁻¹) = ExtraspecialNormalizerEquality_modelMap L e l * ExtraspecialNormalizerEquality_modelMap L e a * (ExtraspecialNormalizerEquality_modelMap L e l)⁻¹
  rw [map_mul,map_mul,map_inv]

omit [Finite G] in
private theorem ExtraspecialNormalizerEquality_modelAction_image (e : (L ⧸ pCore 2 L) ≃* SL)
    (A : Subgroup G) (hAL : A ≤ L) :
    (A.subgroupOf (normalizer (L : Set G))).map (ExtraspecialNormalizerEquality_modelAction L e) =
      ((A.subgroupOf L).map (ExtraspecialNormalizerEquality_modelMap L e)).map MulAut.conj := by
  ext α
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨ExtraspecialNormalizerEquality_modelMap L e ⟨a,hAL ha⟩, ⟨⟨a,hAL ha⟩,ha,rfl⟩, ?_⟩
    exact (ExtraspecialNormalizerEquality_modelAction_inner L e ⟨a,hAL ha⟩).symm
  · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨⟨a,L.le_normalizer a.property⟩,ha,ExtraspecialNormalizerEquality_modelAction_inner L e a⟩

omit [Finite G] in
private theorem ExtraspecialNormalizerEquality_core_subgroupOf (A : Subgroup G) (hAL : A ≤ L) :
    (A.subgroupOf L).pCoreIn 2 = (A.pCoreIn 2).subgroupOf L := by
  apply map_injective L.subtype_injective
  rw [map_pCoreIn_of_injective 2 _ L.subtype L.subtype_injective,
    map_subgroupOf_eq_of_le hAL, map_subgroupOf_eq_of_le ((pCoreIn_le 2 A).trans hAL)]

omit [Finite G] in
private theorem ExtraspecialNormalizerEquality_modelAction_preserves (e : (L ⧸ pCore 2 L) ≃* SL)
    (A : Subgroup G) (g : normalizer (L : Set G))
    (hA : (g : G) ∈ normalizer (A : Set G)) :
    ((A.subgroupOf L).map (ExtraspecialNormalizerEquality_modelMap L e)).map (ExtraspecialNormalizerEquality_modelAction L e g).toMonoidHom =
      (A.subgroupOf L).map (ExtraspecialNormalizerEquality_modelMap L e) := by
  have hle : ((A.subgroupOf L).map (ExtraspecialNormalizerEquality_modelMap L e)).map
      (ExtraspecialNormalizerEquality_modelAction L e g).toMonoidHom ≤ (A.subgroupOf L).map (ExtraspecialNormalizerEquality_modelMap L e) := by
    rintro _ ⟨_,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨L.normalizerMonoidHom g a, (mem_normalizer_iff.mp hA a).mp ha,
      (ExtraspecialNormalizerEquality_modelAction_apply L e g a).symm⟩
  apply eq_of_le_of_card_ge hle
  exact le_of_eq (card_map_of_injective (ExtraspecialNormalizerEquality_modelAction L e g).injective).symm

private theorem ExtraspecialNormalizerEquality_modelAction_fixes_section (e : (L ⧸ pCore 2 L) ≃* SL)
    (A : Subgroup G) (hAL : A ≤ L) (X : Subgroup G)
    (hc : ⁅X,A⁆ ≤ A.pCoreIn 2) (x : normalizer (L : Set G)) (hx : (x : G) ∈ X) :
    ∀ a ∈ (A.subgroupOf L).map (ExtraspecialNormalizerEquality_modelMap L e),
      ExtraspecialNormalizerEquality_modelAction L e x a * a⁻¹ ∈ ((A.subgroupOf L).map (ExtraspecialNormalizerEquality_modelMap L e)).pCoreIn 2 := by
  have hk : IsPGroup 2 (ExtraspecialNormalizerEquality_modelMap L e).ker := by
    have he : (ExtraspecialNormalizerEquality_modelMap L e).ker = pCore 2 L := by
      exact (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
    rw [he]
    exact pCore_isPGroup
  rintro _ ⟨a,ha,rfl⟩
  rw [ExtraspecialNormalizerEquality_modelAction_apply, ← map_inv, ← map_mul,
    ← map_pCoreIn_of_ker_isPGroup (ExtraspecialNormalizerEquality_modelMap L e) hk]
  apply mem_map_of_mem
  rw [ExtraspecialNormalizerEquality_core_subgroupOf L A hAL]
  exact hc (commutator_mem_commutator hx ha)

private theorem ExtraspecialNormalizerEquality_modelAction_inner_image (e : (L ⧸ pCore 2 L) ≃* SL)
    (A X : Subgroup G) (hAL : A ≤ L)
    (hn : X ≤ normalizer (A : Set G)) (hc : ⁅X,A⁆ ≤ A.pCoreIn 2)
    (P : Subgroup SL) (hP : P = pointParabolicSL ∨ P = lineParabolicSL)
    (hm : (A.subgroupOf L).map (ExtraspecialNormalizerEquality_modelMap L e) = residual P) :
    (X.subgroupOf (normalizer (L : Set G))).map (ExtraspecialNormalizerEquality_modelAction L e) ≤
      (A.subgroupOf (normalizer (L : Set G))).map (ExtraspecialNormalizerEquality_modelAction L e) := by
  rw [ExtraspecialNormalizerEquality_modelAction_image L e A hAL,hm]
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨g,hg,he⟩ := quotient_fixer_is_conj P hP (ExtraspecialNormalizerEquality_modelAction L e x)
    (by rw [← hm]; exact ExtraspecialNormalizerEquality_modelAction_preserves L e A x (hn hx))
    (by rw [← hm]; exact ExtraspecialNormalizerEquality_modelAction_fixes_section L e A hAL X hc x hx)
  exact ⟨g,hg,he.symm⟩

end Model
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialNormalizerEquality_exists_L_sylow (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : CFSG.Quasithin.Chapter12.Section02.Structural1222At CFSG.KnownSimple.IsKnownSimple T) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  obtain ⟨S,hS⟩ := (T.subtype (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G))).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer (h.sylow_normalizes_at structural))
  refine ⟨S, map_injective L.subtype_injective ?_⟩
  rw [hS,Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right,subgroupOf_map_subtype]

private theorem ExtraspecialNormalizerEquality_point_residual_marking (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : CFSG.Quasithin.Chapter12.Section02.Structural1222At CFSG.KnownSimple.IsKnownSimple T) :
    ∃ (e : (L ⧸ pCore 2 L) ≃* SL) (P : Subgroup SL),
        (P = pointParabolicSL ∨ P = lineParabolicSL) ∧
        ((F.Li L 1).subgroupOf L).map (ExtraspecialNormalizerEquality_modelMap L e) = residual P := by
  let := h.chosen.elementary
  let e₀ := h.naturalMarking.quotientEquiv.trans (slEquivLinear 3).symm
  let f := ExtraspecialNormalizerEquality_modelMap L e₀
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = pCore 2 L :=
      (MonoidHom.ker_comp_of_injective _ _ e₀.injective).trans (QuotientGroup.ker_mk' _)
    rw [he]
    exact pCore_isPGroup
  let A₀ := (F.Li L 1).subgroupOf L
  let A := A₀.map f
  have hAL : F.Li L 1 ≤ L := (F.Li_le L 1).trans inf_le_left
  have hp₀ : IsPPerfect 2 A₀ := (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
    (subgroupOfEquivOfLe hAL).symm.toMonoidHom (subgroupOfEquivOfLe hAL).symm.surjective
  have hp : IsPPerfect 2 A := hp₀.of_surjective (f.subgroupMap A₀) (f.subgroupMap_surjective A₀)
  have hqker : IsPGroup 2 (f.subgroupMap A₀).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let eA := subgroupOfEquivOfLe hAL
  let eQ := QuotientGroup.congr (pCore 2 A₀) (pCore 2 (F.Li L 1)) eA (pCore_map_iso 2 eA)
  let eImage := MonoidHom.quotientPCoreEquivOfSurjective (f.subgroupMap A₀)
    (f.subgroupMap_surjective A₀) hqker
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 :=
    (Nat.card_congr eImage.toEquiv).symm.trans
      ((Nat.card_congr eQ.toEquiv).trans (pointResidual_core_quotient_card h structural))
  obtain ⟨S,hS⟩ := ExtraspecialNormalizerEquality_exists_L_sylow h structural
  let R := S.mapSurjective (f := f) (e₀.surjective.comp (QuotientGroup.mk'_surjective _))
  have hn₀ : (S : Subgroup L) ≤ normalizer (A₀ : Set L) := by
    rw [hS]
    intro x hx
    apply mem_normalizer_iff.mpr
    intro a
    exact (mem_normalizer_iff.mp (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural) hx) a)
  have hn : (R : Subgroup SL) ≤ normalizer (A : Set SL) :=
    (map_mono hn₀).trans (le_normalizer_map f)
  obtain ⟨_,_,_,_,g,P,hP,_,hmark,_,_⟩ := ResidualRecognition.recognize A R hp hc hn
  refine ⟨e₀.trans (MulAut.conj g),P,hP,?_⟩
  change A₀.map ((MulAut.conj g).toMonoidHom.comp f) = residual P
  rw [← map_map]
  exact hmark

private theorem ExtraspecialNormalizerEquality_threeFree_residual_centralizes_marked_quotient
    (e : (L ⧸ pCore 2 L) ≃* SL) (A D : Subgroup G)
    (hAL : A ≤ L) (hDM : D ≤ normalizer (L : Set G))
    (hn : D ≤ normalizer (A : Set G)) (hc : ⁅D,A⁆ ≤ A.pCoreIn 2)
    (hthree : Nat.Coprime 3 (Nat.card D))
    (P : Subgroup SL) (hP : P = pointParabolicSL ∨ P = lineParabolicSL)
    (hm : (A.subgroupOf L).map (ExtraspecialNormalizerEquality_modelMap L e) = residual P) :
    ⁅L,(pResidual 2 D).map D.subtype⁆ ≤ L.pCoreIn 2 := by
  let f : D →* MulAut SL := (ExtraspecialNormalizerEquality_modelAction L e).comp (inclusion hDM)
  have hI : f.range ≤ (residual P).map MulAut.conj := by
    rintro _ ⟨x,rfl⟩
    have hx := ExtraspecialNormalizerEquality_modelAction_inner_image L e A D hAL hn hc P hP hm
      (mem_map_of_mem (ExtraspecialNormalizerEquality_modelAction L e) (show inclusion hDM x ∈ D.subgroupOf (normalizer (L : Set G)) from x.property))
    rwa [ExtraspecialNormalizerEquality_modelAction_image L e A hAL,hm] at hx
  have h12 : Nat.card (residual P) = 12 := by
    rcases hP with rfl | rfl
    · exact card_point_residual
    · exact card_line_residual
  have hdiv : Nat.card f.range ∣ 12 := by
    have hd := (card_dvd_of_le hI).trans ((residual P).card_map_dvd MulAut.conj)
    rwa [h12] at hd
  have hcop : Nat.Coprime 3 (Nat.card f.range) := hthree.of_dvd_right
    (card_dvd_of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hp : IsPGroup 2 f.range := isPGroup_iff_card_dvd_pow.mpr
    ⟨2, hcop.symm.dvd_of_dvd_mul_left (show Nat.card f.range ∣ 3 * 2 ^ 2 from hdiv)⟩
  have hker : pResidual 2 D ≤ f.ker := sInf_le
    ⟨inferInstance, hp.of_equiv (QuotientGroup.quotientKerEquivRange f).symm⟩
  rw [commutator_comm]
  apply commutator_le.mpr
  rintro x ⟨y,hy,rfl⟩ l hl
  let a : normalizer (L : Set G) := inclusion hDM y
  let b : L := ⟨l,hl⟩
  have ha : ExtraspecialNormalizerEquality_modelAction L e a = 1 := hker hy
  have hf : ExtraspecialNormalizerEquality_modelMap L e (L.normalizerMonoidHom a b) = ExtraspecialNormalizerEquality_modelMap L e b := by
    rw [← ExtraspecialNormalizerEquality_modelAction_apply,ha]
    rfl
  have hq : (L.normalizerMonoidHom a b) / b ∈ pCore 2 L := by
    apply QuotientGroup.eq_iff_div_mem.mp
    exact e.injective hf
  exact mem_map.mpr ⟨(L.normalizerMonoidHom a b) / b,hq,by
    change ((y : G) * l * (y : G)⁻¹) / l = ⁅(y : G),l⁆
    rw [div_eq_mul_inv,commutatorElement_def]⟩

/-- The residual of the actual three-prime supplement fixes the original
L/O₂(L), using the actual point-parabolic marking. -/
theorem extraspecial_normalizer_threePrime_residual_action
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let N := normalizer (K F : Set G)
    let D := (pPrimeCore 3 N).map N.subtype
    ⁅L,(pResidual 2 D).map D.subtype⁆ ≤ L.pCoreIn 2 := by
  let N := normalizer (K F : Set G)
  let D := (pPrimeCore 3 N).map N.subtype
  have hDC : D ≤ normalizerResidualCentralizer F := by
    rw [(extraspecial_normalizer_threePrime_supplement d h hab structural previous faithful earlier he).1]
    exact le_sup_right
  have hDM := hDC.trans (extraspecial_normalizer_centralizer_le_M d h hab structural previous faithful earlier he)
  have hDY := hDC.trans (extraspecial_normalizer_residualCentralizer_le_pointCentralizer
    h hab structural previous faithful he)
  have hn : D ≤ normalizer (F.Li L 1 : Set G) := (hDY.trans inf_le_left).trans
    (extraspecial_normalizer_normalizes_point h hab structural previous faithful he)
  have hc : ⁅D,F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2 := by
    rw [commutator_comm]
    apply commutator_le_core_of_pCoreNormalizerAction_eq_one 2 (F.Li L 1) D hn
    intro x
    obtain ⟨a,ha,heq⟩ := (hDY x.property).2
    exact (show a = inclusion hn x from Subtype.ext heq) ▸ ha
  have hthree : Nat.Coprime 3 (Nat.card D) := by
    rw [card_map_of_injective N.subtype_injective]
    exact pPrimeCore_coprime_card
  obtain ⟨e,P,hP,hm⟩ := ExtraspecialNormalizerEquality_point_residual_marking (F := F) h structural
  exact ExtraspecialNormalizerEquality_threeFree_residual_centralizes_marked_quotient e (F.Li L 1) D
    ((F.Li_le L 1).trans inf_le_left) hDM hn hc hthree P hP hm

/-- The source three-prime supplement is contained in the original Sylow
subgroup: uniqueness kills its two-residual. -/
theorem extraspecial_normalizer_threePrime_le_core
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let N := normalizer (K F : Set G)
    (pPrimeCore 3 N).map N.subtype ≤ N.pCoreIn 2 := by
  let N := normalizer (K F : Set G)
  let D := (pPrimeCore 3 N).map N.subtype
  let Y := (pResidual 2 D).map D.subtype
  have hDN : D ≤ N := map_subtype_le _
  have hNY : N ≤ normalizer (Y : Set G) := by
    have hND : N ≤ normalizer (D : Set G) := by
      have hh := (pPrimeCore 3 N).le_normalizer_map N.subtype
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,N.range_subtype] using hh
    exact hND.trans (normalizer_le_normalizer_characteristic_image D (pResidual 2 D))
  have hND : N ≤ normalizer (D : Set G) := by
    have hh := (pPrimeCore 3 N).le_normalizer_map N.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,N.range_subtype] using hh
  have hTN : (T : Subgroup G) ≤ N := (F.invariant 1).trans (H_normalizes_K F)
  have hQ : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer (h.sylow_normalizes_at structural))
  have hQN : L.pCoreIn 2 ≤ N := by
    have hh := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] at hh
    exact hQ.trans (hh.trans hTN)
  have hLY : L ≤ normalizer (Y : Set G) := normalizes_residual_of_commutator_le_two
    L N D (L.pCoreIn 2) hND hQN (isPGroup_pCoreIn 2 L)
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    (extraspecial_normalizer_threePrime_residual_action d h hab structural previous faithful earlier he)
  have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  have hNmax := (extraspecial_residual_normalizer_unique d h hab structural previous faithful he).1
  have hself : N ⊓ centralizer (N.pCoreIn 2 : Set G) ≤ N.pCoreIn 2 :=
    mem_He_iff.mpr (d.qtke.evenCharacteristic T N hNmax hTN)
  have hY : Y = ⊥ := normal_eq_bot_of_unique_core (L ⊔ (T : Subgroup G)) N
    (normalizer (L : Set G)) Y
    (fun M hM hAM => Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
      show M ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ L ⊔ (T : Subgroup G) ≤ M} from ⟨hM,hAM⟩))
    (fun hn => h.flag_escape_at F previous ((H_normalizes_K F).trans hn)) hself
    ((map_subtype_le _).trans hDN) hNY (sup_le hLY (hTN.trans hNY))
  have hres : pResidual 2 D = ⊥ := (map_eq_bot_iff_of_injective _ D.subtype_injective).mp hY
  have hp : IsPGroup 2 D := (isPGroup_quotient_pResidual (G := D) 2).of_injective
    (QuotientGroup.mk' (pResidual 2 D)) (by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk',hres])
  exact le_pCoreIn_of_normalizes hp hDN hND

/-- Source 14.7.21(1): the full extraspecial residual normalizer is the
original point normalizer, which is a maximal two-local subgroup. -/
theorem extraspecial_normalizer_eq_H
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizer (K F : Set G) = F.H ∧ IsMaximalTwoLocal F.H := by
  let N := normalizer (K F : Set G)
  have hTN : (T : Subgroup G) ≤ N := (F.invariant 1).trans (H_normalizes_K F)
  have hQT : N.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN] using
      pCoreIn_le_sylow N (T.subtype hTN)
  have heq : N = F.H := by
    change normalizer (K F : Set G) = F.H
    rw [(extraspecial_normalizer_threePrime_supplement d h hab structural previous faithful earlier he).2.1]
    exact sup_eq_left.mpr ((extraspecial_normalizer_threePrime_le_core
      d h hab structural previous faithful earlier he).trans (hQT.trans (F.invariant 1)))
  exact ⟨heq,heq ▸ (extraspecial_residual_normalizer_unique d h hab structural previous faithful he).1⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The extraspecial source centralizer and its central four-group

The normalizer equality and the previously proved center containment give
both clauses of 14.7.21 for the original group and flag. The order-four
subgroup chosen after 14.7.25 lies in T and has exact normalizer H.

The first branches of 14.7.26 are then proved. A cyclic choice is TI because
its unique involution generates V₁. A choice centralized by T is centralized
by H = KT, so maximal two-local uniqueness gives the TI property. Otherwise
the choice is elementary, and its order-two quotient by V₁ shows that its
nontrivial T-commutator is exactly V₁. The TI assertion in this last branch
and the subsequent extraspecial exclusion are not asserted here.

Source: Aschbacher–Smith, 14.7.21, 14.7.25 and the opening of 14.7.26,
printed pp.1050–1052; I.6.1, printed p.424.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Both clauses of 14.7.21 on the original group and flag. The centralizer
is that of the actual order-two seed. -/
theorem extraspecial_source_14721
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizer (K F : Set G) = F.H ∧
      F.H = centralizer (F.Vi 1 : Set G) ∧ IsMaximalTwoLocal F.H ∧
      (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype ≤
        (center (K F)).map (K F).subtype := by
  obtain ⟨hN,hH⟩ := extraspecial_normalizer_eq_H d h hab structural previous faithful earlier he
  exact ⟨hN,le_antisymm
    (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
    (Subgroup.centralizer_le_normalizer _),hH,
    extraspecial_core_center_central d h hab structural previous faithful earlier he⟩

/-- The order-four subgroup selected after 14.7.25 has the exact original
normalizer H and lies in T. -/
theorem extraspecial_center_four_normalizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ D ≤ (T : Subgroup G) ∧ normalizer (D : Set G) = F.H := by
  obtain ⟨D,hZD,hDK,hcard,hHD⟩ := extraspecial_center_four d h hab structural previous faithful earlier he
  have hp : IsPGroup 2 D := isPGroup_iff_card_dvd_pow.mpr ⟨2,by rw [hcard]; decide⟩
  have hne : D ≠ ⊥ := by intro heq; simp [heq] at hcard
  have hmax := (extraspecial_normalizer_eq_H d h hab structural previous faithful earlier he).2
  have hDH : D ≤ F.H := hDK.trans ((map_subtype_le _).trans (K_le_H F))
  have hDT : D ≤ (T : Subgroup G) :=
    (le_pCoreIn_of_normalizes hp hDH hHD).trans
      ((pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
        (map_subgroupOf_eq_of_le (F.invariant 1)))
  exact ⟨D,hZD,hDK,hcard,hDT,le_antisymm (hmax.2 ⟨D,hne,hp,rfl⟩ hHD) hHD⟩
/-- The source four-group is TI in the cyclic and Sylow-central branches.
The remaining branch is elementary and has exact displacement V₁. -/
theorem extraspecial_center_four_ti_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ D ≤ (T : Subgroup G) ∧ normalizer (D : Set G) = F.H ∧
      (IsTISubgroup D ∨ (IsElementaryAbelian 2 D ∧
        ⁅D,(T : Subgroup G)⁆ = F.Vi 1 ∧ ¬ D ≤ centralizer (T : Set G))) := by
  obtain ⟨D,hZD,hDK,hcard,hDT,hND⟩ := extraspecial_center_four_normalizer
    d h hab structural previous faithful earlier he
  refine ⟨D,hZD,hDK,hcard,hDT,hND,?_⟩
  have hp : IsPGroup 2 D := isPGroup_iff_card_dvd_pow.mpr ⟨2,by rw [hcard]; decide⟩
  have hHnD : F.H ≤ normalizer (D : Set G) := hND.ge
  have hTnD := (F.invariant 1).trans hHnD
  have hZcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  by_cases hcyc : IsCyclic D
  · let := hcyc
    exact Or.inl (cyclic_two_TI_of_point_normalizer D (F.Vi 1) hp hZcard hZD hHnD)
  by_cases hc : D ≤ centralizer (T : Set G)
  · left
    have hHC : F.H ≤ centralizer (D : Set G) := by
      rw [residual_product F]
      apply sup_le ?_ (le_centralizer_iff.mp hc)
      apply le_centralizer_iff.mpr
      rw [map_center_subtype_eq_inf_centralizer] at hDK
      exact hDK.trans inf_le_right
    have hmax := (extraspecial_normalizer_eq_H d h hab structural previous faithful earlier he).2
    exact lemma_I_6_1_2 D F.H F.H hp hND.symm hmax le_rfl
      (fun M hM hHM => le_antisymm (hmax.2 hM.1 hHM) hHM) hHC
  right
  have hele : IsElementaryAbelian 2 D := {
    toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard
    exponent_dvd_p := ((not_isCyclic_iff_exponent_eq_prime Nat.prime_two hcard).mp hcyc).dvd }
  let Z := (F.Vi 1).subgroupOf D
  have hnZ : Z.Normal := normal_subgroupOf_of_le_normalizer (hDT.trans (F.invariant 1))
  let := hnZ
  have hzcard : Nat.card Z = 2 := (Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv).trans hZcard
  have hquot : Nat.card (D ⧸ Z) ≤ 2 := by
    have hh := Z.card_mul_index
    rw [hzcard,hcard] at hh
    change Z.index ≤ 2
    omega
  have hcomm : ⁅D,(T : Subgroup G)⁆ ≤ F.Vi 1 :=
    commutator_le_of_normalized_quotient_card_le_two (T : Subgroup G) D (F.Vi 1)
      hTnD (F.invariant 1) hnZ hquot
  have hne : ⁅D,(T : Subgroup G)⁆ ≠ ⊥ := fun heq => hc
    (commutator_eq_bot_iff_le_centralizer.mp heq)
  have hccard := commutator_four_card_of_ne_bot D (T : Subgroup G) hTnD T.isPGroup' hcard hne
  exact ⟨hele,eq_of_le_of_card_ge hcomm (by rw [hZcard,hccard]),hc⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end
