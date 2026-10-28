module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSylowIrreducibility
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Source.Complete
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction
public import CFSG.Quasithin.Chapter1.Section03
public import Theory.GroupAction.NormalizerFrattiniTransport

/-!
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
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private def residualFrattiniEquiv (F : InvariantFlag T V 3) :
    XiFrattiniQuotient (K F) ≃*
      ((pResidual 2 (HStar F.H)) ⧸ frattini (pResidual 2 (HStar F.H))) :=
  QuotientGroup.congr _ _ (residualStarEquiv F) (frattini_map_mulEquiv _)

private theorem residualFrattiniEquiv_action
    (hn : (T : Subgroup G) ≤ normalizer (K F : Set G))
    (t : T) (x : XiFrattiniQuotient (K F)) :
    residualFrattiniEquiv F (xiFrattiniAction (T : Subgroup G) (K F) hn t x) =
      quotientAut (frattini (pResidual 2 (HStar F.H)))
        (MulAut.conjNormal (starMap F ⟨t,F.invariant 1 t.property⟩))
        (residualFrattiniEquiv F x) := by
  induction x using QuotientGroup.induction_on with | H x =>
    induction x using QuotientGroup.induction_on with | H k =>
      change residualFrattiniEquiv F (xiFrattiniAction (T : Subgroup G) (K F) hn t
        (QuotientGroup.mk' _ (QuotientGroup.mk' _ k))) =
          quotientAut (frattini (pResidual 2 (HStar F.H)))
            (MulAut.conjNormal (starMap F ⟨t,F.invariant 1 t.property⟩))
            (residualFrattiniEquiv F (QuotientGroup.mk' _ (QuotientGroup.mk' _ k)))
      simp only [xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk,
        residualFrattiniEquiv,QuotientGroup.congr_mk']
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    exact (F.H_mem_Hz (by decide) L (normalizer (L : Set G)) (h.flag_escape F previous)).1.1
  · intro A hA
    let eF := residualFrattiniEquiv F
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
        (residualFrattiniEquiv F y) ∈ A.map eF.toMonoidHom
      rw [←residualFrattiniEquiv_action hn ⟨t,htT⟩]
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
