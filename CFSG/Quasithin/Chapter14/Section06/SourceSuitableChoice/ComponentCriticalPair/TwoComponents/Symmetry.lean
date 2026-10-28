module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.SylowBound
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.PointPlacement
public import Theory.GroupTheory.PerfectCentralizingSupplement

/-!
# Strict comparison of the original terminal endpoint ranks

Proper alignment puts Kplus strictly inside the literal K^g. Their equal
intrinsic quotient orders make Kplus supplement O₂(K^g). If the original
point Z lay in U^g, the quotient action and perfectness would force K^g
to centralize Z. It would then normalize Kplus inside H=C_G(Z), contrary
to the proved core-normalizer index bound.

In the equal-rank case F.9 reversal exchanges the two ranks. The same
paired support marking places its point in U. Transporting by the same
reverse conjugator gives Z≤U^g, the contradiction just obtained. Thus the
denominator rank is strictly smaller than the actor rank.

All markings remain explicit earlier 14.6.20--23 inputs. Their construction,
the identification of the natural/dual summands, and the remaining terminal branches
belong to qt-e-suitable-component-marking; final suitable-choice assembly
belongs to qt-e-suitable-existence. No component exclusion is asserted here.
Source: Aschbacher--Smith 14.6.24(3), printed pp.1040--1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryLinearThree.NaturalDual
variable {G : Type*} [Group G] [Finite G]

/-- A proper aligned component excludes the original point from the opposite
module. Core commutators lie only in the opposite point; perfectness is
needed to remove that remaining central action. -/
theorem point_not_le_opposite_module_of_proper_alignment
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (K B : Subgroup G) (i : h.CriticalEndpoint)
    (hH : D.H = centralizer (D.V₁ : Set G))
    (hKH : K ≤ D.H) (hBH : B ≤ D.H)
    (hK : (K.subgroupOf D.H).IsCComponent)
    (hB : (B.subgroupOf D.H).IsCComponent)
    (hproper : B < i.conjugate K)
    (hn : D.H ≤ normalizer (B : Set G))
    (hc : Nat.card (i.conjugate K ⧸ pCore 2 (i.conjugate K)) ≤
      Nat.card (B ⧸ pCore 2 B)) :
    ¬ D.V₁ ≤ i.conjugate D.UH := by
  intro hZU
  let J := i.conjugate K
  let Hg := i.conjugate D.H
  let Qg := i.conjugate D.QH
  let Zg := i.conjugate D.V₁
  have hJH : J ≤ Hg := map_mono hKH
  have hJ : (J.subgroupOf Hg).IsCComponent :=
    hK.map_relative_equiv D.H K hKH (MulAut.conj i.representative)
  let : Group.IsPerfect (J.subgroupOf Hg) := hJ.perfect
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hJH).toMonoidHom) (subgroupOfEquivOfLe hJH).surjective
  let : Group.IsPerfect (B.subgroupOf D.H) := hB.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBH).toMonoidHom) (subgroupOfEquivOfLe hBH).surjective
  have hBQ : B ⊔ J.pCoreIn 2 = J :=
    sup_twoCoreIn_eq_of_quotient_card_le B J hproper.le hc
  have hQ : J.pCoreIn 2 ≤ Qg := by
    have hh := pCoreAmbient_mono_of_isSubnormalIn J Hg 2 hJH hJ.subnormal
    change J.pCoreIn 2 ≤ Hg.pCoreIn 2 at hh
    change J.pCoreIn 2 ≤ (D.QH).map (MulAut.conj i.representative).toMonoidHom
    rwa [AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (MulAut.conj i.representative).injective D.H] at hh
  have hHgZ : Hg ≤ centralizer (Zg : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr h.H_centralizes,
      Subgroup.map_bot]
  have hQH : Qg ≤ Hg := map_mono (pCoreIn_le 2 D.H)
  have hQcomm : ⁅Qg,D.V₁⁆ ≤ Zg := by
    have hh := map_mono (f := (MulAut.conj i.representative).toMonoidHom)
      h.commutator_UH_QH_le_point
    rw [map_commutator,commutator_comm] at hh
    exact (commutator_mono le_rfl hZU).trans hh
  have hJC : J ≤ centralizer (D.V₁ : Set G) :=
    centralizes_of_perfect_supplement J B Qg D.V₁ Zg
      (hBQ.symm.le.trans (sup_le_sup_left hQ B))
      ((hproper.le.trans hJH).trans (hHgZ.trans (Subgroup.centralizer_le_normalizer _)))
      (hQH.trans (hHgZ.trans (Subgroup.centralizer_le_normalizer _)))
      (hBH.trans_eq hH) hQcomm (le_centralizer_iff.mp (hJH.trans hHgZ))
  have hJHoriginal : J ≤ D.H := hJC.trans_eq hH.symm
  have hBne : B ≠ ⊥ := by
    intro hz
    have hh := hB.ne_bot
    rw [hz,bot_subgroupOf] at hh
    exact hh rfl
  have hi := eight_le_core_relIndex_of_proper_relative_cComponent Hg B J J
    hJH hJ hBne hproper hc (hJHoriginal.trans hn)
  rw [relIndex_eq_one.mpr (pCoreIn_le 2 J)] at hi
  omega

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents

namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryLinearThree.NaturalDual
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The original two ranks are strictly unequal. The reversed endpoint is
placed using the same marked quotient and the original conjugate labels. -/
theorem source_placedEndpoint_strict_comparison
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (K Kplus : Subgroup G)
    (p : PlacedEndpoint
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) K Kplus)
    (hKM : K ≤ Mc) (hKplusM : Kplus ≤ Mc)
    (hcomp : (K.subgroupOf Mc).IsCComponent)
    (hcompPlus : (Kplus.subgroupOf Mc).IsCComponent)
    (hcross : ⁅⁅conjugateSpanBy (localModule T M) Mc,K⁆,Kplus⁆ = ⊥)
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (c : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) (ρ.comp (QuotientGroup.mk' (pCore 2 Mc))))
    (N : Subgroup (Source.Hstar Mc)) (m : Paired.Marking (ρ.comp N.subtype))
    (hN : N = subspaceStabilizer ρ m.leftEmbedding.range ⊓
      subspaceStabilizer ρ m.rightEmbedding.range)
    (hspan : m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤)
    (hperm : ∀ a : Source.Hstar Mc,
      (m.leftEmbedding.range.map (ρ a) = m.leftEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.rightEmbedding.range) ∨
      (m.leftEmbedding.range.map (ρ a) = m.rightEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.leftEmbedding.range))
    (κ₁ κ₂ : BinaryLinearThree.Group →* N)
    (hκrange₁ : (N.subtype.comp κ₁).range = Source.starImage Mc K)
    (hκrange₂ : (N.subtype.comp κ₂).range = Source.starImage Mc Kplus)
    (hl₁ : ∀ k, m.left (κ₁ k) = MulAut.conj k)
    (hr₁ : ∀ k, m.right (κ₁ k) = 1)
    (hl₂ : ∀ k, m.left (κ₂ k) = 1)
    (hr₂ : ∀ k, m.right (κ₂ k) = MulAut.conj k)
    (hpair : ∀ J : Subgroup Mc, J.IsCComponent →
      J = K.subgroupOf Mc ∨ J = Kplus.subgroupOf Mc)
    (hZ₁ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hZ₂ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆)
    (hS₁ : c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = m.leftEmbedding.range)
    (hS₂ : c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆ = m.rightEmbedding.range)
    (hK : (normalizer (K : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.leftEmbedding.range).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (hKplus : (normalizer (Kplus : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.rightEmbedding.range).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (a : N) (ha : m.left a ∉ MulAut.innerSubgroup BinaryLinearThree.Group)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eKplus : (Kplus ⧸ pCore 2 Kplus) ≃* BinaryLinearThree.Group) :
    Nat.log 2 ((conjugateSpanBy (localModule T M) Mc ⊓
      p.endpoint.conjugate (Mc.pCoreIn 2)).relIndex (conjugateSpanBy (localModule T M) Mc)) <
    rank (Source.starImage Mc (p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc))) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  let h : D.Hypothesis := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 D.UH :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab
    Mc (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
  have hp := source_placedEndpoint_proper_alignment
    hG T hempty hM hunique hmany hcard e hab K Kplus p hKM hKplusM hcomp hcompPlus
    hcross c N m hN hperm κ₁ κ₂ hκrange₁ hκrange₂ hl₁ hr₁ hl₂ hr₂
    hpair hZ₁ hZ₂ hS₁ hS₂ hK hKplus a ha
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let ek := K.equivMapOfInjective (MulAut.conj p.endpoint.representative).toMonoidHom
    (MulAut.conj p.endpoint.representative).injective
  let eqk := ek.toMonoidHom.pCoreQuotientEquiv (p := 2) ek.surjective
    (IsPGroup.ker_isPGroup_of_injective ek.injective)
  have hc : Nat.card (p.endpoint.conjugate K ⧸ pCore 2 (p.endpoint.conjugate K)) ≤
      Nat.card (Kplus ⧸ pCore 2 Kplus) :=
    ((Nat.card_congr (eqk.symm.trans eK).toEquiv).trans
      (Nat.card_congr eKplus.toEquiv).symm).le
  have hnot := point_not_le_opposite_module_of_proper_alignment h K Kplus p.endpoint hMc
    hKM hKplusM hcomp hcompPlus hp.1
    ((normal_subgroupOf_iff_le_normalizer hKplusM).mp hp.2.2.2.1) hc
  apply lt_of_le_of_ne p.comparison
  intro heq
  let q := quadraticEndpointOfComparison h p.endpoint hb rfl c p.comparison
  obtain ⟨j,hlabels,hd,ha⟩ := endpoint_reverse_indices h p.endpoint hb q.not_le_core
  have hjcmp : Nat.log 2 ((D.UH ⊓ j.conjugate D.QH).relIndex D.UH) ≤
      rank (Source.starImage D.H (j.conjugate D.UH)) := by
    change rank (Source.starImage D.H (j.conjugate D.UH)) = _ at ha
    rw [hd,ha,heq]
  have hplace := source_pairPointPlacement_of_paired_supports
    hG T hempty hM hunique hmany hcard e hab c N m hN hspan hperm
    K Kplus hZ₁ hZ₂ hS₁ hS₂
  have hjU : j.conjugate D.V₁ ≤ D.UH := by
    rcases hplace j (j.denominator_positive h hb rfl) hjcmp with hl | hr
    · exact hl.trans (le_normalizer_iff_commutator_le_left.mp
        (hKM.trans (le_normalizer_conjugateSpanBy _ _)))
    · exact hr.trans (le_normalizer_iff_commutator_le_left.mp
        (hKplusM.trans (le_normalizer_conjugateSpanBy _ _)))
  have hU := hlabels D.UH (le_normalizer_conjugateSpanBy _ _)
  apply hnot
  have hh : j.conjugate D.V₁ ≤ j.conjugate (p.endpoint.conjugate D.UH) := by
    rwa [hU]
  exact (map_le_map_iff_of_injective (MulAut.conj j.representative).injective).mp hh
/-- The literal denominator has index two and the original star actor has
rank two, with strict comparison discharged by the reversal argument. -/
theorem source_placedEndpoint_denominator_and_actor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (K Kplus : Subgroup G)
    (p : PlacedEndpoint
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) K Kplus)
    (hKM : K ≤ Mc) (hKplusM : Kplus ≤ Mc)
    (hcomp : (K.subgroupOf Mc).IsCComponent)
    (hcompPlus : (Kplus.subgroupOf Mc).IsCComponent)
    (hcross : ⁅⁅conjugateSpanBy (localModule T M) Mc,K⁆,Kplus⁆ = ⊥)
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (c : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) (ρ.comp (QuotientGroup.mk' (pCore 2 Mc))))
    (N : Subgroup (Source.Hstar Mc)) (m : Paired.Marking (ρ.comp N.subtype))
    (hN : N = subspaceStabilizer ρ m.leftEmbedding.range ⊓
      subspaceStabilizer ρ m.rightEmbedding.range)
    (hspan : m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤)
    (hperm : ∀ a : Source.Hstar Mc,
      (m.leftEmbedding.range.map (ρ a) = m.leftEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.rightEmbedding.range) ∨
      (m.leftEmbedding.range.map (ρ a) = m.rightEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.leftEmbedding.range))
    (κ₁ κ₂ : BinaryLinearThree.Group →* N)
    (hκrange₁ : (N.subtype.comp κ₁).range = Source.starImage Mc K)
    (hκrange₂ : (N.subtype.comp κ₂).range = Source.starImage Mc Kplus)
    (hl₁ : ∀ k, m.left (κ₁ k) = MulAut.conj k)
    (hr₁ : ∀ k, m.right (κ₁ k) = 1)
    (hl₂ : ∀ k, m.left (κ₂ k) = 1)
    (hr₂ : ∀ k, m.right (κ₂ k) = MulAut.conj k)
    (hpair : ∀ J : Subgroup Mc, J.IsCComponent →
      J = K.subgroupOf Mc ∨ J = Kplus.subgroupOf Mc)
    (hZ₁ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hZ₂ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆)
    (hS₁ : c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = m.leftEmbedding.range)
    (hS₂ : c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆ = m.rightEmbedding.range)
    (hK : (normalizer (K : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.leftEmbedding.range).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (hKplus : (normalizer (Kplus : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.rightEmbedding.range).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (a : N) (ha : m.left a ∉ MulAut.innerSubgroup BinaryLinearThree.Group)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eKplus : (Kplus ⧸ pCore 2 Kplus) ≃* BinaryLinearThree.Group) :
    (conjugateSpanBy (localModule T M) Mc ⊓ p.endpoint.conjugate (Mc.pCoreIn 2)).relIndex
      (conjugateSpanBy (localModule T M) Mc) = 2 ∧
    rank (Source.starImage Mc (p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc))) = 2 := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  let h : D.Hypothesis := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 D.UH :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hs := source_placedEndpoint_strict_comparison
    hG T hempty hM hunique hmany hcard e hab K Kplus p hKM hKplusM hcomp hcompPlus
    hcross c N m hN hspan hperm κ₁ κ₂ hκrange₁ hκrange₂ hl₁ hr₁ hl₂ hr₂
    hpair hZ₁ hZ₂ hS₁ hS₂ hK hKplus a ha eK eKplus
  exact ⟨p.index_eq_two_of_strict_comparison hs,p.actor_rank_eq_two_of_strict_comparison hs⟩
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
