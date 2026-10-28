module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.ProperAlignment
public import Theory.GroupTheory.CComponent.ProperNormalizerIndex
public import Theory.GroupTheory.SylowIndexTwoExtension

/-!
# The lower Sylow-index bound for the placed component pair

Proper alignment gives Kplus < K^g with both intrinsic two-core quotients
isomorphic to the original binary linear-three group. The general perfect
coset-action bound gives index at least eight in O₂(K^g) for its component
normalizer. Monotonicity transfers this to the literal opposite core Q^g.

Both components are now normal in Mc. Every two-subgroup S of the common
point centralizer therefore normalizes Kplus and lies in Mc^g. The product
Q^g S is a two-group, of order at least 8|S|, and is bounded by the order of
the original Sylow T. This proves the source lower bound without requiring
a separate identification of the common centralizer's perfect residual.

The reverse-endpoint rank comparison and the incompatible index-four
bound on p.1041 remain with qt-e-suitable-component-marking, together with
construction of the explicit 14.6.20--23 action markings. Final suitable
choice assembly remains with qt-e-suitable-existence.
Source: Aschbacher--Smith 14.6.24(3), printed pp.1040--1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryLinearThree.NaturalDual
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The literal opposite two-core has index at least eight over its
intersection with the opposite component normalizer. Properness and all
quotient comparisons are discharged here from the original marked pair. -/
theorem source_placedEndpoint_normalizer_index
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
    8 ≤ (normalizer (Kplus : Set G)).relIndex (p.endpoint.conjugate (Mc.pCoreIn 2)) := by
  have hp := source_placedEndpoint_proper_alignment
    hG T hempty hM hunique hmany hcard e hab K Kplus p hKM hKplusM hcomp hcompPlus
    hcross c N m hN hperm κ₁ κ₂ hκrange₁ hκrange₂ hl₁ hr₁ hl₂ hr₂
    hpair hZ₁ hZ₂ hS₁ hS₂ hK hKplus a ha
  let i := p.endpoint
  let J := i.conjugate K
  let Hg := i.conjugate Mc
  have hJH : J ≤ Hg := map_mono hKM
  have hJ : (J.subgroupOf Hg).IsCComponent :=
    hcomp.map_relative_equiv Mc K hKM (MulAut.conj i.representative)
  let ek := K.equivMapOfInjective (MulAut.conj i.representative).toMonoidHom
    (MulAut.conj i.representative).injective
  let eqk := ek.toMonoidHom.pCoreQuotientEquiv (p := 2) ek.surjective
    (IsPGroup.ker_isPGroup_of_injective ek.injective)
  have hc : Nat.card (J ⧸ pCore 2 J) ≤ Nat.card (Kplus ⧸ pCore 2 Kplus) := by
    exact ((Nat.card_congr (eqk.symm.trans eK).toEquiv).trans
      (Nat.card_congr eKplus.toEquiv).symm).le
  let : Group.IsPerfect (Kplus.subgroupOf Mc) := hcompPlus.perfect
  let : Group.IsPerfect Kplus := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKplusM).toMonoidHom) (subgroupOfEquivOfLe hKplusM).surjective
  have hB : Kplus ≠ ⊥ := by
    intro hz
    have hh := hcompPlus.ne_bot
    rw [hz,bot_subgroupOf] at hh
    exact hh rfl
  have hi := eight_le_core_relIndex_of_proper_relative_cComponent Hg Kplus J
    (normalizer (Kplus : Set G)) hJH hJ hB hp.1 hc le_rfl
  have hQ : J.pCoreIn 2 ≤ i.conjugate (Mc.pCoreIn 2) := by
    have hh := pCoreAmbient_mono_of_isSubnormalIn J Hg 2 hJH hJ.subnormal
    change J.pCoreIn 2 ≤ Hg.pCoreIn 2 at hh
    change J.pCoreIn 2 ≤ (Mc.pCoreIn 2).map (MulAut.conj i.representative).toMonoidHom
    rwa [AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (MulAut.conj i.representative).injective Mc] at hh
  exact hi.trans (relIndex_le_of_le_right hQ index_ne_zero_of_finite)

/-- Every two-subgroup of the literal common point centralizer has order
at most one eighth of the original Sylow order. Normality of Kplus in Mc
supplies its normalization, so no separate residual-identification premise
is needed for this numerical bound. -/
theorem source_placedEndpoint_common_two_subgroup_bound
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
    (eKplus : (Kplus ⧸ pCore 2 Kplus) ≃* BinaryLinearThree.Group)
    (S : Subgroup G) (hS : IsPGroup 2 S)
    (hSC : S ≤ centralizer
      ((centralInvolutions T ⊔ p.endpoint.conjugate (centralInvolutions T) : Subgroup G) : Set G)) :
    8 * Nat.card S ≤ Nat.card T := by
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSH : S ≤ Mc := by
    rw [hMc]
    exact hSC.trans (Subgroup.centralizer_le (fun _ hx => mem_sup_left hx))
  have hSHg : S ≤ p.endpoint.conjugate Mc :=
    le_conjugate_of_point_support Mc (centralInvolutions T)
      (p.endpoint.conjugate (centralInvolutions T)) S hMc
      p.endpoint.representative le_rfl
      (hSC.trans (Subgroup.centralizer_le (fun _ hx => mem_sup_right hx)))
  have hp := source_placedEndpoint_proper_alignment
    hG T hempty hM hunique hmany hcard e hab K Kplus p hKM hKplusM hcomp hcompPlus
    hcross c N m hN hperm κ₁ κ₂ hκrange₁ hκrange₂ hl₁ hr₁ hl₂ hr₂
    hpair hZ₁ hZ₂ hS₁ hS₂ hK hKplus a ha
  have hi := source_placedEndpoint_normalizer_index
    hG T hempty hM hunique hmany hcard e hab K Kplus p hKM hKplusM hcomp hcompPlus
    hcross c N m hN hperm κ₁ κ₂ hκrange₁ hκrange₂ hl₁ hr₁ hl₂ hr₂
    hpair hZ₁ hZ₂ hS₁ hS₂ hK hKplus a ha eK eKplus
  let i := p.endpoint
  let Hg := i.conjugate Mc
  let Qg := i.conjugate (Mc.pCoreIn 2)
  have hQeq : Qg = Hg.pCoreIn 2 :=
    (AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (MulAut.conj i.representative).injective Mc).symm
  have hSn : S ≤ normalizer (Kplus : Set G) := hSH.trans
    ((normal_subgroupOf_iff_le_normalizer hKplusM).mp hp.2.2.2.1)
  have hindex : 8 ≤ S.relIndex Qg := hi.trans
    (relIndex_le_of_le_left hSn index_ne_zero_of_finite)
  have hSQ : S ≤ normalizer (Qg : Set G) := by
    rw [hQeq]
    exact hSHg.trans (Hg.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image Hg (pCore 2 Hg)))
  have hQp : IsPGroup 2 Qg := (isPGroup_pCoreIn 2 Mc).map _
  have hjoin : IsPGroup 2 (Qg ⊔ S : Subgroup G) :=
    hQp.to_sup_of_normal_left' hS hSQ
  have hsize := card_le_sylow_two hjoin T
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) S (Qg ⊔ S) bot_le le_sup_right
  rw [relIndex_bot_left,relIndex_bot_left,relIndex_sup_of_normalizes_left Qg S hSQ] at hcard
  calc
    8 * Nat.card S ≤ S.relIndex Qg * Nat.card S := Nat.mul_le_mul_right _ hindex
    _ = Nat.card (Qg ⊔ S : Subgroup G) := by rw [Nat.mul_comm,hcard]
    _ ≤ Nat.card T := hsize

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
