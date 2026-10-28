module

public import CFSG.Quasithin.ChapterC.Section01.NaturalPointControl.ClassificationExclusions
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Bounds

/-!
# The chief-factor consequence of the natural-point MS alternatives

The natural or doubled-natural commutator core has order at most 64 and
contains the original normal eight. Cubic additivity bounds its movement by
two. All cubic commutators on the ambient two-core lie in this core, so the
same bound holds there. An embedded component subgroup has a two-core image
in SL₃(2) of order at most eight, contributing at most one further layer.
When its two-core quotient has order three, every complete chief series
therefore has at most three noncentral two-factors.

Every quotient and fixed index is formed from the displayed subgroup and
homomorphism. OriginalSource.ChiefBound applies this to the literal L₁ in the
original LT setup. The independent MS classifier is supplied by its source owner.

Source: Aschbacher--Smith C.1.37, pp.141--143, and 14.7.10, p.1045.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.NaturalPointControl
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open NoncentralChiefRefinement NoncentralChiefRefinement.CubicComparison
universe u
variable {G : Type u} [Group G] [Finite G] {V : Subgroup G} [V.Normal]
  [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem section_card {B W F : Type*} [Group B] [AddCommGroup W]
    [Field F] [Module F W] {K D : Subgroup G} {actor : K →* B}
    {rho : Representation F B W} (hm : HasSectionModel K D ⊥ actor rho) :
    Nat.card D = Nat.card W := by
  obtain ⟨_,_,_,hn,e,_⟩ := hm
  let := hn
  let f : D ≃* Multiplicative W := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf D).symm).trans e)
  exact Nat.card_congr f.toEquiv

omit [Finite G] in
private theorem msQ_eq {κ : GroupClass.{u}} {K R : Subgroup G}
    (h : BinaryMS.Input κ K R) : msQ K R = BinaryMS.commutatorCore K := by
  rw [msQ,h.sup_eq_top]
  rw [show (⊤ : Subgroup G).pCoreIn 2 = pCore 2 G from pCore_map_iso 2 topEquiv]

namespace NaturalAction
variable (d : NaturalAction V)

omit [Finite G] in
/-- The surviving two source models have commutator core of order at most 64. -/
theorem core_card_le_of_models {κ : GroupClass.{u}} {K R : Subgroup G}
    (h : BinaryMS.Input κ K R)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := ZMod 2) 3) ∨
      HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
        ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
          (Representation.specialLinearNatural (k := ZMod 2) 3))) :
    Nat.card (BinaryMS.commutatorCore K) ≤ 64 := by
  rw [← msQ_eq h]
  rcases hm with hm | hm
  · rw [section_card hm]
    simp
  · rw [section_card hm]
    simp

include d in
/-- Every cubic in the original component moves at most two binary chief
layers on the actual ambient two-core. -/
theorem core_length_le_two {κ : GroupClass.{u}} {K R : Subgroup G}
    (h : BinaryMS.Input κ K R) (hc : Nat.card (BinaryMS.commutatorCore K) ≤ 64)
    (A : Subgroup G) (hA : IsPGroup 3 A) (hAK : A ≤ K) :
    conjugationCubicLength A (pCore 2 G) ≤ 2 := by
  let := h.component_normal
  let Q := BinaryMS.commutatorCore K
  have hQ : Q ≤ pCore 2 G := commutator_le_left _ _
  have hVQ : V ≤ Q := (d.module_le_center_core h).trans (map_subtype_le _)
  have hn : conjugationCubicLength A Q ≤ 2 :=
    length_le_two_of_normal_eight A Q V hA
      (pCore_isPGroup.of_injective (inclusion hQ) (inclusion_injective _)) hVQ
      le_normalizer_of_normal le_normalizer_of_normal d.module_card hc
  rw [← length_eq_of_commutator_le A (pCore 2 G) Q hA pCore_isPGroup hQ
    le_normalizer_of_normal le_normalizer_of_normal (commutator_mono le_rfl hAK)]
  exact hn

private theorem two_subgroup_card_le_eight (P : Subgroup Matrix.PSL3Two.SL)
    (hp : IsPGroup 2 P) : Nat.card P ≤ 8 := by
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hc : Nat.card (S : Subgroup Matrix.PSL3Two.SL) = 8 := by
    rw [S.card_eq_multiplicity, Matrix.PSL3Two.card_SL]
    decide +kernel
  exact (Nat.card_le_card_of_injective (inclusion hS) (inclusion_injective _)).trans_eq hc

include d in
/-- Bound complete chief series of an actual embedded subgroup of the component.
Its two-core quotient has order three; all cubic movement is transported by f. -/
theorem chief_count_le_three {κ : GroupClass.{u}} {K R : Subgroup G}
    (h : BinaryMS.Input κ K R) (hc : Nat.card (BinaryMS.commutatorCore K) ≤ 64)
    {H : Type*} [Group H] [Finite H] (f : H →* G) (hf : Function.Injective f)
    (hfK : f.range ≤ K) (hq : Nat.card (H ⧸ pCore 2 H) = 3)
    (s : ChiefSeries H) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 3 := by
  have hd : 3 ∣ Nat.card H := by
    rw [← hq, ← index_eq_card]
    exact (pCore 2 H).index_dvd_card
  obtain ⟨A,hA⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := 1) (by simpa using hd)
  have hA3 : Nat.card A = 3 := by simpa using hA
  have hpA : IsPGroup 3 A := IsPGroup.of_card hA
  let N : Subgroup H := (pCore 2 G).comap f
  have hpN : IsPGroup 2 N := pCore_isPGroup.comap_of_injective f hf
  have hNU : N ≤ pCore 2 H := le_sSup ⟨inferInstance, hpN⟩
  have hN : conjugationCubicLength A N ≤ 2 := by
    rw [← length_map_injective f hf]
    exact (conjugationCubicLength_mono (A.map f) (map_comap_le _ _)).trans
      (d.core_length_le_two h hc (A.map f) (hpA.map f) ((map_le_range _ _).trans hfK))
  let φ : pCore 2 H →* Matrix.PSL3Two.SL := (d.q.comp f).comp (pCore 2 H).subtype
  have hk : φ.ker = N.subgroupOf (pCore 2 H) := by
    ext x
    change d.q (f x) = 1 ↔ f x ∈ pCore 2 G
    rw [← d.kernel]
    rfl
  have hφ : IsPGroup 2 φ.range :=
    pCore_isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hquot : Nat.card (pCore 2 H ⧸ N.subgroupOf (pCore 2 H)) ≤ 8 := by
    rw [← hk, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact two_subgroup_card_le_eight φ.range hφ
  have hsection := (section_length_le_log_card A (pCore 2 H) N hpA pCore_isPGroup hNU
    le_normalizer_of_normal le_normalizer_of_normal).trans (Nat.log_mono_right hquot)
  norm_num at hsection
  rw [count_of_core_quotient_card_three hq A hA3 s h0 h1]
  unfold sectionCubicLength at hsection
  omega

end NaturalAction
end CFSG.Quasithin.ChapterC.NaturalPointControl
