module
public import Theory.GroupTheory.Commutator.CentralElementaryFourQuotient
public import Theory.GroupAction.Quotient
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.PGroup

/-!
# Derived containment from a central four quotient and coprime fixed points

Let Z≤W≤Q be finite ambient subgroups with Z central in Q and [W,Q]≤Z.
Keep the supplied normality witness and elementary order-four quotient Q/W.
A three-group T normalizes Q and Z, Q is a two-group, and C_Q(T)≤Z.
Then [Q,Q]≤Z. No action on W by T, abelianness of Q/Z, or additional
fixed-point lifting premise is assumed.

Pass to the literal quotient Q/Z. The image of W is central, and the
canonical third isomorphism identifies its quotient with the supplied
Q/W. The central elementary-four extension theorem bounds the derived
subgroup of Q/Z by two. This characteristic subgroup is fixed pointwise
by every automorphism. On the named conjugation action induced by T,
coprime fixed-point lifting through the central kernel Z identifies the
quotient fixed subgroup with the image of C_Q(T), which is trivial.
Consequently the derived subgroup of Q/Z is trivial; the native quotient
kernel criterion gives the asserted ambient commutator containment.

This source-neutral lemma supplies the order-four fixed-factor step in
Stellmacher (10.1), Journal of Algebra190 (1997), printed p.64, the proof
of (19) following (18). Its graph consumer supplies the actual factors
C_U(Di), C_V(Di), central line, and opposite three-subgroup.
-/

namespace Subgroup
open scoped commutatorElement IsMulCommutative

private theorem automorphism_apply_eq_of_card_le_two
    {K : Type*} [Group K] [Finite K] (hcard : Nat.card K≤2) (f:MulAut K) (k:K) :
    f k=k := by
  by_cases hone : Nat.card K≤1
  · let _ := Finite.card_le_one_iff_subsingleton.mp hone
    exact Subsingleton.elim _ _
  have htwo : Nat.card K=2 := by omega
  obtain ⟨z,_hzne,hunique⟩ := (Nat.card_eq_two_iff' (1:K)).mp htwo
  by_cases hk : k=1
  · rw [hk,f.map_one]
  have hfk : f k≠1 := fun h => hk (f.injective (h.trans f.map_one.symm))
  exact (hunique _ hfk).trans (hunique _ hk).symm

public theorem commutator_le_of_central_four_quotient_coprime_fixed
    {G : Type*} [Group G] [Finite G]
    (Q W Z T : Subgroup G) (hZW : Z≤W) (hWQ : W≤Q)
    (hZcentral : Z≤centralizer (Q:Set G)) (hWcomm : ⁅W,Q⁆≤Z)
    (hQ : IsPGroup 2 Q) (hT : IsPGroup 3 T)
    (hTQ : T≤normalizer (Q:Set G)) (hTZ : T≤normalizer (Z:Set G))
    (hfixed : Q⊓centralizer (T:Set G)≤Z)
    (hN : (W.subgroupOf Q).Normal) :
    let _ := hN
    IsElementaryAbelian 2 (Q ⧸ W.subgroupOf Q) →
      Nat.card (Q ⧸ W.subgroupOf Q)=4 → ⁅Q,Q⁆≤Z := by
  classical
  let _ := hN
  dsimp only
  intro helementary hcard
  let _ := helementary
  let ZQ := Z.subgroupOf Q
  let WQ := W.subgroupOf Q
  have hZQ : Z≤Q := hZW.trans hWQ
  have hZcenter : ZQ≤center Q := by
    intro z hz
    apply mem_center_iff.mpr
    intro q
    exact Subtype.ext (mem_centralizer_iff.mp (hZcentral hz) q q.property)
  let _ : ZQ.Normal := ⟨fun z hz q => by
    rw [mem_center_iff.mp (hZcenter hz) q,mul_inv_cancel_right]
    exact hz⟩
  let _ : IsMulCommutative ZQ := ⟨⟨fun x y => Subtype.ext
    (mem_center_iff.mp (hZcenter x.property) y).symm⟩⟩
  let X := Q ⧸ ZQ
  let π : Q→*X := QuotientGroup.mk' ZQ
  let N := WQ.map π
  let _ : N.Normal := (inferInstance : WQ.Normal).map π (QuotientGroup.mk'_surjective ZQ)
  have hNcenter : N≤center X := by
    rintro _ ⟨w,hw,rfl⟩
    apply mem_center_iff.mpr
    intro x
    obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective ZQ x
    apply (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
    rw [←map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hWcomm (commutator_mem_commutator hw q.property)
  have hZWnative : ZQ≤WQ := fun _ hz => hZW hz
  let equiv : (X ⧸ N) ≃* (Q ⧸ WQ) :=
    QuotientGroup.quotientQuotientEquivQuotient ZQ WQ hZWnative
  let _ : IsElementaryAbelian 2 (X ⧸ N) := {
    toIsMulCommutative := ⟨⟨fun x y => equiv.injective (by simp only [map_mul,mul_comm])⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      equiv.injective (by
        rw [map_pow,map_one]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (Q ⧸ WQ)) (equiv x))) }
  have hcardX : Nat.card (X ⧸ N)=4 := (Nat.card_congr equiv.toEquiv).trans hcard
  have hderivedCard : Nat.card (_root_.commutator X)≤2 :=
    card_commutator_le_two_of_central_elementary_four_quotient N hNcenter hcardX
  let action := conjMulDistribMulActionOfLeNormalizer T Q hTQ
  let _ : MulDistribMulAction T Q := action
  let _ : SMul T Q := action.toSMul
  let _ : MulAction T Q := action.toMulAction
  have hZinvariant : IsInvariant T Q ZQ := by
    constructor
    intro t q
    change (q:G)∈Z ↔ (t:G)*(q:G)*(t:G)⁻¹∈Z
    exact mem_normalizer_iff.mp (hTZ t.property) q
  let quotientAction := quotientMulDistribMulAction (A:=T) ZQ hZinvariant
  let _ : MulDistribMulAction T X := quotientAction
  let _ : SMul T X := quotientAction.toSMul
  let _ : MulAction T X := quotientAction.toMulAction
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hcop : Nat.Coprime (Nat.card T) (Nat.card ZQ) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) T ZQ hT
      (hQ.to_subgroup ZQ)
  have hsourceFixed : FixedPoints.subgroup T Q≤ZQ := by
    intro q hq
    apply hfixed
    refine ⟨q.property,mem_centralizer_iff.mpr ?_⟩
    intro t ht
    have hh := congrArg Subtype.val (hq ⟨t,ht⟩)
    change t*(q:G)*t⁻¹=(q:G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hquotientFixed : FixedPoints.subgroup T X=⊥ := by
    rw [fixedPoints_subgroup_quotient_eq_map_of_isMulCommutative ZQ hZinvariant hcop]
    apply bot_unique
    have hh := map_mono (f:=π) hsourceFixed
    rw [QuotientGroup.map_mk'_self] at hh
    exact hh
  let D := _root_.commutator X
  let _ : IsInvariant T X D := isInvariant_of_characteristic D
  have hderivedFixed : D≤FixedPoints.subgroup T X := by
    intro d hd t
    have hh := automorphism_apply_eq_of_card_le_two hderivedCard
      (MulDistribMulAction.toMulAut T D t) (⟨d,hd⟩:D)
    exact congrArg Subtype.val hh
  have hderivedBot : _root_.commutator X=⊥ := bot_unique (hderivedFixed.trans hquotientFixed.le)
  apply commutator_le.mpr
  intro q hq r hr
  have hh : ⁅π (⟨q,hq⟩:Q),π (⟨r,hr⟩:Q)⁆∈_root_.commutator X :=
    commutator_mem_commutator (mem_top _) (mem_top _)
  rw [hderivedBot,mem_bot,←map_commutatorElement] at hh
  change ⁅(⟨q,hq⟩:Q),(⟨r,hr⟩:Q)⁆∈ZQ
  exact (QuotientGroup.eq_one_iff _).mp hh
end Subgroup
