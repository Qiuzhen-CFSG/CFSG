module
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.Subgroup.Actions
/-!
# Prime-rank obstruction for two factors with split outer action

A prime-order outer pair has a lift of the same order through the given
section. The fixed-point congruence supplies a prime-order element fixed
in each centerless factor. Together their inner automorphisms and the
outer lift generate an elementary subgroup of rank three. Thus ambient
prime rank at most two makes the outer image prime-to-p.

This generalizes the checked PSL2.PairedOuterPrime argument while retaining
the actual quotient map and its section. TwoOrbitOddPrime.SplitOuter and
the original Chapter 10 Suzuki Hall kernel are the consumers.
Source: Aschbacher--Smith 1.2.2(a), printed p.504; application 10.1.3, p.742.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.SplitOuterPair
variable (S : Type*) [Group S]
@[expose] def projection : MulAut S × MulAut S →* MulAut.Outer S × MulAut.Outer S :=
  (QuotientGroup.mk' (MulAut.innerSubgroup S)).prodMap (QuotientGroup.mk' (MulAut.innerSubgroup S))
variable {S}
@[expose] def sectionMap (s : MulAut.Outer S →* MulAut S) := s.prodMap s
variable (s : MulAut.Outer S →* MulAut S)
  (hs : ∀ x, QuotientGroup.mk' (MulAut.innerSubgroup S) (s x) = x)
include s hs
theorem projection_section (x : MulAut.Outer S × MulAut.Outer S) :
    projection S (sectionMap s x) = x := Prod.ext (hs x.1) (hs x.2)
theorem section_injective : Function.Injective (sectionMap s) := by
  intro x y h
  have hh := congrArg (projection S) h
  simpa only [projection_section s hs] using hh
omit s hs in
theorem projection_ker : (projection S).ker = (MulAut.innerSubgroup S).prod (MulAut.innerSubgroup S) := by
  ext a
  change (QuotientGroup.mk' _ a.1,QuotientGroup.mk' _ a.2) = (1,1) ↔ _
  rw [Prod.mk.injEq,QuotientGroup.mk'_apply,QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff,QuotientGroup.eq_one_iff]
  rfl
theorem section_mem_of_full_inner
    (A : Subgroup (MulAut S × MulAut S))
    (hI : (MulAut.innerSubgroup S).prod (MulAut.innerSubgroup S) ≤ A)
    (x : MulAut.Outer S × MulAut.Outer S) (hx : x ∈ A.map (projection S)) :
    sectionMap s x ∈ A := by
  have hk : (projection S).ker ≤ A := (projection_ker (S := S)).trans_le hI
  have hm : sectionMap s x ∈ (A.map (projection S)).comap (projection S) := by
    change projection S (sectionMap s x) ∈ A.map (projection S)
    rwa [projection_section s hs]
  rwa [comap_map_eq_self hk] at hm
variable [Finite S] (p : ℕ) [Fact p.Prime]
omit s hs in
private theorem exists_fixed_prime {S : Type*} [_root_.Group S] [Finite S]
    (α : MulAut S) (hα : α ^ p = 1) (hd : p ∣ Nat.card S) :
    ∃ x : S, orderOf x = p ∧ α x = x := by
  let P := zpowers α
  have hP : IsPGroup p P := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [P,Nat.card_zpowers,pow_one] using orderOf_dvd_of_pow_eq_one hα)
  have hc := hP.card_modEq_card_fixedPoints S
  have hd' : p ∣ Nat.card (FixedPoints.subgroup P S) :=
    Nat.modEq_zero_iff_dvd.mp (hc.symm.trans hd.modEq_zero_nat)
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' p hd'
  exact ⟨x,(orderOf_injective (FixedPoints.subgroup P S).subtype
    Subtype.val_injective x).trans hx,x.property ⟨α,mem_zpowers α⟩⟩

/-- A prime-order outer pair adds a third independent prime-order actor to
fixed inner actors in the two factors. -/
theorem image_coprime (hz : center S = ⊥)
    (A : Subgroup (MulAut S × MulAut S))
    (hI : (MulAut.innerSubgroup S).prod (MulAut.innerSubgroup S) ≤ A) (hr : primeRank p A ≤ 2)
    (hd : p ∣ Nat.card S) :
    Nat.Coprime p (Nat.card (A.map (projection S))) := by
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hdiv
  let π := projection S
  let s₂ := sectionMap s
  obtain ⟨σ,hσ⟩ := exists_prime_orderOf_dvd_card' p hdiv
  let x : A := ⟨s₂ σ,section_mem_of_full_inner s hs A hI σ σ.property⟩
  have hx : orderOf x = p := by
    rw [←orderOf_injective A.subtype A.subtype_injective x]
    change orderOf (s₂ σ.val) = p
    rw [orderOf_injective _ (section_injective s hs)]
    exact (orderOf_injective (A.map π).subtype Subtype.val_injective σ).trans hσ
  have hσpow : (σ.val) ^ p = 1 := by
    have hh := congrArg Subtype.val (hσ ▸ pow_orderOf_eq_one σ)
    exact hh
  have ha : (s σ.val.1) ^ p = 1 := by
    rw [←map_pow,show σ.val.1 ^ p = 1 from congrArg Prod.fst hσpow,map_one]
  have hb : (s σ.val.2) ^ p = 1 := by
    rw [←map_pow,show σ.val.2 ^ p = 1 from congrArg Prod.snd hσpow,map_one]
  obtain ⟨a,ha,hfa⟩ := exists_fixed_prime p (s σ.val.1) ha hd
  obtain ⟨b,hb,hfb⟩ := exists_fixed_prime p (s σ.val.2) hb hd
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    MulAut.conj_injective_of_center_eq_bot hz
  let a' := MulAut.conj a
  let b' := MulAut.conj b
  have ha' : orderOf a' = p := (orderOf_injective _ hinj a).trans ha
  have hb' : orderOf b' = p := (orderOf_injective _ hinj b).trans hb
  let E₀ := (zpowers a').prod (zpowers b')
  let : IsElementaryAbelian p (zpowers a') :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (ha' ▸ pow_orderOf_eq_one a')
  let : IsElementaryAbelian p (zpowers b') :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hb' ▸ pow_orderOf_eq_one b')
  let eE : E₀ ≃* (zpowers a' × zpowers b') := Subgroup.prodEquiv _ _
  let : IsElementaryAbelian p E₀ := {
    toIsMulCommutative := ⟨⟨fun a b => eE.injective (by rw [map_mul,map_mul]; exact mul_comm _ _)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun y => by
      apply Subtype.ext
      exact Prod.ext (elemPow_eq_one_of_isElementaryAbelian y.val.1 y.property.1)
        (elemPow_eq_one_of_isElementaryAbelian y.val.2 y.property.2)) }
  have hEI : E₀ ≤ (MulAut.innerSubgroup S).prod (MulAut.innerSubgroup S) := by
    rintro y ⟨hy₁,hy₂⟩
    exact ⟨zpowers_le.mpr (show a' ∈ MulAut.innerSubgroup S from ⟨a,rfl⟩) hy₁,
      zpowers_le.mpr (show b' ∈ MulAut.innerSubgroup S from ⟨b,rfl⟩) hy₂⟩
  have hEA := hEI.trans hI
  let E := E₀.subgroupOf A
  let : IsElementaryAbelian p E := IsElementaryAbelian.subgroupOf hEA
  have hc : Nat.card E = p ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv,
      Nat.card_congr eE.toEquiv,Nat.card_prod,Nat.card_zpowers,Nat.card_zpowers,ha',hb',pow_two]
  have hxE : x ∉ E := by
    intro he
    have hi : s₂ σ.val ∈ π.ker := (projection_ker (S := S)).symm ▸ hEI he
    have hs : σ.val = 1 := (projection_section s hs σ).symm.trans hi
    have hs' : σ = 1 := Subtype.ext hs
    rw [hs',orderOf_one] at hσ
    exact (Fact.out : p.Prime).ne_one hσ.symm
  have hcomm (β : MulAut S) (y : S) (hy : β y = y) :
      Commute β (MulAut.conj y) := by
    apply MulEquiv.ext
    intro z
    change β (y*z*y⁻¹) = y*β z*y⁻¹
    rw [map_mul,map_mul,map_inv,hy]
  have hfix : E ≤ centralizer ({x} : Set A) := by
    intro y hy
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply Prod.ext
    · exact mem_centralizer_singleton_iff.mp
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hcomm _ a hfa).eq.symm) hy.1)
    · exact mem_centralizer_singleton_iff.mp
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hcomm _ b hfb).eq.symm) hy.2)
  have hl := IsElementaryAbelian.primeRank_ge_of_fixed_join E x hx hxE hfix hc
  omega

/-- The actual inverse image of the two inner factors has prime-to-p index. -/
theorem quotient_by_inner_preimage_coprime (hz : center S = ⊥)
    {D : Type*} [Group D] [Finite D]
    (a : D →* MulAut S × MulAut S)
    (hI : (MulAut.innerSubgroup S).prod (MulAut.innerSubgroup S) ≤ a.range)
    (hr : primeRank p a.range ≤ 2) (hd : p ∣ Nat.card S) :
    Nat.Coprime p (((MulAut.innerSubgroup S).prod (MulAut.innerSubgroup S)).comap a).index := by
  let f := (projection S).comp a
  have hk : f.ker = ((MulAut.innerSubgroup S).prod (MulAut.innerSubgroup S)).comap a := by
    rw [←MonoidHom.comap_ker,projection_ker]
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  change Nat.Coprime p (Nat.card (D ⧸ ((MulAut.innerSubgroup S).prod (MulAut.innerSubgroup S)).comap a))
  rw [Nat.card_congr e.toEquiv,MonoidHom.range_comp]
  exact image_coprime s hs p hz a.range hI hr hd
end Theory.GroupTheory.SplitOuterPair
