module

public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderSevenObstruction
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Seven-free automorphisms of a special group of order sixty-four

Suppose the center and derived subgroup coincide and form an elementary
four-group. An automorphism with seventh power one fixes that center.
Its actions on the quotients by two distinct central involution lines
are trivial by the nonabelian order-thirty-two automorphism bound.
The two literal quotient kernels intersect trivially, so the original
automorphism is the identity.

Consequently a quasisimple group whose order is divisible by seven but whose
center has order prime to seven centralizes any such group it normalizes.
This includes both SL₃(4) and PSL₃(4), without a concrete model for the
order-sixty-four group.

Source application: Aschbacher–Smith, proof of 10.2.3, printed p.747.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace SpecialSixtyFour
variable {S : Type*} [Group S] [Finite S]
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem seven_power_eq_one_small
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (hne : ¬ IsMulCommutative Q) (hc : Nat.card Q ≤ 32)
    (a : MulAut Q) (ha : a ^ 7 = 1) : a = 1 := by
  by_contra hn
  have ho : orderOf a = 7 := orderOf_eq_prime ha hn
  have hcA : Nat.card (zpowers a) = 7 := (Nat.card_zpowers a).trans ho
  exact SmallNonabelianTwoGroup.not_seven_dvd_odd_actor_card hQ hne hc
    (zpowers a) (by rw [hcA]; decide) (by rw [hcA])

private theorem fixes_center [IsElementaryAbelian 2 (center S)]
    (hc : Nat.card (center S) = 4) (a : MulAut S) (ha : a ^ 7 = 1) :
    ∀ z ∈ center S, a z = z := by
  let : Nontrivial (center S) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour (center S) := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  let b := MulAut.characteristic (center S) a
  have hb7 : b ^ 7 = 1 := by change (MulAut.characteristic (center S) a) ^ 7 = 1; rw [← map_pow, ha, map_one]
  have hb : b = 1 := by
    have hdiv7 := orderOf_dvd_of_pow_eq_one hb7
    have hdiv6 : orderOf b ∣ 6 := by
      simpa only [IsKleinFour.card_mulAut] using orderOf_dvd_natCard b
    have hdiv1 : orderOf b ∣ 1 := by
      simpa only [show Nat.gcd 7 6 = 1 by decide] using Nat.dvd_gcd hdiv7 hdiv6
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hdiv1)
  intro z hz
  exact congrArg Subtype.val (DFunLike.congr_fun hb ⟨z,hz⟩)

private theorem fixes_quotient_by_line
    (hS : Nat.card S = 64) (hderived : commutator S = center S)
    (hZ : Nat.card (center S) = 4)
    (a : MulAut S) (ha : a ^ 7 = 1)
    (hfix : ∀ z ∈ center S, a z = z)
    (N : Subgroup S) (hN : N ≤ center S) (hNcard : Nat.card N = 2) :
    ∀ x : S, x⁻¹ * a x ∈ N := by
  let : N.Normal := ⟨fun x hx g => by
    have he := mem_center_iff.mp (hN hx) g
    rw [he, mul_inv_cancel_right]
    exact hx⟩
  have hmap : N.map a.toMonoidHom = N := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change a x ∈ N
      rw [hfix x (hN hx)]
      exact hx
    · intro x hx
      exact ⟨x,hx,hfix x (hN hx)⟩
  let b : MulAut (S ⧸ N) := QuotientGroup.congr N N a hmap
  have hbpow (n : ℕ) (x : S) :
      (b ^ n) (QuotientGroup.mk' N x) = QuotientGroup.mk' N ((a ^ n) x) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, ih]
      rfl
  have hb7 : b ^ 7 = 1 := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      change (b ^ 7) (QuotientGroup.mk' N x) = QuotientGroup.mk' N x
      rw [hbpow, ha, MulAut.one_apply]
  have htwo : IsPGroup 2 S := IsPGroup.of_card (n := 6) (by simpa using hS)
  have hqcard : Nat.card (S ⧸ N) = 32 := by
    have hc := card_eq_card_quotient_mul_card_subgroup N
    rw [hS,hNcard] at hc
    omega
  have hqnon : ¬ IsMulCommutative (S ⧸ N) := by
    intro h
    have hle := Normal.quotient_commutative_iff_commutator_le.mp h
    rw [hderived] at hle
    have hc := card_le_of_le hle
    rw [hZ,hNcard] at hc
    omega
  have hb : b = 1 := seven_power_eq_one_small (htwo.to_quotient N) hqnon
    hqcard.le b hb7
  intro x
  apply QuotientGroup.eq.mp
  have he := DFunLike.congr_fun hb (QuotientGroup.mk' N x)
  exact he.symm

/-- No nonidentity automorphism has seventh power one. -/
theorem seven_power_eq_one [IsElementaryAbelian 2 (center S)]
    (hS : Nat.card S = 64) (hderived : commutator S = center S)
    (hZ : Nat.card (center S) = 4)
    (a : MulAut S) (ha : a ^ 7 = 1) : a = 1 := by
  classical
  let : Nontrivial (center S) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have ho (z : S) (hz : z ∈ center S) (hne : z ≠ 1) : orderOf z = 2 := by
    apply orderOf_eq_prime _ hne
    exact congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (center S)) ⟨z,hz⟩)
  obtain ⟨z,hz⟩ := exists_ne (1 : center S)
  have hz1 : (z : S) ≠ 1 := fun h => hz (Subtype.ext h)
  have hzcard : Nat.card (zpowers (z : S)) = 2 :=
    (Nat.card_zpowers (z : S)).trans (ho z z.property hz1)
  obtain ⟨w,hw,hwout⟩ : ∃ w ∈ center S, w ∉ zpowers (z : S) := by
    by_contra! hn
    have hc := card_le_of_le hn
    rw [hZ,hzcard] at hc
    omega
  have hw1 : w ≠ 1 := fun he => hwout (he ▸ (zpowers (z : S)).one_mem)
  have hwcard : Nat.card (zpowers w) = 2 := (Nat.card_zpowers w).trans (ho w hw hw1)
  have hdis := (zpowers (z : S)).disjoint_zpowers_of_prime_order_not_mem w (ho w hw hw1) hwout
  have hfix := fixes_center hZ a ha
  have hfz := fixes_quotient_by_line hS hderived hZ a ha hfix
    (zpowers (z : S)) (zpowers_le.mpr z.property) hzcard
  have hfw := fixes_quotient_by_line hS hderived hZ a ha hfix
    (zpowers w) (zpowers_le.mpr hw) hwcard
  apply MulEquiv.ext
  intro x
  exact (inv_mul_eq_one.mp (disjoint_def.mp hdis (hfz x) (hfw x))).symm

/-- The full automorphism group has order prime to seven. -/
theorem not_seven_dvd_card_mulAut [IsElementaryAbelian 2 (center S)]
    (hS : Nat.card S = 64) (hderived : commutator S = center S)
    (hZ : Nat.card (center S) = 4) : ¬ 7 ∣ Nat.card (MulAut S) := by
  intro hd
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := MulAut S) 7 hd
  have he := seven_power_eq_one hS hderived hZ a (orderOf_eq_prime_iff.mp ha).1
  exact (orderOf_eq_prime_iff.mp ha).2 he

/-- The quasisimple action is trivial, retaining a possible central cover. -/
theorem hom_eq_one_of_quasisimple [IsElementaryAbelian 2 (center S)]
    (hS : Nat.card S = 64) (hderived : commutator S = center S)
    (hZ : Nat.card (center S) = 4)
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hK : 7 ∣ Nat.card K) (hZK : ¬ 7 ∣ Nat.card (center K))
    (f : K →* MulAut S) : f = 1 := by
  by_contra hf
  have hk : f.ker ≤ center K :=
    (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
      (fun ht => hf (MonoidHom.ker_eq_top_iff.mp ht))
  have hker : ¬ 7 ∣ Nat.card f.ker :=
    fun hd => hZK (hd.trans (card_dvd_of_le hk))
  have hprod := f.ker.index_mul_card
  rw [index_ker] at hprod
  have hr : 7 ∣ Nat.card f.range :=
    ((show Nat.Prime 7 by decide).dvd_mul.mp (hprod.symm ▸ hK)).resolve_right hker
  exact not_seven_dvd_card_mulAut hS hderived hZ (hr.trans f.range.card_subgroup_dvd_card)

/-- Applied to literal conjugation, the quasisimple actor centralizes the group. -/
theorem le_centralizer_of_quasisimple
    {G : Type*} [Group G] [Finite G] (S K : Subgroup G)
    [IsElementaryAbelian 2 (center S)] [IsQuasisimple K]
    (hS : Nat.card S = 64) (hderived : commutator S = center S)
    (hZ : Nat.card (center S) = 4)
    (hK : 7 ∣ Nat.card K) (hZK : ¬ 7 ∣ Nat.card (center K))
    (hn : K ≤ normalizer (S : Set G)) : K ≤ centralizer (S : Set G) := by
  let f : K →* MulAut S := S.normalizerMonoidHom.comp (inclusion hn)
  have hf : f = 1 := hom_eq_one_of_quasisimple hS hderived hZ hK hZK f
  intro k hk s hs
  have he := congrArg (fun a : K →* MulAut S => ((a ⟨k,hk⟩ ⟨s,hs⟩ : S) : G)) hf
  change k * s * k⁻¹ = s at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end SpecialSixtyFour
