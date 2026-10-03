module

public import Stellmacher.Recognition.LargeTerminalLocalCharacter
public import Stellmacher.Recognition.LargeTerminalFourFixedLocalData
public import Stellmacher.Recognition.LargeTerminalReeSquaringFixedRoot
public import Theory.GroupTheory.FiveSquaringPowers
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Fourth powers of terminal squaring lifts

Write R for the first residual and Q for the second local core. At Sylow
order 4096, S/Q has order four. A fourth power in S therefore belongs to
Q, and the binary local character puts it in R. Sylow conjugacy in the
second local group transports this conclusion to every local two-element
of order dividing sixteen.

If the element induces squaring on an order-five subgroup A, its fourth
power centralizes A. The residual fixed-center hypothesis then places
that power in Z(R), of order two. Thus the lift has order four or eight,
and its fourth power is either one or the designated central involution.
The order-eight exclusion, and hence fourth power one, remains open;
these reductions do not assert that the local extension splits.

The fourth power is independent of the choice of local squaring lift.
Indeed, the local five-centralizer is the product of the five-subgroup and
its cyclic fixed four. Multiplying a lift by either factor preserves its
fourth power, whether the lift fixes or inverts the cyclic four. Thus a
single order-four witness suffices, but adjusting a bad lift inside this
normalizer cannot produce that witness.

Source: Thompson VI, pp.629–630, for the terminal local structure, and
Shinoda (1975), pp.81–83, for the eventual model. The power calculation
uses the checked binary character rather than an identification with that
model.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven Subgroup

/-- Every fourth power in the prescribed Sylow lies in the first residual. -/
public theorem LargeTerminalContext.sylow_fourth_power_mem_residual
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) (s : (S : Subgroup G)) :
    (s : G) ^ 4 ∈ ctx.firstResidual := by
  let Q := (twoCoreIn ctx.second).subgroupOf (S : Subgroup G)
  let _ : Q.Normal := ctx.local_character_core_normal
  have hQ : Nat.card Q = 1024 := ctx.local_character_core_card hS
  have hquot : Nat.card (S ⧸ Q) = 4 := by
    have hh := Q.card_eq_card_quotient_mul_card_subgroup
    rw [hS, hQ] at hh
    omega
  have hsQ : s ^ 4 ∈ Q := by
    apply (QuotientGroup.eq_one_iff _).mp
    have hh := pow_card_eq_one' (x := QuotientGroup.mk' Q s)
    rw [hquot] at hh
    change (QuotientGroup.mk' Q) (s ^ 4) = 1
    rw [map_pow]
    exact hh
  obtain ⟨χ, hχ⟩ := ctx.exists_local_character hS
  have hsQ' : ((s ^ 4 : (S : Subgroup G)) : G) ∈ twoCoreIn ctx.second := by
    simpa only [Q, mem_subgroupOf, SubgroupClass.coe_pow] using hsQ
  have hres := (hχ (s ^ 4) hsQ').mp
  have hχ4 : χ (s ^ 4) = 1 := by
    rw [map_pow]
    have hh := pow_card_eq_one' (x := χ s)
    have hh2 : χ s ^ 2 = 1 := by simpa using hh
    rw [show 4 = 2 * 2 by norm_num, pow_mul, hh2, one_pow]
  simpa only [SubgroupClass.coe_pow] using hres hχ4

/-- Sylow conjugacy transports the fourth-power containment to every local
element whose sixteenth power is one. -/
public theorem LargeTerminalContext.two_element_fourth_power_mem_residual
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (b : G) (hbP : b ∈ ctx.second) (hb16 : b ^ 16 = 1) :
    b ^ 4 ∈ ctx.firstResidual := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSP : (S : Subgroup G) ≤ ctx.second :=
    ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
  let bP : ctx.second := ⟨b, hbP⟩
  have hbP16 : bP ^ 16 = 1 := Subtype.ext hb16
  obtain ⟨n, _, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show orderOf bP ∣ 2 ^ 4 from orderOf_dvd_of_pow_eq_one hbP16)
  obtain ⟨s, hs⟩ := (S.subtype hSP).exists_isConj_of_orderOf_eq_prime_pow hn
  obtain ⟨g, hg⟩ := isConj_iff.mp hs
  let sS : S := ⟨((s : ctx.second) : G), s.property⟩
  have hsR := ctx.sylow_fourth_power_mem_residual hS sS
  have heq : (g : G) * b ^ 4 * (g : G)⁻¹ = (sS : G) ^ 4 := by
    have hh := congrArg (fun x : ctx.second => ((x : G) ^ 4)) hg
    simpa only [MulAut.conj_apply, coe_mul, coe_inv, mul_inv_cancel_right,
      conj_pow] using hh
  exact (mem_normalizer_iff.mp (ctx.second_le_residual_normalizer g.property)
    (b ^ 4)).mpr (heq.symm ▸ hsR)

/-- A squaring lift has its fourth power in the order-two residual center. -/
public theorem LargeTerminalContext.five_squaring_fourth_power_mem_residual_center
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (b : G) (hbP : b ∈ ctx.second) (hb16 : b ^ 16 = 1)
    (hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2) :
    b ^ 4 ∈ CenterAmbient ctx.firstResidual := by
  have hR := ctx.two_element_fourth_power_mem_residual hS b hbP hb16
  have hAfix := fourth_power_centralizes_five A hA b hb
  exact mem_map.mpr ⟨⟨b ^ 4, hR⟩, hfixed hAfix, rfl⟩

/-- The residual center excludes order sixteen for a squaring lift. -/
public theorem LargeTerminalContext.five_squaring_eighth_power_eq_one
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (b : G) (hbP : b ∈ ctx.second) (hb16 : b ^ 16 = 1)
    (hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2) : b ^ 8 = 1 := by
  have hZ := ctx.five_squaring_fourth_power_mem_residual_center hS A hA hfixed b hbP hb16 hb
  have hcard : Nat.card (CenterAmbient ctx.firstResidual) = 2 :=
    (card_map_of_injective ctx.firstResidual.subtype_injective).trans
      ctx.first_residual_structure.2.2.2.1
  have hh := pow_card_eq_one' (x := (⟨b ^ 4, hZ⟩ : CenterAmbient ctx.firstResidual))
  rw [hcard] at hh
  have hh' := congrArg Subtype.val hh
  simpa only [coe_pow, coe_one, ← pow_mul] using hh'

/-- The only remaining nonidentity fourth power is the designated central
involution. Excluding this case requires further local geometry. -/
public theorem LargeTerminalContext.five_squaring_fourth_power_eq_one_or_central_involution
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (b : G) (hbP : b ∈ ctx.second) (hb16 : b ^ 16 = 1)
    (hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2) : b ^ 4 = 1 ∨ b ^ 4 = z := by
  classical
  have hZ := ctx.five_squaring_fourth_power_mem_residual_center hS A hA hfixed b hbP hb16 hb
  rw [ctx.first_residual_center_eq_omegaOneCenter, ← hgen,
    mem_zpowers_iff_mem_range_orderOf] at hZ
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hZ
  have hn2 : n < 2 := hz ▸ Finset.mem_range.mp hn
  interval_cases n
  · exact Or.inl (by simpa using he.symm)
  · exact Or.inr (by simpa using he.symm)

/-- A local squaring lift of two-power order has order four or eight. -/
public theorem LargeTerminalContext.five_squaring_order_four_or_eight
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (b : G) (hbP : b ∈ ctx.second) (hb16 : b ^ 16 = 1)
    (hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2) : orderOf b = 4 ∨ orderOf b = 8 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hb4 : b ^ 4 = 1
  · exact Or.inl (orderOf_eq_four_of_squares_five A hA b hb hb4)
  · exact Or.inr (orderOf_eq_prime_pow (p := 2) (n := 2) hb4
      (ctx.five_squaring_eighth_power_eq_one hS A hA hfixed b hbP hb16 hb))

open scoped Pointwise

private theorem mul_fourth_power_eq_of_fixed_or_inverted {G : Type*} [Group G] (b d : G) (hd : d ^ 4 = 1)
    (hb : b * d * b⁻¹ = d ∨ b * d * b⁻¹ = d⁻¹) :
    (d * b) ^ 4 = b ^ 4 := by
  rcases hb with hb | hb
  · have hc : Commute d b := (mul_inv_eq_iff_eq_mul.mp hb).symm
    rw [hc.mul_pow, hd, one_mul]
  · have hs : (d * b) ^ 2 = b ^ 2 := by
      calc
        (d * b) ^ 2 = d * (b * d * b⁻¹) * b ^ 2 := by simp only [pow_two]; group
        _ = b ^ 2 := by rw [hb]; group
    rw [show 4 = 2 * 2 by decide, pow_mul, hs, ← pow_mul]

/-- All local squaring lifts have the same fourth power. This needs neither
a bound on their orders nor a choice of central involution. -/
public theorem LargeTerminalContext.five_squaring_fourth_power_eq
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (t : G) (htQ : t ∈ twoCoreIn ctx.second)
    (htA : t ∈ centralizer (A : Set G)) (ht4 : orderOf t = 4)
    (a b : G) (haP : a ∈ ctx.second) (haN : a ∈ normalizer (A : Set G))
    (hbP : b ∈ ctx.second)
    (ha : ∀ c ∈ A, a * c * a⁻¹ = c ^ 2)
    (hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2) : b ^ 4 = a ^ 4 := by
  have hdA : a⁻¹ * b ∈ centralizer (A : Set G) := by
    apply mem_centralizer_iff.mpr
    intro c hc
    have hh : (a⁻¹ * b) * c * (a⁻¹ * b)⁻¹ = c := by
      calc
        _ = a⁻¹ * (b * c * b⁻¹) * a := by group
        _ = a⁻¹ * (a * c * a⁻¹) * a := by rw [hb c hc, ha c hc]
        _ = c := by group
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hd : a⁻¹ * b ∈ A ⊔ zpowers t := by
    rw [← ctx.five_local_centralizer_eq_sup_fixed_root hS A hA hAP hcard t htQ htA ht4]
    exact ⟨ctx.second.mul_mem (ctx.second.inv_mem haP) hbP, hdA⟩
  have hTA : zpowers t ≤ centralizer (A : Set G) := zpowers_le.mpr htA
  have hprod : a⁻¹ * b ∈ (A : Set G) * (zpowers t : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A (zpowers t)
      (hTA.trans (Subgroup.centralizer_le_normalizer _))]
    exact hd
  obtain ⟨c, hc, d, hd, hcd⟩ := hprod
  obtain ⟨n, rfl⟩ := hd
  change c * t ^ n = a⁻¹ * b at hcd
  have htnA : t ^ n ∈ centralizer (A : Set G) := zpow_mem htA n
  have htn4 : (t ^ n) ^ 4 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      show t ^ 4 = 1 from ht4 ▸ pow_orderOf_eq_one t, one_zpow]
  have hat : a * t ^ n * a⁻¹ = t ^ n ∨ a * t ^ n * a⁻¹ = (t ^ n)⁻¹ := by
    rcases ctx.five_fixed_root_conjugate_eq_self_or_inv A hcard a t
      haP haN htQ htA ht4 with ht | ht
    · left
      calc
        _ = (a * t * a⁻¹) ^ n := (conj_zpow (a := a) (b := t) (i := n)).symm
        _ = t ^ n := by rw [ht]
    · right
      calc
        _ = (a * t * a⁻¹) ^ n := (conj_zpow (a := a) (b := t) (i := n)).symm
        _ = (t ^ n)⁻¹ := by rw [ht, inv_zpow]
  have hca : a * c * a⁻¹ = c ^ 2 := ha c hc
  have hbform : b = c ^ 2 * (a * t ^ n) := by
    calc
      b = a * (c * t ^ n) := by rw [hcd]; group
      _ = (a * c * a⁻¹) * (a * t ^ n) := by group
      _ = c ^ 2 * (a * t ^ n) := by rw [hca]
  have ha' : ∀ e ∈ A, (a * t ^ n) * e * (a * t ^ n)⁻¹ = e ^ 2 := by
    intro e he
    have hte : t ^ n * e * (t ^ n)⁻¹ = e :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp htnA e he).symm
    calc
      _ = a * (t ^ n * e * (t ^ n)⁻¹) * a⁻¹ := by group
      _ = e ^ 2 := by rw [hte, ha e he]
  have hat' : (a * t ^ n) ^ 4 = a ^ 4 := by
    have hh := mul_fourth_power_eq_of_fixed_or_inverted a (t ^ n) htn4 hat
    calc
      _ = a * (t ^ n * a) ^ 4 * a⁻¹ := by
        simp only [pow_succ, pow_zero]
        group
      _ = a ^ 4 := by rw [hh]; group
  rw [hbform, mul_fourth_power_eq_of_squares_five A hA (a * t ^ n) ha' (c ^ 2)
    (pow_mem hc 2), hat']

/-- A single order-four squaring witness settles the fourth-power calculation
for every local squaring lift, with no order restriction on the latter. The
existence of the witness remains a geometric hypothesis. -/
public theorem LargeTerminalContext.five_squaring_fourth_power_eq_one_of_witness
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (hgood : ∃ a : G, a ∈ ctx.second ∧ a ∈ normalizer (A : Set G) ∧
      a ^ 4 = 1 ∧ ∀ c ∈ A, a * c * a⁻¹ = c ^ 2)
    (b : G) (hbP : b ∈ ctx.second)
    (hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2) : b ^ 4 = 1 := by
  obtain ⟨t, htQ, htA, _, ht4, _, _⟩ :=
    ctx.exists_five_fixed_root_of_cyclic A hAN hcard hcyc hfixed z hz hgen
  obtain ⟨a, haP, haN, ha4, ha⟩ := hgood
  exact (ctx.five_squaring_fourth_power_eq hS A hA hAP hcard
    t htQ htA ht4 a b haP haN hbP ha hb).trans ha4

end Stellmacher.Recognition
