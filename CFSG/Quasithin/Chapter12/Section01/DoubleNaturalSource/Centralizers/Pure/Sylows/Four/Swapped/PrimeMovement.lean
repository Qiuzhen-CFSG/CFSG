module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.MovingActor
public import Theory.Representation.BinaryPrimeDisplacement

/-!
# Prime displacement for the moving component

A prime-order element of a component and its conjugate commute and have
trivial diagonal intersection. Their commutator with the swapping involution
still has that prime order. Binary prime displacement bounds the order of two
modulo the prime by twice the involution's fixed codimension.

For the source congruences p = 11 or 13 modulo 24, the six-dimensional bound
leaves only p = 11 or 13. The actor then has rank three, its stabilizer has
rank two, and the involution moves at least five dimensions. These are the
precise bounds consumed by `DiagonalExclusion` on the original action.
Source: Aschbacher--Smith D.3.5--9 and 12.1.4,
printed pp.195--201,790--791 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

/-- Moving a centerless component forces the characteristic-prime binary
order into at most twice the involution displacement. -/
theorem moving_component_prime_displacement
    {Q U : Type*} [Group Q] [Finite Q] [AddCommGroup U]
    [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (hf : Function.Injective ρ)
    (C : Subgroup Q) (hC : IsComponent Q C) (hz : center C = ⊥)
    (a : Q) (han : a ∉ normalizer (C : Set Q))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdiv : p ∣ Nat.card C) :
    orderOf (2 : ZMod p) ≤ 2 * fixedCodim ρ (zpowers a) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := C) p hdiv
  let D := C.map (MulAut.conj a).toMonoidHom
  have hne : D ≠ C := fun he => han (mem_normalizer_iff_map_conj_eq.mpr he)
  have hc : D ≤ centralizer (C : Set Q) :=
    commutator_eq_bot_iff_le_centralizer.mp ((hC.map_conj a).commutator_eq_bot_of_ne hC hne)
  let y := (MulAut.conj a) (x : Q)
  have hy : y ∈ D := mem_map_of_mem _ x.property
  have hxy : Commute y (x : Q)⁻¹ :=
    ((mem_centralizer_iff.mp (hc hy)) _ (C.inv_mem x.property)).symm
  have hxp : (x : Q) ^ p = 1 := by
    exact congrArg Subtype.val (hx ▸ pow_orderOf_eq_one x)
  have hyp : y ^ p = 1 := by
    change ((MulAut.conj a).toMonoidHom (x : Q)) ^ p = 1
    rw [←map_pow,hxp,map_one]
  have hpw : (y * (x : Q)⁻¹) ^ p = 1 := by rw [hxy.mul_pow,hyp,inv_pow,hxp,inv_one,mul_one]
  have hyne : y * (x : Q)⁻¹ ≠ 1 := by
    intro he
    have he' : y = (x : Q) := mul_inv_eq_one.mp he
    have hxZ : x ∈ center C := mem_center_iff.mpr (fun z =>
      Subtype.ext ((he' ▸ hc hy) z z.property))
    have hx1 : x = 1 := mem_bot.mp (hz ▸ hxZ)
    rw [hx1,orderOf_one] at hx
    exact hp.ne_one hx.symm
  have hyorder : orderOf (y * (x : Q)⁻¹) = p := orderOf_eq_prime hpw hyne
  have hb := prime_order_le_fixedCodim ρ hf hp hp2 _ hyorder
  exact hb.trans (fixedCodim_commutator_le_twice ρ a (x : Q))

private theorem rank_one_characteristic_dvd
    {C : Type*} [Group C] [Finite C] {p : ℕ}
    (_hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL C 2 p) : p ∣ Nat.card C := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ ho)
  have hd : p ∣ 2 * Nat.card C := by
    rw [mul_comm 2, Nat.card_congr e.toEquiv,hc,hF]
    exact dvd_mul_right p _
  exact ho.coprime_two_right.dvd_mul_left.mp hd

/-- The source prime congruences and six-dimensional displacement leave
only eleven and thirteen; no component classification is used here. -/
theorem prime_eq_eleven_or_thirteen_of_binary_order
    {p : ℕ} (hp : p.Prime) (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hd : orderOf (2 : ZMod p) ≤ 12) : p = 11 ∨ p = 13 := by
  let : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hh := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have := Nat.le_of_dvd (by decide : 0 < 2) hh
    omega
  have hpos : 0 < orderOf (2 : ZMod p) :=
    (isUnit_iff_ne_zero.mpr htwo).isOfFinOrder.orderOf_pos
  have hpow := pow_orderOf_eq_one (2 : ZMod p)
  generalize hn : orderOf (2 : ZMod p) = n at *
  have hdiv : p ∣ 2 ^ n - 1 := by
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    rw [Nat.cast_sub (by have hh : 0 < 2 ^ n := pow_pos (by decide) n; omega : 1 ≤ 2 ^ n),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,hpow,sub_self]
  interval_cases n <;> norm_num at hdiv
  all_goals
    try simp only [show 15 = 3 * 5 from rfl, show 63 = 3 * 3 * 7 from rfl,
      show 255 = 3 * 5 * 17 from rfl, show 511 = 7 * 73 from rfl,
      show 1023 = 3 * 11 * 31 from rfl, show 2047 = 23 * 89 from rfl,
      show 4095 = 3 * 3 * 5 * 7 * 13 from rfl, hp.dvd_mul] at hdiv
  all_goals
    try simp only [Nat.dvd_prime (by decide : Nat.Prime 3),
      Nat.dvd_prime (by decide : Nat.Prime 5),
      Nat.dvd_prime (by decide : Nat.Prime 7),
      Nat.dvd_prime (by decide : Nat.Prime 11),
      Nat.dvd_prime (by decide : Nat.Prime 13),
      Nat.dvd_prime (by decide : Nat.Prime 17),
      Nat.dvd_prime (by decide : Nat.Prime 23),
      Nat.dvd_prime (by decide : Nat.Prime 31),
      Nat.dvd_prime (by decide : Nat.Prime 73),
      Nat.dvd_prime (by decide : Nat.Prime 89),
      Nat.dvd_prime (by decide : Nat.Prime 127)] at hdiv
  all_goals omega

/-- The bounded mover has prime eleven or thirteen, rank exactly three and
displacement at least five, for the actual module and its fixed quotient. -/
theorem small_mover_prime_and_rank
    {Q U : Type*} [Group Q] [Finite Q] [AddCommGroup U]
    [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (hf : Function.Injective ρ)
    (C C' : Subgroup Q) (hC : IsComponent Q C) [IsSimpleGroup C]
    (hactor : SmallMovingCubicActorPair ρ C C')
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL C 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13) :
    (p = 11 ∨ p = 13) ∧
    ∃ E : Subgroup Q, E ∈ ChapterD.QhatStar ρ ∧ rank E = 3 ∧
      rank (E ⊓ normalizer (C : Set Q)) = 2 ∧ fixedCodim ρ E ≤ 6 ∧
      fixedCodim (fixedQuotient ρ ⊤) E ≤ 6 ∧
      ∃ a ∈ E, orderOf a = 2 ∧ a ∉ normalizer (C : Set Q) ∧
        C.map (MulAut.conj a).toMonoidHom = C' ∧
        5 ≤ fixedCodim ρ (zpowers a) ∧
        (p = 13 → fixedCodim ρ (zpowers a) = 6 ∧ fixedCodim ρ E = 6) := by
  obtain ⟨hindex,E,hE,he,hr,hd,hdq,a,ha,ha2,han,hmap,hfaith⟩ := hactor
  let := hC.2
  have hz : center C = ⊥ :=
    (inferInstance : (center C).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp he))
  have hdiv := rank_one_characteristic_dvd hp ho hm
  have hprime := moving_component_prime_displacement ρ hf C hC hz a han hp (by omega) hdiv
  have hda : fixedCodim ρ (zpowers a) ≤ fixedCodim ρ E := by
    have hh := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr ha))
    have h₁ := fixedCodim_add_finrank ρ (zpowers a)
    have h₂ := fixedCodim_add_finrank ρ E
    omega
  have hp' : p = 11 ∨ p = 13 := prime_eq_eleven_or_thirteen_of_binary_order hp hmod (by omega)
  have hlo : 5 ≤ fixedCodim ρ (zpowers a) := by
    rcases hp' with rfl | rfl
    · rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hprime
      omega
    · rw [BinaryPrimeDegree.orderOf_two_mod_thirteen] at hprime
      omega
  have hnum := (actionRatio_le_nat_iff ρ hE.1.2.1 2).mp (hE.1.2.2.2.le.trans hE.1.1)
  refine ⟨hp',E,hE,by omega,by omega,hd,hdq,a,ha,ha2,han,hmap,hlo,?_⟩
  intro hp13
  subst p
  rw [BinaryPrimeDegree.orderOf_two_mod_thirteen] at hprime
  omega


end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
