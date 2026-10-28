module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.NineExtension.Automorphisms
public import Theory.PPrimeCore
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PGroup.OrderTwentySeven
public import Theory.ElementaryAbelian.Extraspecial
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Finite extensions with the full action on an elementary group of order nine

Let `R` be a normal elementary abelian subgroup of order nine in a finite
group `H`. Suppose conjugation onto `Aut(R)` is surjective and its kernel
modulo `R` is a two-group. Then the odd core of `H` is exactly `R`. For any
element `d` of order three outside `R`, the subgroup `R⟨d⟩` is a Sylow
three-subgroup, extraspecial of order twenty-seven and exponent three.

The explicit identification `Aut(R) ≃ GL₂(3)` supplies order 48 and the
triviality of its odd normal subgroups. Thus odd elements of the action kernel
lie in `R`, the odd core equals `R`, and the three-part of `|H|` is 27. The
split extension `R⟨d⟩` has order 27 and cannot be abelian. Cubing is a
homomorphism in a nonabelian group of this order; it kills both generating
factors, proving the exponent assertion. The center has order three and its
quotient is elementary abelian of order nine.

This is the conditional finite-group calculation used for `C_I(τf)` in
Aschbacher--Smith, *The Classification of Quasithin Groups*, 15.3.38,
printed p.1137 (manuscript of 1 March 2004, `refs/quasithin.pdf`). The
application must separately establish the two action hypotheses and the
specified element outside `R`; this module does not assert the source lemma.
-/

namespace Matrix.PSL3Four.ExtendedCentralizer.NineExtension
open Subgroup
open scoped Pointwise
local notation "E₉" => Multiplicative (Fin 2 → ZMod 3)
variable {H : Type*} [Group H] [Finite H] (R : Subgroup H) [R.Normal]
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

omit [Finite H] [R.Normal] in
private theorem residual_card (e : R ≃* E₉) : Nat.card R = 9 := by
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

omit [Finite H] [R.Normal] in
private theorem residual_cube (e : R ≃* E₉) (r : R) : r ^ 3 = 1 := by
  apply e.injective
  rw [map_pow, map_one]
  change (3 : ℕ) • Multiplicative.toAdd (e r) = 0
  exact ZModModule.char_nsmul_eq_zero 3 _

omit [Finite H] in
private theorem residual_le_kernel (e : R ≃* E₉) :
    R ≤ (MulAut.conjNormal : H →* MulAut R).ker := by
  intro r hr
  change MulAut.conjNormal r = (1 : MulAut R)
  ext s
  rw [MulAut.conjNormal_apply]
  have hc : (⟨r, hr⟩ : R) * s = s * ⟨r, hr⟩ := by
    apply e.injective
    simp only [map_mul, mul_comm]
  have hc' := congrArg Subtype.val hc
  change r * s.val = s.val * r at hc'
  rw [hc', mul_inv_cancel_right]
  rfl

omit [Finite H] in
private theorem odd_mem_residual
    (hkernel : IsPGroup 2 ((MulAut.conjNormal : H →* MulAut R).ker ⧸
      R.subgroupOf (MulAut.conjNormal : H →* MulAut R).ker))
    (x : H) (hx : x ∈ (MulAut.conjNormal : H →* MulAut R).ker)
    (hodd : Nat.Coprime 2 (orderOf x)) : x ∈ R := by
  let K := (MulAut.conjNormal : H →* MulAut R).ker
  let q := QuotientGroup.mk' (R.subgroupOf K)
  let k : K := ⟨x, hx⟩
  have hq : q k = 1 := by
    obtain ⟨n, hn⟩ := hkernel.exists_orderOf_eq_pow (q k)
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes (hodd.pow_left n)
      (hn ▸ dvd_refl _) (by simpa [k] using orderOf_map_dvd q k)
  exact (QuotientGroup.eq_one_iff (N := R.subgroupOf K) k).mp hq

/-- The normal elementary subgroup is the entire odd core. -/
public theorem oddCore_eq (e : R ≃* E₉)
    (hsurj : Function.Surjective (MulAut.conjNormal : H →* MulAut R))
    (hkernel : IsPGroup 2 ((MulAut.conjNormal : H →* MulAut R).ker ⧸
      R.subgroupOf (MulAut.conjNormal : H →* MulAut R).ker)) :
    pPrimeCore 2 H = R := by
  let θ : H →* MulAut R := MulAut.conjNormal
  have hmap : (pPrimeCore 2 H).map θ = ⊥ := by
    have : ((pPrimeCore 2 H).map θ).Normal :=
      (inferInstance : (pPrimeCore 2 H).Normal).map θ hsurj
    exact odd_normal_eq_bot e _
      ((pPrimeCore_coprime_card (p := 2) (G := H)).of_dvd_right (card_map_dvd _ θ))
  apply le_antisymm
  · intro x hx
    exact odd_mem_residual R hkernel x ((Subgroup.map_eq_bot_iff _).mp hmap hx)
      ((pPrimeCore_coprime_card (p := 2) (G := H)).of_dvd_right
        ((pPrimeCore 2 H).orderOf_dvd_natCard hx))
  · exact le_sSup ⟨inferInstance, by norm_num [residual_card R e]⟩

private theorem ambient_card (e : R ≃* E₉)
    (hsurj : Function.Surjective (MulAut.conjNormal : H →* MulAut R))
    (hkernel : IsPGroup 2 ((MulAut.conjNormal : H →* MulAut R).ker ⧸
      R.subgroupOf (MulAut.conjNormal : H →* MulAut R).ker)) :
    ∃ n : ℕ, Nat.card H = 27 * 2 ^ n := by
  let θ : H →* MulAut R := MulAut.conjNormal
  have hRK := residual_le_kernel R e
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hkernel
  have hR : Nat.card (R.subgroupOf θ.ker) = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe hRK).toEquiv).trans (residual_card R e)
  have hK : Nat.card θ.ker = 9 * 2 ^ n := by
    have hm := (R.subgroupOf θ.ker).card_mul_index
    rw [hR, Subgroup.index_eq_card, hn] at hm
    exact hm.symm
  have hθ : θ.ker.index = 48 := by
    rw [index_ker, MonoidHom.range_eq_top.mpr hsurj, card_top]
    exact automorphism_card e
  refine ⟨n + 4, ?_⟩
  rw [← θ.ker.card_mul_index, hK, hθ, pow_add]
  ring

omit [Finite H] in
private theorem join_card (e : R ≃* E₉) (d : H)
    (hd : orderOf d = 3) (hdR : d ∉ R) : Nat.card (R ⊔ zpowers d : Subgroup H) = 27 := by
  rw [card_sup_eq_mul_of_normalizes_of_disjoint R (zpowers d)
    (by rw [R.normalizer_eq_top]; exact le_top)
    (R.disjoint_zpowers_of_prime_order_not_mem d hd hdR),
    residual_card R e, Nat.card_zpowers, hd]

omit [Finite H] in
private theorem join_noncomm
    (hkernel : IsPGroup 2 ((MulAut.conjNormal : H →* MulAut R).ker ⧸
      R.subgroupOf (MulAut.conjNormal : H →* MulAut R).ker))
    (d : H) (hd : orderOf d = 3) (hdR : d ∉ R) :
    ¬ IsMulCommutative (R ⊔ zpowers d : Subgroup H) := by
  intro hc
  let P := R ⊔ zpowers d
  let : IsMulCommutative P := hc
  have hdP : d ∈ P := (le_sup_right : zpowers d ≤ R ⊔ zpowers d) (mem_zpowers d)
  have hdker : d ∈ (MulAut.conjNormal : H →* MulAut R).ker := by
    change MulAut.conjNormal d = (1 : MulAut R)
    ext r
    rw [MulAut.conjNormal_apply]
    have hrP : r.val ∈ P := (le_sup_left : R ≤ R ⊔ zpowers d) r.property
    have hcomm := congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨d, hdP⟩ : P) ⟨r.val, hrP⟩)
    change d * r.val = r.val * d at hcomm
    rw [hcomm, mul_inv_cancel_right]
    rfl
  exact hdR (odd_mem_residual R hkernel d hdker (by norm_num [hd]))

private theorem join_cube (e : R ≃* E₉)
    (hkernel : IsPGroup 2 ((MulAut.conjNormal : H →* MulAut R).ker ⧸
      R.subgroupOf (MulAut.conjNormal : H →* MulAut R).ker))
    (d : H) (hd : orderOf d = 3) (hdR : d ∉ R)
    (x : (R ⊔ zpowers d : Subgroup H)) : x ^ 3 = 1 := by
  let P := R ⊔ zpowers d
  have hcard := join_card R e d hd hdR
  have hncomm := join_noncomm R hkernel d hd hdR
  have hx : x.val ∈ (R : Set H) * (zpowers d : Set H) := by
    rw [← coe_mul_of_right_le_normalizer_left R (zpowers d)
      (by rw [R.normalizer_eq_top]; exact le_top)]
    exact x.property
  obtain ⟨a, ha, b, hb, hab⟩ := hx
  let aP : P := ⟨a, (le_sup_left : R ≤ R ⊔ zpowers d) ha⟩
  let bP : P := ⟨b, (le_sup_right : zpowers d ≤ R ⊔ zpowers d) hb⟩
  have heq : x = aP * bP := Subtype.ext hab.symm
  have ha3 : aP ^ 3 = 1 := by
    apply Subtype.ext
    exact congrArg (fun r : R => (r : H)) (residual_cube R e ⟨a, ha⟩)
  have hb3 : bP ^ 3 = 1 := by
    apply Subtype.ext
    exact orderOf_dvd_iff_pow_eq_one.mp (by
      simpa only [hd] using orderOf_dvd_of_mem_zpowers hb)
  rw [heq, OrderTwentySeven.cube_mul hcard hncomm, ha3, hb3, mul_one]

private theorem join_extraspecial (e : R ≃* E₉)
    (hkernel : IsPGroup 2 ((MulAut.conjNormal : H →* MulAut R).ker ⧸
      R.subgroupOf (MulAut.conjNormal : H →* MulAut R).ker))
    (d : H) (hd : orderOf d = 3) (hdR : d ∉ R) :
    IsExtraspecial 3 (R ⊔ zpowers d : Subgroup H) := by
  let P := R ⊔ zpowers d
  have hcard := join_card R e d hd hdR
  have hncomm := join_noncomm R hkernel d hd hdR
  have hQ := OrderTwentySeven.quotient_center_card hcard hncomm
  refine ⟨OrderTwentySeven.center_card hcard hncomm, ?_, ?_⟩
  · refine { toIsMulCommutative :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by simpa using hQ)
             exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center P) q
    rw [← map_pow, join_cube R e hkernel d hd hdR x, map_one]
  · exact Finite.one_lt_card_iff_nontrivial.mp (by omega)

/-- The specified split extension is extraspecial Sylow of order 27 and exponent three. -/
public theorem exists_sylow (e : R ≃* E₉)
    (hsurj : Function.Surjective (MulAut.conjNormal : H →* MulAut R))
    (hkernel : IsPGroup 2 ((MulAut.conjNormal : H →* MulAut R).ker ⧸
      R.subgroupOf (MulAut.conjNormal : H →* MulAut R).ker))
    (d : H) (hd : orderOf d = 3) (hdR : d ∉ R) :
    ∃ P : Sylow 3 H, (P : Subgroup H) = R ⊔ zpowers d ∧
      IsExtraspecial 3 P ∧ Nat.card P = 27 ∧ Monoid.exponent P = 3 := by
  let D := R ⊔ zpowers d
  have hcard : Nat.card D = 27 := join_card R e d hd hdR
  have hp : IsPGroup 3 D := IsPGroup.of_card (n := 3) (by simpa using hcard)
  have hindex : ¬ 3 ∣ D.index := by
    obtain ⟨n, hn⟩ := ambient_card R e hsurj hkernel
    have hm := D.card_mul_index
    rw [hcard, hn] at hm
    have hi : D.index = 2 ^ n := (Nat.mul_left_cancel (by norm_num : 0 < 27) hm)
    rw [hi]
    exact Nat.prime_three.coprime_iff_not_dvd.mp
      ((by decide : Nat.Coprime 3 2).pow_right n)
  let P : Sylow 3 H := hp.toSylow hindex
  have heq : (P : Subgroup H) = D := rfl
  have hexp : Monoid.exponent D = 3 := by
    apply Nat.dvd_antisymm
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (join_cube R e hkernel d hd hdR)
    · let dD : D := ⟨d, (le_sup_right : zpowers d ≤ R ⊔ zpowers d) (mem_zpowers d)⟩
      have hdD : orderOf dD = 3 := by rwa [← Subgroup.orderOf_coe]
      exact hdD ▸ Monoid.order_dvd_exponent dD
  refine ⟨P, heq, ?_, ?_, ?_⟩
  · change IsExtraspecial 3 D
    exact join_extraspecial R e hkernel d hd hdR
  · exact hcard
  · exact hexp

/-- The complete finite-extension conclusion, with only the action hypotheses
and the specified cubic element as input. -/
public theorem oddCore_eq_and_exists_sylow (e : R ≃* E₉)
    (hsurj : Function.Surjective (MulAut.conjNormal : H →* MulAut R))
    (hkernel : IsPGroup 2 ((MulAut.conjNormal : H →* MulAut R).ker ⧸
      R.subgroupOf (MulAut.conjNormal : H →* MulAut R).ker))
    (d : H) (hd : orderOf d = 3) (hdR : d ∉ R) :
    pPrimeCore 2 H = R ∧
      ∃ P : Sylow 3 H, (P : Subgroup H) = R ⊔ zpowers d ∧
        IsExtraspecial 3 P ∧ Nat.card P = 27 ∧ Monoid.exponent P = 3 :=
  ⟨oddCore_eq R e hsurj hkernel, exists_sylow R e hsurj hkernel d hd hdR⟩

end Matrix.PSL3Four.ExtendedCentralizer.NineExtension
