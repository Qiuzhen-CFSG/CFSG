module
public import Theory.GroupTheory.CyclicSubgroupNormalizer
public import Theory.GroupAction.OddInvolutionFrattini
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Cyclic obstructions for the odd residual in Proposition 16.5

Nontrivial p-subgroups in a finite cyclic group intersect nontrivially.
This excludes cyclicity when the original group contains nontrivial fixed
and inverted p-subgroups for one odd-order operator action. Separately, the
fixed and inverted subgroups of an involutory automorphism show that every
nontrivial such automorphism of an odd cyclic p-group is inversion.

These calculations transfer the two marked torus actions to the literal
R, Rᵤ and Rᵥ in GLS IV, Chapter 2, Proposition 16.5, lines 2945–2952.
-/

noncomputable section
namespace BenderSuzuki.ZD.NativeSource16
open Subgroup
open scoped IsMulCommutative

/-- Two nontrivial p-subgroups of a finite cyclic group cannot be disjoint. -/
public theorem cyclic_pSubgroups_not_disjoint {H : Type*} [Group H] [Finite H]
    [IsCyclic H] {p : ℕ} [Fact p.Prime]
    (P Q : Subgroup H) (hP : IsPGroup p P) (hQ : IsPGroup p Q)
    (hPn : P ≠ ⊥) (hQn : Q ≠ ⊥) : ¬ Disjoint P Q := by
  have hpP : p ∣ Nat.card P := hP.card_eq_or_dvd.resolve_left
    (fun he => hPn (P.eq_bot_iff_card.mpr he))
  have hpQ : p ∣ Nat.card Q := hQ.card_eq_or_dvd.resolve_left
    (fun he => hQn (Q.eq_bot_iff_card.mpr he))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) p hpP
  have hxQ : (x : H) ∈ Q := mem_of_pow_card_eq_one_in_cyclic Q (by
    exact congrArg (fun a : P => (a : H)) (orderOf_dvd_iff_pow_eq_one.mp (hx ▸ hpQ)))
  intro hd
  have hx1 : x = 1 := Subtype.ext (disjoint_def.mp hd x.property hxQ)
  exact (Fact.out : p.Prime).ne_one (by simpa only [hx1, orderOf_one] using hx.symm)

/-- A nontrivial involutory automorphism of an odd cyclic p-group is inversion. -/
public theorem cyclic_pGroup_involution_inverts
    {H : Type*} [Group H] [Finite H] [IsCyclic H]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p H) (hp : Odd p)
    (a : MulAut H) (ha : a ^ 2 = 1) (hne : a ≠ 1) : ∀ x : H, a x = x⁻¹ := by
  let : CommGroup H := IsCyclic.commGroup
  have hodd : Odd (Nat.card H) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk]
    exact hp.pow
  have ha2 (x : H) : a (a x) = x := by
    have hh := MulEquiv.congr_fun ha x
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  let I : Subgroup H := {
    carrier := {x | a x = x⁻¹}
    one_mem' := by simp
    mul_mem' := by
      intro x y hx hy
      change a (x * y) = (x * y)⁻¹
      rw [map_mul, hx, hy, mul_inv]
    inv_mem' := by
      intro x hx
      change a x⁻¹ = x⁻¹⁻¹
      rw [map_inv, hx] }
  have hI : I ≠ ⊥ := by
    intro he
    apply hne
    ext x
    have hx : a x * x⁻¹ ∈ I := by
      change a (a x * x⁻¹) = (a x * x⁻¹)⁻¹
      rw [map_mul, map_inv, ha2, mul_inv]
      simp only [inv_inv, mul_comm]
    rw [he, mem_bot] at hx
    simpa only [MulAut.one_apply] using mul_inv_eq_one.mp hx
  have hd : Disjoint a.fixedSubgroup I := by
    apply disjoint_def.mpr
    intro x hx hxI
    have hfix : a x = x := (MulAut.mem_fixedSubgroup a x).mp hx
    have hinv : a x = x⁻¹ := hxI
    have hx2 : x ^ 2 = 1 := by
      calc
        x ^ 2 = x * x := pow_two x
        _ = x * x⁻¹ := congrArg (fun y => x * y) (hfix.symm.trans hinv)
        _ = 1 := mul_inv_cancel x
    exact hodd.coprime_two_right.pow_left_bijective.injective (by
      simpa only [one_pow] using hx2)
  have hF : a.fixedSubgroup = ⊥ := by
    by_contra hFn
    exact cyclic_pSubgroups_not_disjoint a.fixedSubgroup I
      (hP.to_subgroup _) (hP.to_subgroup _) hFn hI hd
  have hfree : MonoidHom.FixedPointFree a.toMonoidHom := by
    intro x hx
    have hm : x ∈ a.fixedSubgroup := (MulAut.mem_fixedSubgroup a x).mpr hx
    rwa [hF, mem_bot] at hm
  exact fun x => congrFun (hfree.coe_eq_inv_of_involutive ha2) x

/-- Ambient version of the cyclic p-group involution calculation. -/
public theorem involution_inverts_cyclic_pSubgroup
    {H : Type*} [Group H] [Finite H] (Q : Subgroup H) [IsCyclic Q]
    {p : ℕ} [Fact p.Prime] (hQ : IsPGroup p Q) (hp : Odd p)
    (w : H) (hw : w ^ 2 = 1) (hn : w ∈ normalizer (Q : Set H))
    (hne : ¬ Q ≤ centralizer ({w} : Set H)) :
    ∀ x ∈ Q, w * x * w⁻¹ = x⁻¹ := by
  let a : MulAut Q := Q.normalizerMonoidHom ⟨w, hn⟩
  have ha : a ^ 2 = 1 := by
    ext x
    change w * (w * (x : H) * w⁻¹) * w⁻¹ = (x : H)
    calc
      w * (w * (x : H) * w⁻¹) * w⁻¹ = (w * w) * (x : H) * (w * w)⁻¹ := by group
      _ = (x : H) := by rw [← pow_two, hw]; simp
  have hane : a ≠ 1 := by
    intro he
    apply hne
    intro x hx
    have hh := MulEquiv.congr_fun he ⟨x, hx⟩
    have hxfix : w * x * w⁻¹ = x := congrArg Subtype.val hh
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hxfix).symm
  intro x hx
  exact congrArg Subtype.val (cyclic_pGroup_involution_inverts hQ hp a ha hane ⟨x, hx⟩)

/-- Distinct fixed and inverted nontrivial p-subgroups exclude cyclicity
of the original overgroup, without assuming either subgroup is a Sylow. -/
public theorem noncyclic_of_fixed_inverted_pSubgroups
    {H : Type*} [Group H] [Finite H] (R X Y : Subgroup H)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hXR : X ≤ R) (hYR : Y ≤ R) (hX : IsPGroup p X) (hY : IsPGroup p Y)
    (hXn : X ≠ ⊥) (hYn : Y ≠ ⊥)
    (u : H) (hXu : X ≤ centralizer ({u} : Set H))
    (hYu : ∀ y ∈ Y, u * y * u⁻¹ = y⁻¹) : ¬ IsCyclic R := by
  intro hcyc
  let : IsCyclic R := hcyc
  have hXp : IsPGroup p (X.subgroupOf R) := hX.of_equiv (subgroupOfEquivOfLe hXR).symm
  have hYp : IsPGroup p (Y.subgroupOf R) := hY.of_equiv (subgroupOfEquivOfLe hYR).symm
  have hXnr : X.subgroupOf R ≠ ⊥ := by
    intro he
    apply hXn
    have hh := congrArg (Subgroup.map R.subtype) he
    simpa only [map_subgroupOf_eq_of_le hXR, Subgroup.map_bot] using hh
  have hYnr : Y.subgroupOf R ≠ ⊥ := by
    intro he
    apply hYn
    have hh := congrArg (Subgroup.map R.subtype) he
    simpa only [map_subgroupOf_eq_of_le hYR, Subgroup.map_bot] using hh
  apply cyclic_pSubgroups_not_disjoint (X.subgroupOf R) (Y.subgroupOf R)
    hXp hYp hXnr hYnr
  apply disjoint_def.mpr
  intro x hx hy
  have hc : (x : H) * u = u * (x : H) := mem_centralizer_singleton_iff.mp (hXu hx)
  have he : (x : H) = (x : H)⁻¹ := by
    calc
      (x : H) = u * (x : H) * u⁻¹ := by rw [← hc]; simp
      _ = (x : H)⁻¹ := hYu x hy
  have hs : (x : H) ^ 2 = 1 := by
    calc
      (x : H) ^ 2 = (x : H) * x := pow_two _
      _ = (x : H) * (x : H)⁻¹ := congrArg (fun y => (x : H) * y) he
      _ = 1 := mul_inv_cancel _
  have hodd : Odd (Nat.card X) := by
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    rw [hk]
    exact hp.pow
  have hx1 : (⟨x, hx⟩ : X) = 1 := hodd.coprime_two_right.pow_left_bijective.injective (by
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, one_pow] using hs)
  exact Subtype.ext (congrArg (fun a : X => (a : H)) hx1)

end BenderSuzuki.ZD.NativeSource16
