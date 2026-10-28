module

public import Theory.GroupTheory.Hall.Existence
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupAction.OddFiveSixteen
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Tactic

/-!
# Normal five-subgroups in odd binary four-dimensional actors

A finite solvable group of order dividing 315 has normal Sylow five-subgroups.
Indeed, a Hall {3,5}-subgroup containing a given five-subgroup has order dividing
45, so Sylow counting makes the five-subgroup normal there. The Hall subgroup
has index dividing seven. Thus the number of Sylow five-subgroups in the whole
group divides seven and is congruent to one modulo five, forcing uniqueness.

The automorphism group of an elementary abelian group of order sixteen has
order 20160 = 64 * 315. This gives the required bound for every odd faithful
actor. We also provide the formulation for an injective linear representation
on a four-dimensional binary vector space and the cyclic-fifteen consequence.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma
14.2.21, printed p.989 (PDF p.1006), the odd-overgroup calculation in GL₄(2).
The Hall--Sylow argument expands the source's appeal to the structure of L₄(2).
-/

open Subgroup

/-- Every subgroup of order five in a finite solvable group whose order divides
315 is normal. A Hall {3,5}-subgroup normalizes it and has index dividing seven. -/
public theorem Subgroup.normal_of_card_five_of_solvable_card_dvd_315
    {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    (hG : Nat.card G ∣ 315) (K : Subgroup G) (hK : Nat.card K = 5) : K.Normal := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hi : K.index ∣ 63 := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 5)).mp
    have he : 5 * K.index = Nat.card G := by rw [← hK, K.card_mul_index]
    simpa only [he] using hG
  have hp : IsPGroup 5 K := IsPGroup.of_card (p := 5) (n := 1) (by simpa using hK)
  let P : Sylow 5 G := hp.toSylow (fun h => by have := h.trans hi; norm_num at this)
  let _ : MulDistribMulAction Unit G := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  let π : Set Nat.Primes := {p | p.val = 3 ∨ p.val = 5}
  have hKπ : IsPiSubgroup π K := by
    intro p hp
    rw [hK] at hp
    exact Or.inr ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hp |>.resolve_left p.property.ne_one)
  obtain ⟨H, hHall, _, hKH⟩ := exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (A := Unit) hsolv (by simp) π K hKπ ⟨fun _ _ => Iff.rfl⟩
  have hH : Nat.card H ∣ 45 := by
    have hn : ¬ 7 ∣ Nat.card H := by
      intro h
      have := hHall.p_in_pi_of_p_dvd_card ⟨7, by decide⟩ h
      change (7 : ℕ) = 3 ∨ 7 = 5 at this
      omega
    exact ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr hn).symm.dvd_of_dvd_mul_left
      (show Nat.card H ∣ 7 * 45 from H.card_subgroup_dvd_card.trans hG)
  have hHi : H.index ∣ 7 := by
    have hn3 : ¬ 3 ∣ H.index := fun h =>
      hHall.p_in_pi_of_p_dvd_index ⟨3, by decide⟩ h (Or.inl rfl)
    have hn5 : ¬ 5 ∣ H.index := fun h =>
      hHall.p_in_pi_of_p_dvd_index ⟨5, by decide⟩ h (Or.inr rfl)
    have hc3 : Nat.Coprime H.index 3 := ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr hn3).symm
    have hc5 : Nat.Coprime H.index 5 := ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr hn5).symm
    exact ((hc3.pow_right 2).mul_right hc5).dvd_of_dvd_mul_left
      (show H.index ∣ (3 ^ 2 * 5) * 7 from H.index_dvd_card.trans hG)
  let PH := P.subtype hKH
  have hPHcard : Nat.card PH = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv).trans hK
  have hPHi : PH.toSubgroup.index ∣ 9 := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 5)).mp
    have he : 5 * PH.toSubgroup.index = Nat.card H := by
      simpa only [hPHcard] using PH.toSubgroup.card_mul_index
    simpa only [he] using hH
  have hcH : Nat.card (Sylow 5 H) = 1 := by
    have hd := PH.card_dvd_index.trans hPHi
    have hm := card_sylow_modEq_one 5 H
    have hh := Nat.mem_divisors.mpr ⟨hd, (by decide : 9 ≠ 0)⟩
    rw [show Nat.divisors 9 = {1, 3, 9} by decide] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with h | h | h
    · exact h
    · norm_num [h, Nat.ModEq] at hm
    · norm_num [h, Nat.ModEq] at hm
  let _ : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp hcH).1
  have hHN : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp PH.normal_of_subsingleton
  have hc : Nat.card (Sylow 5 G) = 1 := by
    have hd : Nat.card (Sylow 5 G) ∣ 7 := by
      rw [P.card_eq_index_normalizer]
      exact (index_dvd_of_le hHN).trans hHi
    have hm := card_sylow_modEq_one 5 G
    rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with h | h
    · exact h
    · norm_num [h, Nat.ModEq] at hm
  let _ : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp hc).1
  exact P.normal_of_subsingleton


namespace Theory.GroupAction

/-- An odd solvable faithful actor on an elementary abelian group of order
sixteen normalizes every subgroup of order five. -/
public theorem normal_five_of_odd_binary_four
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] (hsolv : Group.IsSolvable A)
    (ρ : A →* MulAut V) (hρ : Function.Injective ρ)
    (hodd : Odd (Nat.card A)) (hV : Nat.card V = 16)
    (K : Subgroup A) (hK : Nat.card K = 5) : K.Normal := by
  have hdiv := Subgroup.card_dvd_of_injective ρ hρ
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow V 4
    (by simpa using hV)] at hdiv
  norm_num [Fin.prod_univ_succ] at hdiv
  have h315 : Nat.card A ∣ 315 :=
    (hodd.coprime_two_right.pow_right 6).dvd_of_dvd_mul_left hdiv
  exact Subgroup.normal_of_card_five_of_solvable_card_dvd_315 hsolv h315 K hK

/-- Linear representation formulation of `normal_five_of_odd_binary_four`.
The supplied representation is converted to automorphisms of the underlying
elementary abelian group, preserving its injectivity. -/
public theorem normal_five_of_odd_linear_four
    {A V : Type*} [Group A] [Finite A]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hsolv : Group.IsSolvable A)
    (ρ : A →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ)
    (hodd : Odd (Nat.card A)) (hV : Module.finrank (ZMod 2) V = 4)
    (K : Subgroup A) (hK : Nat.card K = 5) : K.Normal := by
  let _ : Finite V := Module.finite_of_finite (ZMod 2)
  let _ : IsElementaryAbelian 2 (Multiplicative V) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      change (2 : ℕ) • x.toAdd = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
      exact zero_smul (ZMod 2) x.toAdd) }
  let σ : A →* MulAut (Multiplicative V) := {
    toFun a := (ρ a).toAddEquiv.toMultiplicative
    map_one' := by ext x; exact congrArg Multiplicative.ofAdd (LinearEquiv.congr_fun ρ.map_one x.toAdd)
    map_mul' a b := by ext x; exact congrArg Multiplicative.ofAdd (LinearEquiv.congr_fun (ρ.map_mul a b) x.toAdd) }
  have hσ : Function.Injective σ := by
    intro a b h
    apply hρ
    ext x
    exact congrArg Multiplicative.toAdd (MulEquiv.congr_fun h (Multiplicative.ofAdd x))
  have hv : Nat.card (Multiplicative V) = 16 := by
    change Nat.card V = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hV, Nat.card_zmod]
    norm_num
  exact normal_five_of_odd_binary_four hsolv σ hσ hodd hv K hK


/-- A strict odd solvable enlargement of a five-subgroup, acting faithfully on
an elementary abelian group of order sixteen, is cyclic of order fifteen. -/
public theorem cyclic_fifteen_of_odd_binary_four_five_lt_top
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] (hsolv : Group.IsSolvable A)
    (ρ : A →* MulAut V) (hρ : Function.Injective ρ)
    (hodd : Odd (Nat.card A)) (hV : Nat.card V = 16)
    (K : Subgroup A) (hK : Nat.card K = 5) (hlt : K < ⊤) :
    Nat.card A = 15 ∧ IsCyclic A := by
  let _ : K.Normal := normal_five_of_odd_binary_four hsolv ρ hρ hodd hV K hK
  exact cyclic_fifteen_of_normal_five_lt_top ρ hρ K hK hodd hV hlt

end Theory.GroupAction
