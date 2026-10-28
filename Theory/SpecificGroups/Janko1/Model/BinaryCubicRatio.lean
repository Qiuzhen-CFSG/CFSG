module
public import Theory.SpecificGroups.Janko1.Model.Certification
public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.Representation.BinaryOffender.CubicConjugateDimension
/-!
# Binary cubic ratios for the actual J₁ actor

Every involution is conjugate to the standard involution a, whose commutator
with b has order nineteen. Its binary displacement has dimension at least
eighteen, so each involution moves at least nine dimensions. Elementary
actors have rank at most three by the checked order of J₁. These bounds
exclude cubic ratio at most two for every faithful binary action.

This direct inner-actor form needs no irreducibility or outer-action
hypothesis. Source: Aschbacher–Smith K.4, printed p.457, used in C.5.13,
printed p.163. The checked intrinsic group and involution fusion supply
the model facts, as in the cover-preserving JankoOneExclusion source.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace Janko1
private theorem orderOf_two_nineteen : orderOf (2 : ZMod 19) = 18 := by
  apply (orderOf_eq_iff (by decide : 0 < 18)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

private theorem standard_commutator_order :
    orderOf (Janko1.a * Janko1.b * Janko1.a⁻¹ * Janko1.b⁻¹) = 19 := by
  have ha : Janko1.a⁻¹ = Janko1.a :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using Janko1.a_pow_two)
  have hb : Janko1.b⁻¹ = Janko1.b ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    exact (pow_succ' Janko1.b 2).symm.trans Janko1.b_pow_three
  simpa only [ha, hb] using Janko1.orderOf_abab_sq


/-- Every involution in a faithful binary J₁ action moves at least nine dimensions.
This applies directly to the original C.5.12 block image, without irreducibility. -/
theorem nine_le_fixedCodim_of_involution {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (e : G ≃* Janko1.Model) (t : G) (ht2 : orderOf t = 2) :
    9 ≤ fixedCodim ρ (zpowers t) := by
  obtain ⟨k,hk⟩ := Janko1.involution_fusion (e t) ((e.orderOf_eq t).trans ht2)
  let l := e.symm k
  let t' := l*t*l⁻¹
  let y := e.symm Janko1.b
  have ht' : e t' = Janko1.a := by
    simpa only [t',l,map_mul,map_inv,MulEquiv.apply_symm_apply] using hk
  have hc : orderOf (t'*y*t'⁻¹*y⁻¹)=19 := by
    rw [← e.orderOf_eq]
    simpa only [map_mul,map_inv,ht',y,MulEquiv.apply_symm_apply] using standard_commutator_order
  have hlo : 18 ≤ fixedCodim ρ (zpowers (t'*y*t'⁻¹*y⁻¹)) := by
    simpa only [orderOf_two_nineteen] using
      prime_order_le_fixedCodim ρ hf (by decide : Nat.Prime 19) (by decide) _ hc
  have hup := fixedCodim_commutator_le_twice ρ t' y
  have he : fixedCodim ρ (zpowers t')=fixedCodim ρ (zpowers t) := fixedCodim_zpowers_conj ρ t l
  rw [he] at hup
  omega

/-- Every faithful binary action of the actual J₁ group has cubic ratio above two. -/
theorem two_lt_cubicRatio_of_model {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (e : G ≃* Janko1.Model) : 2 < cubicRatio ρ := by
  by_contra hn
  obtain ⟨A,hA,_,hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp (le_of_not_gt hn)
  let := hA.2
  have hAr : rank A ≤ 3 := by
    have hd := A.card_subgroup_dvd_card
    rw [Nat.card_congr e.toEquiv,Janko1.card_model] at hd
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have hn3 : n ≤ 3 := by
      by_contra! hn3
      have h16 : 16 ∣ 175560 :=
        (show 16 ∣ 2 ^ n from pow_dvd_pow 2 (by omega : 4 ≤ n)).trans (hn ▸ hd)
      norm_num at h16
    simpa only [rank,hn,Nat.log_pow (by decide : 1 < 2)] using hn3
  obtain ⟨t,htA,ht⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ht2 : orderOf t=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t htA) ht
  have hmove := nine_le_fixedCodim_of_involution ρ hf e t ht2
  have hfix := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr htA))
  have h1 := fixedCodim_add_finrank ρ (zpowers t)
  have h2 := fixedCodim_add_finrank ρ A
  omega
end Janko1
