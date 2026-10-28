module

public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.PPrimeCore
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Frattini-kernel images of groups with a self-centralizing normal p-subgroup

Let S be a self-centralizing normal p-subgroup of a finite group H. If a
surjection has kernel contained in the ambient image of Φ(S), its target has
trivial p-prime core. Indeed, the target p-prime core centralizes the image
of S. Its inverse image therefore acts trivially on S/Φ(S). The Burnside
basis-kernel theorem and C_H(S) ≤ S make this inverse image a p-group; its
p-prime image is consequently trivial.

This source-neutral consequence of the Burnside basis theorem is used for
the normalizer quotient in GLS4, Chapter 2, Proposition 14.1.
-/

namespace Theory.GroupTheory
open Subgroup
open scoped commutatorElement

/-- A Frattini-kernel image of a group with a self-centralizing normal p-subgroup
has trivial p-prime core. -/
public theorem pPrimeCore_eq_bot_of_selfCentralizing_frattini_image
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    (p : ℕ) [Fact p.Prime] (S : Subgroup H) [S.Normal] (hS : IsPGroup p S)
    (hC : centralizer (S : Set H) ≤ S)
    (f : H →* K) (hf : Function.Surjective f)
    (hk : f.ker ≤ (frattini S).map S.subtype) : pPrimeCore p K = ⊥ := by
  let a : H →* MulAut S := MulAut.conjNormal
  have ha : IsPGroup p a.ker := by
    apply hS.to_le
    intro x hx
    apply hC
    apply mem_centralizer_iff.mpr
    intro y hy
    have he := congrArg (fun b : MulAut S => (b ⟨y, hy⟩ : H)) hx
    change x * y * x⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  let b := (quotientAut (frattini S)).comp a
  have hb : IsPGroup p b.ker :=
    (isPGroup_quotientAut_frattini_kernel hS).comap_of_ker_isPGroup a ha
  let O := pPrimeCore p K
  let R := S.map f
  let : R.Normal := Subgroup.Normal.map inferInstance f hf
  have hR : IsPGroup p R := hS.map f
  have hcop : Nat.Coprime (Nat.card O) (Nat.card R) := by
    obtain ⟨n, hn⟩ := hR.exists_card_dvd_pow
    exact (pPrimeCore_coprime_card.symm.pow_right n).of_dvd_right hn
  have hdis : Disjoint O R := disjoint_of_coprime_natCard hcop
  have hcomm : ⁅O, R⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_le_inf _ _).trans hdis.eq_bot.le)
  have hpre : O.comap f ≤ b.ker := by
    intro x hx
    apply MulEquiv.ext
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (frattini S) q
    change quotientAut (frattini S) (a x) (QuotientGroup.mk' (frattini S) y) =
      QuotientGroup.mk' (frattini S) y
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq.mpr
    have hc : f (y : H) * f x = f x * f (y : H) :=
      (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx _ (mem_map_of_mem f y.property)
    have hd : (y : H)⁻¹ * (x * (y : H) * x⁻¹) ∈ f.ker := by
      apply MonoidHom.mem_ker.mpr
      simp only [map_mul, map_inv]
      rw [← hc]
      group
    obtain ⟨v, hv, he⟩ := hk hd
    have he' : v = y⁻¹ * a x y := Subtype.ext he
    rw [he'] at hv
    simpa only [mul_inv_rev, inv_inv] using (frattini S).inv_mem hv
  have hpreP : IsPGroup p (O.comap f) := hb.to_le hpre
  have hO : IsPGroup p O := by
    have himage := hpreP.map f
    rw [map_comap_eq_self_of_surjective hf] at himage
    exact himage
  apply card_eq_one.mp
  obtain ⟨n, hn⟩ := hO.exists_card_dvd_pow
  exact Nat.eq_one_of_dvd_coprimes (pPrimeCore_coprime_card.pow_left n) hn dvd_rfl

end Theory.GroupTheory
