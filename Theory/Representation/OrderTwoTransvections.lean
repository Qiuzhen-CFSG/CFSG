module

public import Theory.Comparator.Defs
public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.Tactic

/-!
# Three-involution bound for characteristic-two transvections

This module isolates the finite-linear obstruction used in the order-two base
case of Stellmacher's Lemma (1.6).  Let a finite group act faithfully on a
finite vector space over `ZMod 2`.  If every involution acts as a transvection,
distinct involutions do not commute, and the product of any two distinct
involutions has odd order, then the group has at most three involutions.
More precisely, after choosing distinct involutions `t` and `u`, every
involution is `t`, `u`, or `u⁻¹ * t * u`.

The proof writes a transvection as `x ↦ x + f(x)v`.  Odd order rules out the
one-sided cross-pairing cases, while noncommutation rules out the zero-zero
case; hence both cross-pairings of two distinct involutions are one.  For four
putative distinct involutions these scalar identities force the conjugate of
the first transvection by the second to commute with the fourth.  Faithfulness
transports this contradiction back to the original group.

Source: the sentence “If `|S| = 2`, then ... (d) follows easily” in the proof
of Stellmacher (1.6), `refs/latex/stellmacher-n-group.tex`, journal p. 17.
-/

open scoped IsMulCommutative

namespace Representation

universe u v

private theorem transvection_mul_pow_four_of_cross_zero_one
    {X : Type v} [AddCommGroup X] [Module (ZMod 2) X]
    (f g : Module.Dual (ZMod 2) X) (v w : X)
    (hfv : f v = 0) (hgw : g w = 0)
    (hfw : f w = 0) (hgv : g v = 1) :
    (LinearEquiv.transvection hfv * LinearEquiv.transvection hgw) ^ 4 = 1 := by
  apply LinearEquiv.ext
  intro x
  simp [pow_succ, LinearMap.transvection.apply, hfv, hgw, hfw, hgv]
  match_scalars <;>
    simp [ZModModule.add_self, add_comm, add_left_comm]

private theorem transvection_mul_pow_four_of_cross_one_zero
    {X : Type v} [AddCommGroup X] [Module (ZMod 2) X]
    (f g : Module.Dual (ZMod 2) X) (v w : X)
    (hfv : f v = 0) (hgw : g w = 0)
    (hfw : f w = 1) (hgv : g v = 0) :
    (LinearEquiv.transvection hfv * LinearEquiv.transvection hgw) ^ 4 = 1 := by
  apply LinearEquiv.ext
  intro x
  simp [pow_succ, LinearMap.transvection.apply, hfv, hgw, hfw, hgv]
  match_scalars <;>
    simp [ZModModule.add_self, add_comm, add_left_comm]

private theorem eq_one_of_odd_order_of_pow_four
    {H : Type u} [Group H] (x : H)
    (hodd : Odd (orderOf x)) (hpow : x ^ 4 = 1) :
    x = 1 := by
  have hdvd : orderOf x ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hle : orderOf x ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < orderOf x := hodd.pos
  have hord : orderOf x = 1 := by
    interval_cases hx : orderOf x
    · rfl
    · obtain ⟨k, hk⟩ := hodd
      omega
    · norm_num [hx] at hdvd
    · obtain ⟨k, hk⟩ := hodd
      omega
  exact orderOf_eq_one_iff.mp hord

private theorem transvection_cross_eq_one_of_odd_order_of_not_commute
    {X : Type v} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (f g : Module.Dual (ZMod 2) X) (v w : X)
    (hfv : f v = 0) (hgw : g w = 0)
    (hodd : Odd (orderOf
      (LinearEquiv.transvection hfv * LinearEquiv.transvection hgw)))
    (hncomm : ¬ Commute
      (LinearEquiv.transvection hfv) (LinearEquiv.transvection hgw)) :
    f w = 1 ∧ g v = 1 := by
  have hfw : f w = 0 ∨ f w = 1 := by
    have hz (a : ZMod 2) : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact hz (f w)
  have hgv : g v = 0 ∨ g v = 1 := by
    have hz (a : ZMod 2) : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact hz (g v)
  rcases hfw with hfw | hfw <;> rcases hgv with hgv | hgv
  · exfalso
    apply hncomm
    apply LinearEquiv.ext
    intro x
    simp [LinearMap.transvection.apply, hfw, hgv]
    module
  · exfalso
    apply hncomm
    have hpow := transvection_mul_pow_four_of_cross_zero_one
      f g v w hfv hgw hfw hgv
    have heq := eq_one_of_odd_order_of_pow_four
      (LinearEquiv.transvection hfv * LinearEquiv.transvection hgw) hodd hpow
    rw [eq_inv_of_mul_eq_one_left heq]
    exact (Commute.refl (LinearEquiv.transvection hgw)).inv_left
  · exfalso
    apply hncomm
    have hpow := transvection_mul_pow_four_of_cross_one_zero
      f g v w hfv hgw hfw hgv
    have heq := eq_one_of_odd_order_of_pow_four
      (LinearEquiv.transvection hfv * LinearEquiv.transvection hgw) hodd hpow
    rw [eq_inv_of_mul_eq_one_left heq]
    exact (Commute.refl (LinearEquiv.transvection hgw)).inv_left
  · exact ⟨hfw, hgv⟩

private theorem conjugate_transvection_commutes_third
    {X : Type v} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (f g h : Module.Dual (ZMod 2) X) (v w z : X)
    (hfv : f v = 0) (hgw : g w = 0) (hhz : h z = 0)
    (hodd_fg : Odd (orderOf
      (LinearEquiv.transvection hfv * LinearEquiv.transvection hgw)))
    (hodd_fh : Odd (orderOf
      (LinearEquiv.transvection hfv * LinearEquiv.transvection hhz)))
    (hodd_gh : Odd (orderOf
      (LinearEquiv.transvection hgw * LinearEquiv.transvection hhz)))
    (hncomm_fg : ¬ Commute
      (LinearEquiv.transvection hfv) (LinearEquiv.transvection hgw))
    (hncomm_fh : ¬ Commute
      (LinearEquiv.transvection hfv) (LinearEquiv.transvection hhz))
    (hncomm_gh : ¬ Commute
      (LinearEquiv.transvection hgw) (LinearEquiv.transvection hhz)) :
    Commute
      ((LinearEquiv.transvection hgw)⁻¹ *
        LinearEquiv.transvection hfv * LinearEquiv.transvection hgw)
      (LinearEquiv.transvection hhz) := by
  obtain ⟨hfw, hgv⟩ :=
    transvection_cross_eq_one_of_odd_order_of_not_commute
      f g v w hfv hgw hodd_fg hncomm_fg
  obtain ⟨hfz, hhv⟩ :=
    transvection_cross_eq_one_of_odd_order_of_not_commute
      f h v z hfv hhz hodd_fh hncomm_fh
  obtain ⟨hgz, hhw⟩ :=
    transvection_cross_eq_one_of_odd_order_of_not_commute
      g h w z hgw hhz hodd_gh hncomm_gh
  have hginv : (LinearEquiv.transvection hgw)⁻¹ =
      LinearEquiv.transvection hgw := by
    apply inv_eq_of_mul_eq_one_left
    apply LinearEquiv.ext
    intro x
    simp [LinearMap.transvection.apply, hgw]
    match_scalars <;> simp [ZModModule.add_self]
  rw [hginv]
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hthree : (3 : ZMod 2) = 1 := by decide
  have hfour : (4 : ZMod 2) = 0 := by decide
  apply LinearEquiv.ext
  intro x
  simp [LinearMap.transvection.apply, hgw,
    hfw, hgv, hfz, hhv, hgz, hhw]
  match_scalars <;> abel_nf <;>
    simp [htwo, hthree, hfour, ZModModule.add_self,
      ZModModule.add_add_add_cancel]

/-- A faithful characteristic-two representation in which all involutions are
transvections has at most three involutions when distinct involutions do not
commute and have odd-order products. -/
public theorem three_involutions_of_faithful_transvection_representation
    {G : Type u} {X : Type v} [Group G] [Finite G]
    [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (ρ : Representation (ZMod 2) G X)
    (hρ : Function.Injective ρ.asGroupHom)
    (htrans : ∀ {x : G}, IsInvolution x →
      LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom x) ∈
        LinearEquiv.transvections (ZMod 2) X)
    (hpair : ∀ {x y : G}, IsInvolution x → IsInvolution y → x ≠ y →
      ¬ Commute x y ∧ Odd (orderOf (x * y)))
    {t u : G} (ht : IsInvolution t) (hu : IsInvolution u) (htu : t ≠ u) :
    ∀ {x : G}, IsInvolution x →
      x = t ∨ x = u ∨ x = u⁻¹ * t * u := by
  let e : G →* (X ≃ₗ[ZMod 2] X) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) X).toMonoidHom.comp
      ρ.asGroupHom
  have he_inj : Function.Injective e :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) X).injective.comp hρ
  have pair_image {a b : G} (ha : IsInvolution a) (hb : IsInvolution b)
      (hab : a ≠ b) :
      ¬ Commute (e a) (e b) ∧ Odd (orderOf (e a * e b)) := by
    obtain ⟨hncomm, hodd⟩ := hpair ha hb hab
    constructor
    · intro hcomm
      apply hncomm
      apply he_inj
      simpa [map_mul] using hcomm.eq
    · rw [← map_mul, orderOf_injective e he_inj]
      exact hodd
  let s : G := u⁻¹ * t * u
  have hs : IsInvolution s := by
    constructor
    · intro hsone
      apply ht.1
      have := congrArg (fun z : G => u * z * u⁻¹) hsone
      simpa [s, mul_assoc] using this
    · dsimp [s]
      rw [pow_two]
      calc
        (u⁻¹ * t * u) * (u⁻¹ * t * u) = u⁻¹ * (t * t) * u := by group
        _ = 1 := by rw [← pow_two, ht.2]; simp
  have hst : s ≠ t := by
    intro hst
    apply (hpair ht hu htu).1
    show t * u = u * t
    have := congrArg (fun z : G => u * z) hst
    simpa [s, mul_assoc] using this
  have hsu : s ≠ u := by
    intro hsu
    apply htu
    have := congrArg (fun z : G => u * z * u⁻¹) hsu
    simpa [s, mul_assoc] using this
  intro x hx
  by_cases hxt : x = t
  · exact Or.inl hxt
  by_cases hxu : x = u
  · exact Or.inr (Or.inl hxu)
  by_cases hxs : x = s
  · exact Or.inr (Or.inr hxs)
  exfalso
  have htx := pair_image ht hx (Ne.symm hxt)
  have hux := pair_image hu hx (Ne.symm hxu)
  have htu_image := pair_image ht hu htu
  have httrans := htrans ht
  have hutrans := htrans hu
  have hxtrans := htrans hx
  rw [LinearEquiv.mem_transvections_iff] at httrans hutrans hxtrans
  obtain ⟨ft, vt, htvt, het⟩ := httrans
  obtain ⟨fu, vu, huvu, heu⟩ := hutrans
  obtain ⟨fx, vx, hxvx, hex⟩ := hxtrans
  have het' : e t = LinearEquiv.transvection htvt := het
  have heu' : e u = LinearEquiv.transvection huvu := heu
  have hex' : e x = LinearEquiv.transvection hxvx := hex
  have hcomm_image := conjugate_transvection_commutes_third
    ft fu fx vt vu vx htvt huvu hxvx
    (by simpa only [het', heu'] using htu_image.2)
    (by simpa only [het', hex'] using htx.2)
    (by simpa only [heu', hex'] using hux.2)
    (by simpa only [het', heu'] using htu_image.1)
    (by simpa only [het', hex'] using htx.1)
    (by simpa only [heu', hex'] using hux.1)
  have hcomm_e : Commute ((e u)⁻¹ * e t * e u) (e x) := by
    simpa only [het', heu', hex'] using hcomm_image
  apply (hpair hs hx (Ne.symm hxs)).1
  apply he_inj
  simpa only [s, map_mul, map_inv, mul_assoc] using hcomm_e.eq

end Representation

