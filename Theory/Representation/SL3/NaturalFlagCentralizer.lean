module
public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.Algebra.CharP.Algebra
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Two-group centralizers of natural SL₃ flags

Suppose a faithful binary action contains a natural self-extension of full
SL₃(F), and a two-group centralizes that component and preserves the flag.
Its actions on the natural submodule and quotient are scalar. A scalar of
two-power order in characteristic two is one, so both actions are trivial.
The remaining displacement factors from the quotient to the submodule;
the natural commutant calculation makes it scalar too. These displacements
add under multiplication and detect every group element, giving an embedding
of the whole two-group in the additive coefficient field.

No invariant complement or semisimplicity is assumed, and both natural
sections use the same full SL₃ marking. The source application is the
saturated central-omega kernel in Aschbacher–Smith C.1.34, printed pp.136–137,
implemented in LinearThreeMS/NonbinarySource/KernelCoordinates.
-/

public noncomputable section
open Representation Subgroup
open scoped MatrixGroups
set_option backward.isDefEq.respectTransparency false
namespace Representation.SL3NaturalFlag
variable {F X V : Type*} [Field F] [Algebra (ZMod 2) F]
  [Group X] [AddCommGroup V] [Module (ZMod 2) V]

private theorem natural_two_power_eq_one
    {B : Type*} [Group B] (π : B →* SL(3,F)) (hπ : Function.Surjective π)
    (f : Module.End (ZMod 2) (Fin 3 → F))
    (hc : ∀ b v, f (specialLinearNatural 3 (π b) v) = specialLinearNatural 3 (π b) (f v))
    (m : ℕ) (hm : f^(2^m) = 1) : f = 1 := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  obtain ⟨c,hc⟩ := SL3OddNaturalNormalizer.centralizer_scalar f.toAddMonoidHom
    (by intro g v; obtain ⟨b,rfl⟩ := hπ g; exact hc b v)
  change ∀ v, f v = c • v at hc
  have hp (k : ℕ) (v : Fin 3 → F) : (f^k) v = c^k • v := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ',Module.End.mul_apply,ih,hc,smul_smul,pow_succ']
  have he : c^(2^m) = 1 := by
    have hh := congrFun (hp (2^m) (fun _ => 1)) 0
    simpa only [hm,Module.End.one_apply,Pi.smul_apply,smul_eq_mul,mul_one] using hh.symm
  have hi (k : ℕ) : Function.Injective (fun a : F => a^(2^k)) := by
    induction k with
    | zero => intro a b hab; simpa only [pow_zero,pow_one] using hab
    | succ k ih =>
      intro a b hab
      apply ih
      apply CharTwo.sq_injective
      simpa only [pow_succ,pow_mul] using hab
  have hc1 : c = 1 := hi m (he.trans (one_pow _).symm)
  exact LinearMap.ext (fun v => by change f v = v; simpa only [hc1,one_smul] using hc v)

/-- A two-group centralizing a natural self-extension and preserving its flag
embeds in the additive coefficient field. No complement of the flag is assumed. -/
theorem two_group_embedding
    (ρ : Representation (ZMod 2) X V) (hρ : Function.Injective ρ)
    (B P : Subgroup X) (hp : IsPGroup 2 P)
    (hc : P ≤ centralizer (B : Set X))
    (π : B →* SL(3,F)) (hπ : Function.Surjective π)
    (N : Subrepresentation (ρ.comp B.subtype))
    (en : N.toRepresentation.Equiv
      (((specialLinearNatural (k := F) 3).restrictScalars (k := ZMod 2)).comp π))
    (eq : N.quotientRepresentation.Equiv
      (((specialLinearNatural (k := F) 3).restrictScalars (k := ZMod 2)).comp π))
    (hs : ∀ (p : P) v, v ∈ N.toSubmodule → ρ p.val v ∈ N.toSubmodule) :
    ∃ a : P →* Multiplicative F, Function.Injective a := by
  let W := Fin 3 → F
  let σ := ((specialLinearNatural (k := F) 3).restrictScalars (k := ZMod 2)).comp π
  let T : Subrepresentation (ρ.comp P.subtype) := ⟨N.toSubmodule,hs⟩
  have commute_action (p : P) (b : B) (v : V) : ρ p.val (ρ b.val v) = ρ b.val (ρ p.val v) := by
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    rw [(hc p.property b b.property).symm]
  have hnfix (p : P) (v : N.toSubmodule) : ρ p.val v.val = v.val := by
    let f : Module.End (ZMod 2) W := en.toLinearEquiv.conjRingEquiv (T.toRepresentation p)
    have hf (b : B) (w : W) : f (σ b w) = σ b (f w) := by
      have hn (v : N.toSubmodule) : en (N.toRepresentation b v) = σ b (en v) :=
        LinearMap.congr_fun (en.isIntertwining' b) v
      change en (T.toRepresentation p (en.symm (σ b w))) = σ b (en (T.toRepresentation p (en.symm w)))
      rw [show en.symm (σ b w) = N.toRepresentation b (en.symm w) from
        LinearMap.congr_fun (en.symm.isIntertwining' b) w,←hn]
      apply congrArg en
      exact Subtype.ext (commute_action p b (en.symm w))
    obtain ⟨m,hm⟩ := isPGroup_iff_pow_pow_eq_one.mp hp p
    have hm' : f^(2^m) = 1 := by
      rw [←map_pow,←map_pow,hm,map_one,map_one]
    have he := natural_two_power_eq_one π hπ f hf m hm'
    have hh := LinearMap.congr_fun he (en v)
    change en (T.toRepresentation p (en.symm (en v))) = en v at hh
    rw [en.symm_apply_apply] at hh
    exact congrArg Subtype.val (en.injective hh)
  have hqfix (p : P) (v : V ⧸ N.toSubmodule) : T.quotientRepresentation p v = v := by
    let f : Module.End (ZMod 2) W := eq.toLinearEquiv.conjRingEquiv (T.quotientRepresentation p)
    have hqcomm (p : P) (b : B) (v : V ⧸ N.toSubmodule) :
        T.quotientRepresentation p (N.quotientRepresentation b v) =
          N.quotientRepresentation b (T.quotientRepresentation p v) := by
      obtain ⟨v,rfl⟩ := N.toSubmodule.mkQ_surjective v
      exact congrArg N.toSubmodule.mkQ (commute_action p b v)
    have hf (b : B) (w : W) : f (σ b w) = σ b (f w) := by
      have hn (v : V ⧸ N.toSubmodule) : eq (N.quotientRepresentation b v) = σ b (eq v) :=
        LinearMap.congr_fun (eq.isIntertwining' b) v
      change eq (T.quotientRepresentation p (eq.symm (σ b w))) = σ b (eq (T.quotientRepresentation p (eq.symm w)))
      rw [show eq.symm (σ b w) = N.quotientRepresentation b (eq.symm w) from
        LinearMap.congr_fun (eq.symm.isIntertwining' b) w,←hn,hqcomm]
    obtain ⟨m,hm⟩ := isPGroup_iff_pow_pow_eq_one.mp hp p
    have hm' : f^(2^m) = 1 := by
      rw [←map_pow,←map_pow,hm,map_one,map_one]
    have he := natural_two_power_eq_one π hπ f hf m hm'
    have hh := LinearMap.congr_fun he (eq v)
    change eq (T.quotientRepresentation p (eq.symm (eq v))) = eq v at hh
    rw [eq.symm_apply_apply] at hh
    exact eq.injective hh
  let i : W →ₗ[ZMod 2] V := N.toSubmodule.subtype.comp en.symm.toLinearEquiv.toLinearMap
  let q : V →ₗ[ZMod 2] W := eq.toLinearEquiv.toLinearMap.comp N.toSubmodule.mkQ
  have hi : Function.Injective i := Subtype.val_injective.comp en.symm.toLinearEquiv.injective
  have hq : Function.Surjective q := eq.toLinearEquiv.surjective.comp N.toSubmodule.mkQ_surjective
  have hi_equiv (b : B) (w : W) : ρ b.val (i w) = i (σ b w) := by
    exact (congrArg Subtype.val (LinearMap.congr_fun (en.symm.isIntertwining' b) w)).symm
  have hq_equiv (b : B) (v : V) : q (ρ b.val v) = σ b (q v) := by
    exact LinearMap.congr_fun (eq.isIntertwining' b) (N.toSubmodule.mkQ v)
  have hqker (v : V) : q v = 0 ↔ v ∈ N.toSubmodule := by
    change eq.toLinearEquiv (N.toSubmodule.mkQ v) = 0 ↔ _
    rw [eq.toLinearEquiv.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero _
  have hqP (p : P) (v : V) : q (ρ p.val v) = q v :=
    congrArg eq (hqfix p (N.toSubmodule.mkQ v))
  obtain ⟨j,hj⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqj (w : W) : q (j w) = w := LinearMap.congr_fun hj w
  have hdmem (p : P) (v : V) : ρ p.val v-v ∈ N.toSubmodule := by
    apply (hqker _).mp
    rw [map_sub,hqP,sub_self]
  let d (p : P) : Module.End (ZMod 2) W := en.toLinearEquiv.toLinearMap.comp
    (((ρ p.val - 1).comp j).codRestrict N.toSubmodule (fun w => hdmem p (j w)))
  have hid (p : P) (w : W) : i (d p w) = ρ p.val (j w) - j w := by
    change (en.symm (en ⟨_,hdmem p (j w)⟩)).val = _
    rw [en.symm_apply_apply]
  have hfull (p : P) (v : V) : ρ p.val v-v = i (d p (q v)) := by
    have hv : v-j (q v) ∈ N.toSubmodule := by
      apply (hqker _).mp
      rw [map_sub,hqj,sub_self]
    have hh := hnfix p ⟨v-j (q v),hv⟩
    change ρ p.val (v-j (q v)) = v-j (q v) at hh
    rw [map_sub] at hh
    rw [hid]
    exact (sub_eq_sub_iff_sub_eq_sub.mp hh)
  have hdcomm (p : P) (b : B) (w : W) : d p (σ b w) = σ b (d p w) := by
    apply hi
    rw [←hi_equiv,←hqj w,←hq_equiv,←hfull,hqj,hid,map_sub,commute_action]
  have hdmul (p r : P) : d (p*r) = d p + d r := by
    apply LinearMap.ext
    intro w
    apply hi
    change i (d (p*r) w) = i (d p w + d r w)
    rw [map_add,hid,hid,hid]
    have hh := hnfix p ⟨ρ r.val (j w)-j w,hdmem r (j w)⟩
    change ρ p.val (ρ r.val (j w)-j w) = ρ r.val (j w)-j w at hh
    rw [map_sub] at hh
    change ρ (p.val*r.val) (j w)-j w = _
    rw [map_mul,Module.End.mul_apply]
    calc
      ρ p.val (ρ r.val (j w))-j w =
          (ρ p.val (ρ r.val (j w))-ρ p.val (j w)) + (ρ p.val (j w)-j w) := by abel
      _ = _ := by rw [hh]; abel
  let c (p : P) : F := d p (fun _ => 1) 0
  have hscalar (p : P) (w : W) : d p w = c p • w := by
    obtain ⟨a,ha⟩ := SL3OddNaturalNormalizer.centralizer_scalar (d p).toAddMonoidHom
      (by intro g w; obtain ⟨b,rfl⟩ := hπ g; exact hdcomm p b w)
    change ∀ w, d p w = a • w at ha
    have he : c p = a := by
      change d p (fun _ => 1) 0 = a
      rw [ha]
      change a * 1 = a
      exact mul_one a
    rw [he]
    exact ha w
  let a : P →* Multiplicative F := {
    toFun := fun p => Multiplicative.ofAdd (c p)
    map_one' := by
      have hh := hdmul 1 1
      simp only [one_mul] at hh
      have he : d 1 = 0 := add_eq_left.mp hh.symm
      change c 1 = 0
      simp only [c,he,LinearMap.zero_apply]
      rfl
    map_mul' := by
      intro p r
      change c (p*r) = c p+c r
      simp only [c,hdmul,LinearMap.add_apply]
      rfl }
  refine ⟨a,?_⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro p hp
  apply Subtype.ext
  apply hρ
  change ρ p.val = ρ 1
  rw [map_one]
  apply LinearMap.ext
  intro v
  have hc0 : c p = 0 := hp
  have he := hfull p v
  rw [hscalar,hc0,zero_smul,map_zero] at he
  exact sub_eq_zero.mp he

end Representation.SL3NaturalFlag
