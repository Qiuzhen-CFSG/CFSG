module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Holomorph
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The presentation of the marked holomorph

An element of order eight, and commuting involutions acting on it by
fifth power and inversion, determine an injective homomorphism from
C₈ ⋊ (Z/8)ˣ. The semidirect product gives the homomorphism; its kernel
is trivial because the unit action on C₈ is faithful.

This is the presentation used for the local calculation in
Aschbacher–Smith, *The Classification of Quasithin Groups*, pp.567–570.
-/

namespace AlternatingSix.ShadowLocal.Holomorph

private def cyclicHom {P : Type*} [Group P] {n : ℕ} [NeZero n]
    (a : P) (ha : a ^ n = 1) : Multiplicative (ZMod n) →* P where
  toFun v := a ^ v.toAdd.val
  map_one' := by simp
  map_mul' u v := by
    change a ^ (u.toAdd + v.toAdd).val = a ^ u.toAdd.val * a ^ v.toAdd.val
    rw [ZMod.val_add, ← pow_eq_pow_mod _ ha, pow_add]

private def unitCoordinates : (ZMod 8)ˣ →*
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) where
  toFun u := (Multiplicative.ofAdd (if (u : ZMod 8) = 5 ∨ (u : ZMod 8) = 3 then 1 else 0),
    Multiplicative.ofAdd (if (u : ZMod 8) = 7 ∨ (u : ZMod 8) = 3 then 1 else 0))
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private def unitsHom {P : Type*} [Group P]
    (c t : P) (hc : c ^ 2 = 1) (ht : t ^ 2 = 1) (hct : Commute c t) : (ZMod 8)ˣ →* P :=
  ((cyclicHom c hc).noncommCoprod (cyclicHom t ht)
    (fun u v => hct.pow_pow u.toAdd.val v.toAdd.val)).comp unitCoordinates

private theorem units_cases (u : (ZMod 8)ˣ) : u = 1 ∨ u = five ∨ u = (-1) ∨ u = five * (-1) := by
  revert u
  decide

private theorem unitsHom_values {P : Type*} [Group P]
    (c t : P) (hc : c ^ 2 = 1) (ht : t ^ 2 = 1) (hct : Commute c t) :
    unitsHom c t hc ht hct five = c ∧ unitsHom c t hc ht hct (-1) = t := by
  constructor
  · change c ^ 1 * t ^ 0 = c
    simp
  · change c ^ 0 * t ^ 1 = t
    simp

private theorem lift_compatible {P : Type*} [Group P]
    (a c t : P) (ha : a ^ 8 = 1) (hc : c ^ 2 = 1) (ht : t ^ 2 = 1)
    (hct : Commute c t) (hca : c * a * c⁻¹ = a ^ 5) (hta : t * a * t⁻¹ = a⁻¹) :
    ∀ u, (cyclicHom a ha).comp (unitAction u).toMonoidHom =
      (MulAut.conj (unitsHom c t hc ht hct u)).toMonoidHom.comp (cyclicHom a ha) := by
  let f := cyclicHom a ha
  let g := unitsHom c t hc ht hct
  have hvals := unitsHom_values c t hc ht hct
  have ha7 : a ^ 7 = a⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, ha])
  have hon (u : (ZMod 8)ˣ) :
      f (unitAction u (Multiplicative.ofAdd 1)) = g u * a * (g u)⁻¹ := by
    rcases units_cases u with rfl | rfl | rfl | rfl
    · simp only [map_one, MulAut.one_apply, one_mul, inv_one, mul_one]
      change a ^ 1 = a
      exact pow_one a
    · rw [show g five = c from hvals.1]
      change a ^ 5 = c * a * c⁻¹
      exact hca.symm
    · rw [show g (-1) = t from hvals.2]
      change a ^ 7 = t * a * t⁻¹
      exact ha7.trans hta.symm
    · rw [g.map_mul]
      rw [show g five = c from hvals.1, show g (-1) = t from hvals.2]
      change a ^ 3 = (c * t) * a * (c * t)⁻¹
      calc
        a ^ 3 = (a ^ 5)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_add]; exact ha)
        _ = c * a⁻¹ * c⁻¹ := by rw [← hca]; group
        _ = (c * t) * a * (c * t)⁻¹ := by rw [← hta]; group
  intro u
  apply MonoidHom.ext
  intro v
  have hv : (Multiplicative.ofAdd (1 : ZMod 8)) ^ v.toAdd.val = v := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow, nsmul_eq_mul]
  rw [← hv]
  simp only [MonoidHom.comp_apply, map_pow, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hf1 : cyclicHom a ha (Multiplicative.ofAdd 1) = a := by
    change a ^ 1 = a
    exact pow_one a
  rw [hf1]
  exact congrArg (fun q : P => q ^ v.toAdd.val) (hon u)

private theorem conjugation_rotation : ∀ m : Model,
    m * Holomorph.rotation * m⁻¹ = Holomorph.rotation ^ (m.right : ZMod 8).val := by decide +kernel

/-- The defining affine actions give an injective homomorphism, with the three generators fixed. -/
public theorem exists_injective_hom_of_relations
    {P : Type*} [Group P]
    (a c t : P) (ha : orderOf a = 8) (hc : c ^ 2 = 1) (ht : t ^ 2 = 1)
    (hct : Commute c t) (hca : c * a * c⁻¹ = a ^ 5) (hta : t * a * t⁻¹ = a⁻¹) :
    ∃ f : Model →* P, Function.Injective f ∧
      f Holomorph.rotation = a ∧ f transposition = c ∧ f reflection = t := by
  have ha8 : a ^ 8 = 1 := ha ▸ pow_orderOf_eq_one a
  let fn := cyclicHom a ha8
  let g := unitsHom c t hc ht hct
  let f : Model →* P := SemidirectProduct.lift fn g
    (lift_compatible a c t ha8 hc ht hct hca hta)
  have hftrans : f Holomorph.rotation = a := by
    change SemidirectProduct.lift fn g _ (SemidirectProduct.inl _) = a
    rw [SemidirectProduct.lift_inl]
    change a ^ 1 = a
    exact pow_one a
  have hker (m : Model) (hm : f m = 1) : m = 1 := by
    have hconj := congrArg f (conjugation_rotation m)
    simp only [map_mul, map_inv, map_pow, hm, hftrans, one_mul, inv_one,
      mul_one] at hconj
    have hval : (m.right : ZMod 8).val = 1 :=
      pow_injOn_Iio_orderOf (by simpa [ha] using (m.right : ZMod 8).val_lt)
        (by simp [ha]) (hconj.symm.trans (pow_one a).symm)
    have hu : m.right = 1 := Units.ext ((ZMod.val_eq_one (by decide +kernel) _).mp hval)
    have hfleft : f m = a ^ m.left.toAdd.val := by
      change fn m.left * g m.right = _
      rw [hu, map_one, mul_one]
      rfl
    have hzero : m.left.toAdd.val = 0 :=
      pow_injOn_Iio_orderOf (by simpa [ha] using m.left.toAdd.val_lt)
        (by simp [ha]) ((hfleft.symm.trans hm).trans (pow_zero a).symm)
    have hl : m.left = 1 := Multiplicative.toAdd.injective
      ((ZMod.val_eq_zero _).mp hzero)
    apply SemidirectProduct.ext <;> assumption
  have hi : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply bot_unique
    intro m hm
    exact hker m hm
  refine ⟨f, hi, hftrans, ?_, ?_⟩
  · change SemidirectProduct.lift fn g _ (SemidirectProduct.inr five) = c
    rw [SemidirectProduct.lift_inr]
    exact (unitsHom_values c t hc ht hct).1
  · change SemidirectProduct.lift fn g _ (SemidirectProduct.inr (-1)) = t
    rw [SemidirectProduct.lift_inr]
    exact (unitsHom_values c t hc ht hct).2


end AlternatingSix.ShadowLocal.Holomorph
