module
public import Theory.SpecificGroups.AffineEight.Basic
public import Theory.GroupTheory.AbelianExponentFourRecognition

/-!
# Recognizing the affine group from a root-inverting involution

Suppose a finite group of order 32 contains commuting elements r and x,
where r has order four, x and t square to one, t inverts r, and
(xt)⁴ = r². Set a = xt and c = ra². Then a has order eight, c and t
are commuting involutions, and their actions on a are fifth power and
inversion. These are the actual affine actions on the cyclic group of
order eight.

The homomorphism from the affine model is constructed by the semidirect
product universal property. Its kernel is trivial: conjugation on the
translation generator detects the unit coordinate, after which the exact
order of a detects the translation coordinate. Equality of cardinalities
then gives an equivalence, without an assumed generation statement or an
external classification of groups of order 32.

This is the intrinsic presentation calculation for the outside-core
alternative of Janko–Thompson, Math. Z. 113 (1970), Lemma 4.1,
printed p.393.
-/

namespace AffineEight

private theorem standard_relations {P : Type*} [Group P]
    (r x t : P) (hr : r ^ 4 = 1) (hx : x ^ 2 = 1) (ht : t ^ 2 = 1)
    (hrx : Commute r x) (htr : t * r * t⁻¹ = r⁻¹)
    (hxt : (x * t) ^ 4 = r ^ 2) :
    let a := x * t
    let c := r * a ^ 2
    a ^ 8 = 1 ∧ c ^ 2 = 1 ∧ Commute c t ∧
      t * a * t⁻¹ = a⁻¹ ∧ c * a * c⁻¹ = a ^ 5 := by
  let a := x * t
  let c := r * a ^ 2
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hx)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht)
  have hxxt : x * x = 1 := by simpa [pow_two] using hx
  have htt : t * t = 1 := by simpa [pow_two] using ht
  have ht_a : t * a * t⁻¹ = a⁻¹ := by
    dsimp [a]
    simp only [mul_inv_rev, hxi, hti, mul_assoc, htt, mul_one]
  have ha8 : a ^ 8 = 1 := by
    rw [show 8 = 4 * 2 from rfl, pow_mul, hxt, ← pow_mul, hr]
  have hra : r * a * r⁻¹ = a ^ 5 := by
    have hh : t * r⁻¹ = r * t := by
      have hi := congrArg Inv.inv htr
      simp only [mul_inv_rev, inv_inv] at hi
      exact (mul_inv_eq_iff_eq_mul.mp (by simpa only [mul_assoc] using hi))
    calc
      r * a * r⁻¹ = x * r * (t * r⁻¹) := by dsimp [a]; rw [← mul_assoc, hrx.eq]; group
      _ = x * r ^ 2 * t := by rw [hh]; simp only [pow_two, mul_assoc]
      _ = r ^ 2 * a := by rw [← (hrx.pow_left 2).eq]; exact mul_assoc _ _ _
      _ = a ^ 5 := by rw [← hxt]; change a ^ 4 * a = a ^ 5; exact (pow_succ a 4).symm
  have hra2 : Commute r (a ^ 2) := by
    have hh : r * a ^ 2 * r⁻¹ = a ^ 2 := by
      rw [← conj_pow, hra, ← pow_mul]
      calc
        a ^ (5 * 2) = a ^ 8 * a ^ 2 := by rw [← pow_add]
        _ = a ^ 2 := by rw [ha8, one_mul]
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hc2 : c ^ 2 = 1 := by
    dsimp [c]
    rw [hra2.mul_pow, ← pow_mul, hxt, ← pow_two, ← pow_mul, hr]
  have htc : Commute c t := by
    have hh : t * c * t⁻¹ = c⁻¹ := by
      calc
        t * c * t⁻¹ = (t * r * t⁻¹) * (t * a ^ 2 * t⁻¹) := by dsimp [c]; group
        _ = r⁻¹ * (a⁻¹) ^ 2 := by rw [htr, ← conj_pow, ht_a]
        _ = c⁻¹ := by
          calc
            r⁻¹ * (a⁻¹) ^ 2 = r⁻¹ * (a ^ 2)⁻¹ := by rw [inv_pow]
            _ = (a ^ 2)⁻¹ * r⁻¹ := hra2.inv_inv.eq
            _ = (r * a ^ 2)⁻¹ := (mul_inv_rev _ _).symm
    have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hc2)
    rw [hci] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  refine ⟨ha8, hc2, htc, ht_a, ?_⟩
  change c * a * c⁻¹ = a ^ 5
  calc
    _ = r * a * r⁻¹ := by dsimp [c]; group
    _ = a ^ 5 := hra

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
  map_one' := by decide
  map_mul' := by decide

private def unitsHom {P : Type*} [Group P]
    (c t : P) (hc : c ^ 2 = 1) (ht : t ^ 2 = 1) (hct : Commute c t) : (ZMod 8)ˣ →* P :=
  ((cyclicHom c hc).noncommCoprod (cyclicHom t ht)
    (fun u v => hct.pow_pow u.toAdd.val v.toAdd.val)).comp unitCoordinates

private theorem units_cases (u : (ZMod 8)ˣ) : u = 1 ∨ u = five ∨ u = seven ∨ u = five * seven := by
  revert u
  decide

private theorem unitsHom_values {P : Type*} [Group P]
    (c t : P) (hc : c ^ 2 = 1) (ht : t ^ 2 = 1) (hct : Commute c t) :
    unitsHom c t hc ht hct five = c ∧ unitsHom c t hc ht hct seven = t := by
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
    · rw [show g seven = t from hvals.2]
      change a ^ 7 = t * a * t⁻¹
      exact ha7.trans hta.symm
    · rw [g.map_mul]
      rw [show g five = c from hvals.1, show g seven = t from hvals.2]
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

private def translation : Model := SemidirectProduct.inl (Multiplicative.ofAdd 1)

private theorem conjugation_translation : ∀ m : Model,
    m * translation * m⁻¹ = translation ^ (m.right : ZMod 8).val := by decide

/-- The standard cyclic-eight action relations recognize its full holomorph. -/
public theorem nonempty_mulEquiv_of_standard_relations
    {P : Type*} [Group P] [Finite P] (hcard : Nat.card P = 32)
    (a c t : P) (ha : orderOf a = 8) (hc : c ^ 2 = 1) (ht : t ^ 2 = 1)
    (hct : Commute c t) (hca : c * a * c⁻¹ = a ^ 5) (hta : t * a * t⁻¹ = a⁻¹) :
    Nonempty (P ≃* Model) := by
  have ha8 : a ^ 8 = 1 := ha ▸ pow_orderOf_eq_one a
  let fn := cyclicHom a ha8
  let g := unitsHom c t hc ht hct
  let f : Model →* P := SemidirectProduct.lift fn g
    (lift_compatible a c t ha8 hc ht hct hca hta)
  have hftrans : f translation = a := by
    change SemidirectProduct.lift fn g _ (SemidirectProduct.inl _) = a
    rw [SemidirectProduct.lift_inl]
    change a ^ 1 = a
    exact pow_one a
  have hker (m : Model) (hm : f m = 1) : m = 1 := by
    have hconj := congrArg f (conjugation_translation m)
    simp only [map_mul, map_inv, map_pow, hm, hftrans, one_mul, inv_one,
      mul_one] at hconj
    have hval : (m.right : ZMod 8).val = 1 :=
      pow_injOn_Iio_orderOf (by simpa [ha] using (m.right : ZMod 8).val_lt)
        (by simp [ha]) (hconj.symm.trans (pow_one a).symm)
    have hu : m.right = 1 := Units.ext ((ZMod.val_eq_one (by decide) _).mp hval)
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
  exact ⟨(MulEquiv.ofBijective f (hi.bijective_of_nat_card_le
    (by rw [hcard, card_model]))).symm⟩

/-- A commuting fourth root and swapped involutions identify the affine group. -/
public theorem nonempty_mulEquiv_of_root_inverting_involution
    {P : Type*} [Group P] [Finite P] (hcard : Nat.card P = 32)
    (r x t : P) (hr : orderOf r = 4) (hx : x ^ 2 = 1) (ht : t ^ 2 = 1)
    (hrx : Commute r x) (htr : t * r * t⁻¹ = r⁻¹)
    (hxt : (x * t) ^ 4 = r ^ 2) : Nonempty (P ≃* Model) := by
  obtain ⟨ha8, hc, hct, hta, hca⟩ := standard_relations r x t
    (hr ▸ pow_orderOf_eq_one r) hx ht hrx htr hxt
  have ha4 : (x * t) ^ 4 ≠ 1 := by
    rw [hxt]
    exact pow_ne_one_of_lt_orderOf (by decide) (by omega)
  have ha : orderOf (x * t) = 8 := by
    have hd : orderOf (x * t) ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one ha8
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    have hn : ¬ orderOf (x * t) ∣ 4 := fun h => ha4 (orderOf_dvd_iff_pow_eq_one.mp h)
    rw [he] at hn ⊢
    interval_cases k <;> norm_num at hn
    norm_num
  exact nonempty_mulEquiv_of_standard_relations hcard (x * t) (r * (x * t) ^ 2) t
    ha hc ht hct hca hta

end AffineEight
