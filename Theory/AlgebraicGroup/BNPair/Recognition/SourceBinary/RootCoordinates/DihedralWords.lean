module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.MarkedQuotient
public import Theory.GroupTheory.DihedralPresentation

/-!
# Marked finite dihedral coordinates

The two distinct nonidentity involutions of a marked finite quotient give
an explicit isomorphism of its Weyl group with `DihedralGroup m`, where
`m = orderOf (s₀ * s₁) ≥ 2`. The isomorphism sends the original generators
to `sr 0` and `sr 1`; its inverse gives the unique rotation/reflection
normal forms. Neither irreducibility nor a prescribed value of m is used,
and the original carrier need not be finite.

The presentation map follows the private calculation in
`Theory.GroupTheory.DihedralPresentation`. Its injectivity is proved here:
a reflection cannot be a rotation, since then the rotation has square one
and one of the original nonidentity reflections would be the identity.
Generation gives surjectivity. This supplies the marked Weyl coordinates
for Carter, §2.5 (the supplied `GLS3/Chapter2Ca2.tex`), without assuming a
root system or a Lie-model realization.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
private def rotation {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (c : G) (hc : c ^ m = 1) : Multiplicative (ZMod m) →* G where
  toFun i := c ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change c ^ (i.toAdd + j.toAdd).val = c ^ i.toAdd.val * c ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod (i.toAdd.val + j.toAdd.val) hc).symm

private theorem rotation_one {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (c : G) (hc : c ^ m = 1) : rotation c hc (.ofAdd 1) = c := by
  change c ^ (1 : ZMod m).val = c
  rw [← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod 1 hc, pow_one]

private def presentationHom {G : Type*} [Group G] {m : ℕ} [NeZero m]
    (c d : G) (hc : c ^ m = 1) (hd : d ^ 2 = 1)
    (hconj : d * c * d⁻¹ = c⁻¹) : DihedralGroup m →* G := by
  let f := rotation c hc
  have hswap (i : Multiplicative (ZMod m)) : f i * d = d * (f i)⁻¹ := by
    have hh : d * f i * d⁻¹ = (f i)⁻¹ := by
      change d * c ^ i.toAdd.val * d⁻¹ = (c ^ i.toAdd.val)⁻¹
      rw [← conj_pow, hconj, inv_pow]
    have dd : d * d = 1 := by simpa [pow_two] using hd
    calc
      f i * d = (d * d) * f i * d := by rw [dd, one_mul]
      _ = d * (d * f i * d⁻¹) := by
        have hi : d⁻¹ = d := inv_eq_of_mul_eq_one_right dd
        rw [hi]
        simp only [mul_assoc]
      _ = d * (f i)⁻¹ := by rw [hh]
  refine {
    toFun := fun x => match x with
      | .r i => f (.ofAdd i)
      | .sr i => d * f (.ofAdd i)
    map_one' := by change f 1 = 1; exact f.map_one
    map_mul' := ?_ }
  intro x y
  cases x with
  | r i =>
    cases y with
    | r j => exact f.map_mul (.ofAdd i) (.ofAdd j)
    | sr j =>
      change d * f (.ofAdd (j - i)) = f (.ofAdd i) * (d * f (.ofAdd j))
      rw [← mul_assoc, hswap, mul_assoc]
      rw [sub_eq_add_neg]
      change d * f ((.ofAdd j) * (.ofAdd i)⁻¹) = d * ((f (.ofAdd i))⁻¹ * f (.ofAdd j))
      rw [map_mul, map_inv]
      congr 1
      simpa only [map_inv] using (Commute.map (Commute.all (.ofAdd j) ((.ofAdd i)⁻¹)) f).eq
  | sr i =>
    cases y with
    | r j =>
      change d * f ((.ofAdd i) * (.ofAdd j)) = d * f (.ofAdd i) * f (.ofAdd j)
      rw [map_mul, mul_assoc]
    | sr j =>
      change f (.ofAdd (j - i)) = (d * f (.ofAdd i)) * (d * f (.ofAdd j))
      rw [mul_assoc d, ← mul_assoc (f (.ofAdd i)), hswap, ← mul_assoc d, ← mul_assoc d d]
      have dd : d * d = 1 := by simpa [pow_two] using hd
      rw [dd, one_mul]
      rw [sub_eq_add_neg]
      change f ((.ofAdd j) * (.ofAdd i)⁻¹) = (f (.ofAdd i))⁻¹ * f (.ofAdd j)
      rw [map_mul, map_inv]
      simpa only [map_inv] using (Commute.map (Commute.all (.ofAdd j) ((.ofAdd i)⁻¹)) f).eq


private theorem reflection_ne_rotation_power {G : Type*} [Group G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (k : ℕ) : a ≠ (a * b) ^ k := by
  intro h
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hc : Commute a (a * b) := by
    nth_rw 1 [h]
    exact (Commute.refl (a * b)).pow_left k
  have hconj : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    simp only [mul_inv_rev, hai, hbi, ← mul_assoc, ha, one_mul]
  have hr : (a * b) ^ 2 = 1 := by
    have he : a * b = (a * b)⁻¹ := by
      rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one] at hconj
      exact hconj
    calc
      (a * b) ^ 2 = (a * b) * (a * b) := pow_two _
      _ = (a * b) * (a * b)⁻¹ := congrArg ((a * b) * ·) he
      _ = 1 := mul_inv_cancel _
  have hm := pow_eq_pow_mod k hr
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with hk | hk
  · exact ha1 (by simpa [hk] using h.trans hm)
  · have hab : a = a * b := by simpa [hk] using h.trans hm
    exact hb1 ((mul_left_cancel (show a * b = a * 1 by simpa using hab.symm)))

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (d : MarkedQuotient P)

/-- The literal Weyl quotient of the supplied marked quotient. -/
abbrev Weyl := d.tits.N ⧸ (d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N

/-- The order of the product in the original endpoint order. -/
@[expose] def rotationOrder : ℕ := orderOf (d.simple 0 * d.simple 1)

/-- Distinct nonidentity simple reflections give at least a four-element Weyl group. -/
theorem rotationOrder_ge_two : 2 ≤ rotationOrder d := by
  have hp := orderOf_pos (d.simple 0 * d.simple 1)
  have hn : d.simple 0 * d.simple 1 ≠ 1 := by
    intro h
    have hi := inv_eq_of_mul_eq_one_right (by
      simpa only [pow_two] using (d.tits.involutions _ (d.simple_mem 0)).2)
    have he : d.simple 1 = d.simple 0 := by
      simpa only [hi] using eq_inv_of_mul_eq_one_right h
    exact (by decide : (1 : Fin 2) ≠ 0) (d.simple_injective he)
  have hh := (orderOf_eq_one_iff).not.mpr hn
  change 2 ≤ orderOf (d.simple 0 * d.simple 1)
  omega

instance rotationOrder_neZero : NeZero (rotationOrder d) :=
  ⟨by have := rotationOrder_ge_two d; omega⟩

private def normalFormMap : DihedralGroup (rotationOrder d) →* Weyl d :=
  presentationHom (d.simple 0 * d.simple 1) (d.simple 0)
    (pow_orderOf_eq_one _) (d.tits.involutions _ (d.simple_mem 0)).2 (by
      have h0 := (d.tits.involutions _ (d.simple_mem 0)).2
      have h1 := (d.tits.involutions _ (d.simple_mem 1)).2
      have hi0 : (d.simple 0)⁻¹ = d.simple 0 :=
        inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h0)
      have hi1 : (d.simple 1)⁻¹ = d.simple 1 :=
        inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h1)
      simp only [mul_inv_rev, hi0, hi1, ← mul_assoc,
        show d.simple 0 * d.simple 0 = 1 by simpa only [pow_two] using h0, one_mul])

private theorem normalFormMap_r (i : ZMod (rotationOrder d)) :
    normalFormMap d (.r i) = (d.simple 0 * d.simple 1) ^ i.val := rfl

private theorem normalFormMap_sr (i : ZMod (rotationOrder d)) :
    normalFormMap d (.sr i) = d.simple 0 * (d.simple 0 * d.simple 1) ^ i.val := rfl

private theorem normalFormMap_sr_zero : normalFormMap d (.sr 0) = d.simple 0 := by
  simp [normalFormMap_sr]

private theorem normalFormMap_sr_one : normalFormMap d (.sr 1) = d.simple 1 := by
  have hr : normalFormMap d (.r 1) = d.simple 0 * d.simple 1 :=
    rotation_one (m := rotationOrder d) _ (pow_orderOf_eq_one _)
  have he : (DihedralGroup.sr 1 : DihedralGroup (rotationOrder d)) = .sr 0 * .r 1 := by simp
  rw [he, map_mul, normalFormMap_sr_zero, hr, ← mul_assoc]
  have h0 := (d.tits.involutions _ (d.simple_mem 0)).2
  rw [show d.simple 0 * d.simple 0 = 1 by simpa only [pow_two] using h0, one_mul]

private theorem normalFormMap_injective : Function.Injective (normalFormMap d) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  change normalFormMap d x = 1 at hx
  change x = 1
  cases x with
  | r i =>
    rw [normalFormMap_r] at hx
    have hi : i.val = 0 := by
      have hh := (pow_inj_mod.mp (hx.trans (pow_zero _).symm))
      change i.val % rotationOrder d = 0 % rotationOrder d at hh
      simpa only [Nat.mod_eq_of_lt i.val_lt, Nat.zero_mod] using hh
    have he : i = 0 := ZMod.val_injective _ (by simpa only [ZMod.val_zero] using hi)
    simp [he]
  | sr i =>
    rw [normalFormMap_sr] at hx
    have ha := (d.tits.involutions _ (d.simple_mem 0))
    have hb := (d.tits.involutions _ (d.simple_mem 1))
    have ha2 : d.simple 0 * d.simple 0 = 1 := by simpa only [pow_two] using ha.2
    have hb2 : d.simple 1 * d.simple 1 = 1 := by simpa only [pow_two] using hb.2
    have he : d.simple 0 = (d.simple 0 * d.simple 1) ^ i.val := by
      have := eq_inv_of_mul_eq_one_right hx
      simpa only [inv_eq_of_mul_eq_one_right ha2] using this.symm
    exact False.elim (reflection_ne_rotation_power _ _ ha2 hb2 ha.1 hb.1 i.val he)

private theorem normalFormMap_surjective : Function.Surjective (normalFormMap d) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← d.tits.quotient_generate, closure_le]
  intro x hx
  obtain ⟨i, rfl⟩ := d.simple_range.symm ▸ hx
  fin_cases i
  · exact ⟨.sr 0, normalFormMap_sr_zero d⟩
  · exact ⟨.sr 1, normalFormMap_sr_one d⟩

/-- Explicit marked coordinates, with the original endpoints in their given order. -/
def weylEquiv : Weyl d ≃* DihedralGroup (rotationOrder d) :=
  (MulEquiv.ofBijective (normalFormMap d)
    ⟨normalFormMap_injective d, normalFormMap_surjective d⟩).symm

/-- The first original reflection is the zero reflection. -/
@[simp] theorem weylEquiv_simple_zero : weylEquiv d (d.simple 0) = .sr 0 := by
  apply (weylEquiv d).symm.injective
  rw [MulEquiv.symm_apply_apply]
  change d.simple 0 = normalFormMap d (.sr 0)
  exact (normalFormMap_sr_zero d).symm

/-- The second original reflection is the unit reflection. -/
@[simp] theorem weylEquiv_simple_one : weylEquiv d (d.simple 1) = .sr 1 := by
  apply (weylEquiv d).symm.injective
  rw [MulEquiv.symm_apply_apply]
  change d.simple 1 = normalFormMap d (.sr 1)
  exact (normalFormMap_sr_one d).symm

/-- The Weyl order follows from the constructed normal forms. -/
theorem weyl_card : Nat.card (Weyl d) = 2 * rotationOrder d := by
  rw [Nat.card_congr (weylEquiv d).toEquiv, DihedralGroup.nat_card]

/-- The rotation coordinates are powers of the original ordered product. -/
@[simp] theorem weylEquiv_symm_r (i : ZMod (rotationOrder d)) :
    (weylEquiv d).symm (.r i) = (d.simple 0 * d.simple 1) ^ i.val := by
  change normalFormMap d (.r i) = _
  exact normalFormMap_r d i

/-- The reflection coordinates retain the first original simple reflection. -/
@[simp] theorem weylEquiv_symm_sr (i : ZMod (rotationOrder d)) :
    (weylEquiv d).symm (.sr i) = d.simple 0 * (d.simple 0 * d.simple 1) ^ i.val := by
  change normalFormMap d (.sr i) = _
  exact normalFormMap_sr d i

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
