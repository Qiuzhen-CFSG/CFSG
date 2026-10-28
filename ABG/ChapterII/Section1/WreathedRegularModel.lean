module
public import ABG.ChapterII.Section1.WreathedNormalForm
public import ABG.ChapterII.Section1.WreathedRelations
public import Mathlib.GroupTheory.RegularWreathProduct

/-!
# Concrete regular wreath products from ABG presentations

A wreathed presentation of height `n` identifies its carrier with
`C_(2^n) ≀ C₂`. Evaluate the two base coordinates as powers of the commuting
presentation generators, and the top coordinate as a power of the swapping
involution. The conjugation relations prove multiplicativity. The existing
normal-form theorem gives surjectivity, and the prescribed group order makes
the map bijective.

This supplies a concrete model without assuming any recognition result for
an arbitrary Sylow subgroup. Source: Alperin–Brauer–Gorenstein, Chapter II §1,
article p.9, the wreathed presentation preceding Lemma 2.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private abbrev C2 := Multiplicative (ZMod 2)
private abbrev Model (n : ℕ) := RegularWreathProduct (Multiplicative (ZMod (2 ^ n))) C2
private abbrev flip : C2 := Multiplicative.ofAdd 1

private def eval (w : Model n) : S :=
  P.s ^ (w.left 1).toAdd.val * P.t ^ (w.left flip).toAdd.val * P.z ^ w.right.toAdd.val

private theorem c2_cases (x : C2) : x = 1 ∨ x = flip := by
  have h : ∀ x : C2, x = 1 ∨ x = flip := by decide
  exact h x

private theorem swap_base (i j : ℕ) :
    P.z * (P.s ^ i * P.t ^ j) = (P.s ^ j * P.t ^ i) * P.z := by
  rw [← mul_assoc, P.z_mul_s_pow, mul_assoc, P.z_mul_t_pow, ← mul_assoc,
    (show Commute P.s P.t from P.commute).pow_pow j i |>.eq]

private theorem eval_mul (v w : Model n) : P.eval (v * w) = P.eval v * P.eval w := by
  have hc : Commute P.s P.t := P.commute
  rcases v with ⟨f, a⟩
  rcases w with ⟨g, b⟩
  rcases c2_cases a with rfl | rfl <;> rcases c2_cases b with rfl | rfl
  all_goals
    simp only [eval, RegularWreathProduct.mul_left, RegularWreathProduct.mul_right,
      Pi.mul_apply, inv_one, one_mul, mul_one]
  all_goals
    simp only [show flip⁻¹ = flip from rfl, show flip * flip = (1 : C2) from rfl,
      show (1 : C2).toAdd.val = 0 from rfl, show flip.toAdd.val = 1 from rfl,
      pow_zero, pow_one, mul_one]
  all_goals
    simp only [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ P.s_pow,
      ← pow_eq_pow_mod _ P.t_pow, pow_add]
  · exact (hc.pow_pow _ _).mul_mul_mul_comm _ _
  · simpa only [mul_assoc] using congrArg (· * P.z)
      ((hc.pow_pow (g 1).toAdd.val (f flip).toAdd.val).mul_mul_mul_comm
        (P.s ^ (f 1).toAdd.val) (P.t ^ (g flip).toAdd.val))
  · rw [(hc.pow_pow _ _).mul_mul_mul_comm, mul_assoc _ P.z, P.swap_base]
    simp only [mul_assoc]
  · rw [(hc.pow_pow _ _).mul_mul_mul_comm, mul_assoc _ P.z,
      ← mul_assoc P.z, P.swap_base]
    simp only [mul_assoc, ← pow_two, P.z_sq, mul_one]

private def evalHom : Model n →* S where
  toFun := P.eval
  map_one' := by simp [eval]
  map_mul' := P.eval_mul

private theorem evalHom_surjective : Function.Surjective P.evalHom := by
  intro x
  obtain ⟨i, j, b, h⟩ := P.exists_normal_form x
  let w : Model n := ⟨fun q => if q = 1 then Multiplicative.ofAdd (i.val : ZMod (2 ^ n))
    else Multiplicative.ofAdd (j.val : ZMod (2 ^ n)),
    Multiplicative.ofAdd (b.val : ZMod 2)⟩
  refine ⟨w, ?_⟩
  simpa [evalHom, eval, w, flip, ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt b.isLt] using h

private theorem evalHom_bijective : Function.Bijective P.evalHom := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨P.evalHom_surjective, ?_⟩
  rw [RegularWreathProduct.card, P.card]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [pow_add, Nat.mul_comm 2 n, pow_mul]
  ring

/-- An ABG presentation gives an isomorphism to the concrete regular wreath product. -/
public noncomputable def mulEquivRegularWreath : S ≃*
    RegularWreathProduct (Multiplicative (ZMod (2 ^ n))) (Multiplicative (ZMod 2)) :=
  (MulEquiv.ofBijective P.evalHom P.evalHom_bijective).symm

end ABG.Wreathed.Presentation

namespace ABG

/-- The intrinsic wreathed presentation identifies the actual regular wreath group. -/
public theorem IsWreathedOfHeight.nonempty_mulEquiv_regularWreath
    {S : Type*} [Group S] {n : ℕ} (h : IsWreathedOfHeight S n) :
    Nonempty (S ≃* RegularWreathProduct
      (Multiplicative (ZMod (2 ^ n))) (Multiplicative (ZMod 2))) := by
  obtain ⟨P⟩ := Wreathed.nonempty_presentation h
  exact ⟨P.mulEquivRegularWreath⟩

end ABG
