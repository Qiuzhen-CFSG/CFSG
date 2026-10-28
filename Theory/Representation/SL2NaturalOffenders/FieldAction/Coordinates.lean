module

public import Theory.Representation.SL2NaturalOffenders.FieldAction.Basic

/-!
# Coordinates and counting for a semilinear centralizer

A nonidentity linear involution in characteristic two has a basis in which it
is the upper transvection. Every commuting semilinear map then has an upper
triangular matrix with equal diagonal entries. A separate scalar estimate
embeds the product of the fixed scalars and any scalar eigenspace of a
nontrivial field automorphism into the field itself.

These elementary linear and field calculations are used in the natural-module
offender estimate for Aschbacher--Smith B.4.2(1), printed p.86 of the combined
manuscript (1 March 2004).
-/

public section

namespace Representation.SL2NaturalOffenders
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- A nonidentity linear involution is an upper transvection in a suitable basis. -/
theorem involution_coordinates (T : Module.End F (Fin 2 → F))
    (hsq : T * T = 1) (hne : T ≠ 1) :
    ∃ e : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F), ∀ v,
      e (T v) = ![e v 0 + e v 1, e v 1] := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  obtain ⟨v, hv⟩ : ∃ v, T v ≠ v := by
    by_contra! h
    exact hne (LinearMap.ext h)
  let w := T v - v
  have hw : w ≠ 0 := sub_ne_zero.mpr hv
  have hv' : T v = w + v := by simp [w]
  have hw' : T w = w := by
    have h := LinearMap.congr_fun hsq v
    change T (T v) = v at h
    change T (T v - v) = T v - v
    rw [map_sub, h]
    ext i
    simp [CharTwo.sub_eq_add, add_comm]
  let L : (Fin 2 → F) →ₗ[F] (Fin 2 → F) :=
    { toFun := fun x => x 0 • w + x 1 • v
      map_add' := by intro x y; simp only [Pi.add_apply, add_smul]; abel
      map_smul' := by intro c x; simp [smul_add, mul_smul] }
  have hL : Function.Injective L := by
    intro x y he
    change x 0 • w + x 1 • v = y 0 • w + y 1 • v at he
    have he' := congrArg T he
    simp only [map_add, map_smul, hw', hv'] at he'
    have hz : (x 1 - y 1) • w = 0 := by
      calc
        _ = ((x 0 • w + x 1 • (w + v)) - (y 0 • w + y 1 • (w + v))) -
            ((x 0 • w + x 1 • v) - (y 0 • w + y 1 • v)) := by
          simp only [smul_add, sub_smul]
          abel
        _ = 0 := by rw [he, he']; simp
    have h1 : x 1 = y 1 := sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hw)
    rw [h1] at he
    have h0 := smul_left_injective F hw (add_right_cancel he)
    ext i
    fin_cases i <;> assumption
  let e := (LinearEquiv.ofBijective L ⟨hL, Finite.surjective_of_injective hL⟩).symm
  refine ⟨e, fun x => ?_⟩
  apply e.symm.injective
  rw [e.symm_apply_apply]
  change T x = L ![e x 0 + e x 1, e x 1]
  have hx : x = L (e x) := (e.symm_apply_apply x).symm
  conv_lhs => rw [hx]
  change T (e x 0 • w + e x 1 • v) = (e x 0 + e x 1) • w + e x 1 • v
  rw [map_add, map_smul, map_smul, hw', hv', smul_add, add_smul]
  abel

omit [Algebra (ZMod 2) F] in
/-- Fixed scalars times a twisted fixed line have cardinality at most the field. -/
theorem coefficient_eigenspace_card_mul_le (σ : F ≃+* F) (hne : σ ≠ 1) (d : F) :
    Nat.card {x : F // σ x = x} * Nat.card {x : F // σ x = d * x} ≤ Nat.card F := by
  obtain ⟨c, hc⟩ : ∃ c, σ c * d ≠ c := by
    by_contra! h
    have hd : d = 1 := by simpa using h 1
    apply hne
    ext x
    simpa [hd] using h x
  let f : {x : F // σ x = x} × {x : F // σ x = d * x} → F :=
    fun x => x.1.val + c * x.2.val
  have hf : Function.Injective f := by
    intro x y he
    change x.1.val + c * x.2.val = y.1.val + c * y.2.val at he
    have he' := congrArg σ he
    simp only [map_add, map_mul, x.1.property, x.2.property, y.1.property, y.2.property] at he'
    have hz : (σ c * d - c) * (x.2.val - y.2.val) = 0 := by
      linear_combination he' - he
    have h2 : x.2.val = y.2.val := sub_eq_zero.mp
      ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc))
    have h1 : x.1.val = y.1.val := by rw [h2] at he; exact add_right_cancel he
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf


omit [Finite F] [Algebra (ZMod 2) F] in
/-- Commuting with the upper transvection forces equal diagonal coefficients. -/
theorem commuting_transvection_shape (f : (Fin 2 → F) →+ (Fin 2 → F))
    (σ : F ≃+* F)
    (hσ : ∀ (c : F) (v : Fin 2 → F), f (c • v) = σ c • f v)
    (hcomm : ∀ v, f ![v 0 + v 1, v 1] = ![f v 0 + f v 1, f v 1]) :
    ∀ v, f v = ![f ![0, 1] 1 * σ (v 0) + f ![0, 1] 0 * σ (v 1),
      f ![0, 1] 1 * σ (v 1)] := by
  have hU : ![(1 : F), 1] = ![1, 0] + ![0, 1] := by ext i; fin_cases i <;> simp
  have he := hcomm ![0, 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    zero_add] at he
  rw [hU, map_add] at he
  have he0 : f ![1, 0] = ![f ![0, 1] 1, 0] := by
    ext i
    fin_cases i
    · change f ![1, 0] 0 = f ![0, 1] 1
      have h := congrFun he 0
      simp only [Pi.add_apply, Matrix.cons_val_zero] at h
      linear_combination h
    · change f ![1, 0] 1 = 0
      have h := congrFun he 1
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
      linear_combination h
  intro v
  have hv : v = v 0 • ![1, 0] + v 1 • ![0, 1] := by ext i; fin_cases i <;> simp
  calc
    f v = σ (v 0) • f ![1, 0] + σ (v 1) • f ![0, 1] := by
      conv_lhs => rw [hv, map_add, hσ, hσ]
    _ = _ := by ext i; fin_cases i <;> simp [he0, mul_comm]

end Representation.SL2NaturalOffenders
