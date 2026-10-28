module
public import Theory.SpecificGroups.ExoticTwoGroup.ActionModel
import Mathlib.Tactic

/-!
# Quarter-turn coordinates in a C₄-square

The quarter-turn and the two prescribed inner actions have sixteen distinct
words. Their eight even words are exactly the words fixing the basis squares.
The final finite identity is the split-lift obstruction used in MacWilliams,
Trans. AMS 150 (1970), §4 (xx)–(xxii), printed p.399.
-/

namespace ExoticTwoGroup.QuarterTurn
open C4SquareExtension Subgroup ActionModel

private def act₁ (x : Model) : Model :=
  (Multiplicative.ofAdd (-x.1.toAdd + 2 * x.2.toAdd),
    Multiplicative.ofAdd (-x.2.toAdd))
private def act₂ (x : Model) : Model :=
  (Multiplicative.ofAdd (-x.1.toAdd),
    Multiplicative.ofAdd (2 * x.1.toAdd - x.2.toAdd))

private theorem basis_evaluate (f : Model →* Model) (x : Model) :
    f x = f u ^ x.1.toAdd.val * f v ^ x.2.toAdd.val := by
  have hx : x = u ^ x.1.toAdd.val * v ^ x.2.toAdd.val :=
    (by rw [u_eq, v_eq]; decide : ∀ x : Model,
      x = u ^ x.1.toAdd.val * v ^ x.2.toAdd.val) x
  conv_lhs => rw [hx, map_mul, map_pow, map_pow]

private theorem inner₁_apply (x : Model) : inner₁ x = act₁ x := by
  have he := basis_evaluate inner₁.toMonoidHom x
  change inner₁ x = inner₁ u ^ x.1.toAdd.val * inner₁ v ^ x.2.toAdd.val at he
  rw [inner₁_u, inner₁_v] at he
  exact he.trans ((by rw [u_eq, v_eq]; decide : ∀ x : Model,
    (u⁻¹) ^ x.1.toAdd.val * (u ^ 2 * v⁻¹) ^ x.2.toAdd.val = act₁ x) x)

private theorem inner₂_apply (x : Model) : inner₂ x = act₂ x := by
  have he := basis_evaluate inner₂.toMonoidHom x
  change inner₂ x = inner₂ u ^ x.1.toAdd.val * inner₂ v ^ x.2.toAdd.val at he
  rw [inner₂_u, inner₂_v] at he
  exact he.trans ((by rw [u_eq, v_eq]; decide : ∀ x : Model,
    (u⁻¹ * v ^ 2) ^ x.1.toAdd.val * (v⁻¹) ^ x.2.toAdd.val = act₂ x) x)

/-- Simultaneous inversion acts by group inversion on every coordinate. -/
public theorem inversion_apply (x : Model) : inversion x = x⁻¹ := by
  have he := basis_evaluate inversion.toMonoidHom x
  change inversion x = inversion u ^ x.1.toAdd.val * inversion v ^ x.2.toAdd.val at he
  rw [inversion_u, inversion_v] at he
  exact he.trans ((by rw [u_eq, v_eq]; decide : ∀ x : Model,
    (u⁻¹) ^ x.1.toAdd.val * (v⁻¹) ^ x.2.toAdd.val = x⁻¹) x)

/-- The rotation sending the first basis element to the second and the second
 to the inverse of the first. -/
public def rotation : MulAut Model where
  toFun x := (x.2⁻¹, x.1)
  invFun x := (x.2, x.1⁻¹)
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by ext <;> simp [mul_comm]

private theorem rotation_apply (x : Model) : rotation x = (x.2⁻¹, x.1) := rfl
public theorem rotation_u : rotation u = v := by rw [u_eq, v_eq]; decide
public theorem rotation_v : rotation v = u⁻¹ := by rw [u_eq, v_eq]; decide
public theorem rotation_square : rotation ^ 2 = inversion := by
  apply MulEquiv.ext
  intro x
  simp only [pow_two, MulAut.mul_apply, rotation_apply, inversion_apply]
  rfl
public theorem rotation_four : rotation ^ 4 = 1 := by
  apply MulEquiv.ext
  exact (by decide : ∀ x : Model, (rotation ^ 4) x = x)
public theorem rotation_inner₁ : rotation * inner₁ * rotation⁻¹ = inner₂ := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply MulEquiv.ext
  intro x
  simp only [MulAut.mul_apply, inner₁_apply, inner₂_apply, rotation_apply]
  exact (by decide : ∀ x : Model, ((act₁ x).2⁻¹, (act₁ x).1) = act₂ (x.2⁻¹, x.1)) x
public theorem rotation_inner₂ : rotation * inner₂ * rotation⁻¹ = inner₁ := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply MulEquiv.ext
  intro x
  simp only [MulAut.mul_apply, inner₁_apply, inner₂_apply, rotation_apply]
  exact (by decide : ∀ x : Model, ((act₂ x).2⁻¹, (act₂ x).1) = act₁ (x.2⁻¹, x.1)) x

/-- Each inner action induces the identity modulo the square-trivial part. -/
public theorem inner_defect_squares (d : Model) :
    (inner₁ d * d⁻¹) ^ 2 = 1 ∧ (inner₂ d * d⁻¹) ^ 2 = 1 := by
  rw [inner₁_apply, inner₂_apply]
  exact (by decide : ∀ d : Model,
    (act₁ d * d⁻¹) ^ 2 = 1 ∧ (act₂ d * d⁻¹) ^ 2 = 1) d

private abbrev Bits := Fin 2 × Fin 2 × Fin 4
private def word (q : Bits) : MulAut Model :=
  inner₁ ^ q.1.val * inner₂ ^ q.2.1.val * rotation ^ q.2.2.val
private theorem aut_pow_apply (f : MulAut Model) (n : ℕ) (x : Model) :
    (f ^ n) x = f^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']

private def wordEval (q : Bits) (x : Model) : Model :=
  act₁^[q.1.val] (act₂^[q.2.1.val] ((fun x : Model => (x.2⁻¹, x.1))^[q.2.2.val] x))
private theorem word_apply (q : Bits) (x : Model) : word q x = wordEval q x := by
  simp only [word, MulAut.mul_apply, aut_pow_apply,
    show (inner₁ : Model → Model) = act₁ from funext inner₁_apply,
    show (inner₂ : Model → Model) = act₂ from funext inner₂_apply,
    show (rotation : Model → Model) = (fun x => (x.2⁻¹, x.1)) from funext rotation_apply,
    wordEval]
private theorem word_injective : Function.Injective word := by
  have h : Function.Injective (fun q : Bits => (word q u, word q v)) := by
    simp_rw [word_apply, u_eq, v_eq]
    decide
  exact fun _ _ heq => h (congrArg (fun f : MulAut Model => (f u, f v)) heq)

/-- Every automorphism fixing the basis squares in the sixteen-element image
is an even word in the quarter-turn. -/
public theorem exists_even_word (A : Subgroup (MulAut Model)) (hA : Nat.card A = 16)
    (h₁ : inner₁ ∈ A) (h₂ : inner₂ ∈ A) (ht : rotation ∈ A)
    (f : A) (hu : (f : MulAut Model) (u ^ 2) = u ^ 2)
    (hv : (f : MulAut Model) (v ^ 2) = v ^ 2) :
    ∃ i j k : Fin 2, (f : MulAut Model) =
      inner₁ ^ i.val * inner₂ ^ j.val * (rotation ^ 2) ^ k.val := by
  let w : Bits → A := fun q => ⟨word q,
    mul_mem (mul_mem (pow_mem h₁ _) (pow_mem h₂ _)) (pow_mem ht _)⟩
  have hinj : Function.Injective w := fun _ _ h => word_injective (congrArg Subtype.val h)
  have hsurj := ((Nat.bijective_iff_injective_and_card w).mpr
    ⟨hinj, by simpa only [Nat.card_prod, Nat.card_fin] using hA.symm⟩).2
  obtain ⟨q, hq⟩ := hsurj f
  have he : word q = (f : MulAut Model) := congrArg Subtype.val hq
  have hfinite : ∀ q : Bits, word q (u ^ 2) = u ^ 2 → word q (v ^ 2) = v ^ 2 →
      ∃ k : Fin 2, q.2.2.val = 2 * k.val := by
    simp_rw [word_apply, u_eq, v_eq]
    decide
  obtain ⟨k, hk⟩ := hfinite q (he ▸ hu) (he ▸ hv)
  exact ⟨q.1, q.2.1, k, by rw [← he]; dsimp [word]; rw [hk, pow_mul]⟩

/-- Commuting involutory inner lifts constrain their quarter-turn defects so
that both commutators with the square of the quarter-turn are square-trivial. -/
public theorem split_defect_squares (d e : Model)
    (hd : inner₂ d = d⁻¹) (he : inner₁ e = e⁻¹)
    (hcomm : d * inner₂ e = e * inner₁ d) :
    (rotation d * e) ^ 2 = 1 ∧ (rotation e * d) ^ 2 = 1 := by
  simp only [inner₁_apply, inner₂_apply] at hd he hcomm
  simp only [rotation_apply]
  exact (by decide : ∀ d e : Model,
    act₂ d = d⁻¹ → act₁ e = e⁻¹ → d * act₂ e = e * act₁ d →
    (((d.2⁻¹, d.1) : Model) * e) ^ 2 = 1 ∧
      (((e.2⁻¹, e.1) : Model) * d) ^ 2 = 1) d e hd he hcomm

end ExoticTwoGroup.QuarterTurn
