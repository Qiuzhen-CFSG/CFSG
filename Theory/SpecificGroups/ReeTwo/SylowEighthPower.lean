module

public import Theory.SpecificGroups.ReeTwo.MaximalCharacters

/-!
# Eighth powers in the Ree two Sylow model

An element has nontrivial eighth power exactly when its cyclic-four parity
and root-3 character are both nontrivial.

Project the core onto its first six binary coordinates. Their multiplication
closes, and the cyclic-four action descends to this group: compatibility is
verified on the ten generating roots. A kernel-checked calculation on this
64-element group and the four complement coordinates shows that a fourth
power has its first four coordinates zero. The product of its next two
coordinates is parity times the original root-3 coordinate. Squaring such
a core element leaves only that product in the final, central coordinate.

Source: Shinoda (1975), (2.3), pp. 81–83, through the verified multiplication
and action in `Core`, `RootAction`, and `Sylow`. The finite certificate uses
only the six-coordinate formulas proved here.
-/

namespace ReeTwo.SylowModel

namespace EighthPower

@[ext] structure Head where
  b0 : ZMod 2
  b1 : ZMod 2
  b2 : ZMod 2
  b3 : ZMod 2
  b4 : ZMod 2
  b5 : ZMod 2
  deriving DecidableEq

def mul (x y : Head) : Head :=
  ⟨x.b0 + y.b0, x.b1 + y.b1, x.b2 + y.b2, x.b3 + y.b3, x.b4 + y.b4,
    x.b5 + x.b2 * y.b0 + x.b3 * y.b0 + x.b1 * y.b1 + y.b5⟩
instance : Mul Head := ⟨mul⟩
instance : One Head := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩
instance : Inv Head := ⟨fun x => (x * x) * x⟩
instance : Group Head := Group.ofLeftAxioms
  (by intro x y z; change mul (mul x y) z = mul x (mul y z)
      apply Head.ext <;> simp only [mul] <;> ring)
  (by intro x; change mul ⟨0, 0, 0, 0, 0, 0⟩ x = x
      apply Head.ext <;> simp [mul])
  (by intro x; change mul (mul (mul x x) x) x = ⟨0, 0, 0, 0, 0, 0⟩
      apply Head.ext <;> simp only [mul] <;> ring_nf <;> reduce_mod_char)

def head : Core →* Head where
  toFun x := ⟨x.b0, x.b1, x.b2, x.b3, x.b4, x.b5⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mul_eq (x y : Head) : x * y = mul x y := rfl

def act : Head →* Head where
  toFun x := ⟨x.b0, x.b0 + x.b1, x.b0 + x.b1 + x.b2, x.b1 + x.b3,
    x.b0 + x.b1 + x.b3 + x.b4, x.b0 + x.b0 * x.b1 + x.b5⟩
  map_one' := by apply Head.ext <;> decide
  map_mul' x y := by
    apply Head.ext
    all_goals simp only [mul_eq, mul]
    all_goals ring_nf
    all_goals reduce_mod_char

theorem head_a (x : Core) : head (Core.a x) = act (head x) := by
  have h : head.comp Core.a.toMonoidHom = act.comp head := by
    apply Core.hom_ext
    exact (by decide +kernel : ∀ i : CoreRoot,
      head (Core.a (Core.root i)) = act (head (Core.root i)))
  exact DFunLike.congr_fun h x

instance : Fintype Head := Fintype.ofEquiv (Fin 6 → ZMod 2)
  { toFun := fun v => ⟨v 0, v 1, v 2, v 3, v 4, v 5⟩
    invFun := fun x => ![x.b0, x.b1, x.b2, x.b3, x.b4, x.b5]
    left_inv := by intro v; funext i; fin_cases i <;> rfl
    right_inv := by intro x; rfl }

def action (t : FiveFour.Cyclic 4) (v : Head) : Head := act^[t.toAdd.val] v

theorem head_action (t : FiveFour.Cyclic 4) (x : Core) :
    head (Core.complementAction (SemidirectProduct.inr t) x) = action t (head x) := by
  conv_lhs => rw [← FiveFour.generator_pow_val t, map_pow, map_pow]
  change head ((Core.a ^ t.toAdd.val) x) = _
  unfold action
  generalize t.toAdd.val = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, head_a, ih, Function.iterate_succ_apply']

def square (v : Head × FiveFour.Cyclic 4) : Head × FiveFour.Cyclic 4 :=
  (mul v.1 (action v.2 v.1), v.2 * v.2)
def coords (x : SylowModel) : Head × FiveFour.Cyclic 4 := (head x.left, x.right)

theorem coords_square (x : SylowModel) : coords (x * x) = square (coords x) := by
  apply Prod.ext
  · exact (map_mul head _ _).trans (congrArg (fun v => head x.left * v) (head_action _ _))
  · rfl

theorem fourth_head : ∀ (h : Head) (t : FiveFour.Cyclic 4),
    let v := (square (square (h, t))).1
    v.b0 = 0 ∧ v.b1 = 0 ∧ v.b2 = 0 ∧ v.b3 = 0 ∧
    v.b4 * v.b5 = (parity t).toAdd * h.b0 := by decide +kernel

theorem core_square (x : Core) (h0 : x.b0 = 0) (h1 : x.b1 = 0)
    (h2 : x.b2 = 0) (h3 : x.b3 = 0) :
    x * x = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, x.b4 * x.b5⟩ := by
  change Core.mul x x = _
  apply Core.ext <;> simp only [Core.mul, h0, h1, h2, h3]
  all_goals ring_nf
  all_goals reduce_mod_char

theorem eighth_eq (x : SylowModel) :
    x ^ 8 = SemidirectProduct.inl
      (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, (parity x.right).toAdd * x.left.b0⟩ : Core) := by
  have hr : (x ^ 4).right = 1 := by
    change SemidirectProduct.rightHom (x ^ 4) = 1
    rw [map_pow]
    exact (by decide +kernel : ∀ t : FiveFour.Cyclic 4, t ^ 4 = 1) x.right
  have hh : coords (x ^ 4) = square (square (coords x)) := by
    change coords (x ^ (2 * 2)) = _
    rw [pow_mul]
    simp only [pow_two, coords_square]
  have hc := fourth_head (head x.left) x.right
  change (square (square (coords x))).1.b0 = 0 ∧
    (square (square (coords x))).1.b1 = 0 ∧
    (square (square (coords x))).1.b2 = 0 ∧
    (square (square (coords x))).1.b3 = 0 ∧
    (square (square (coords x))).1.b4 * (square (square (coords x))).1.b5 =
      (parity x.right).toAdd * x.left.b0 at hc
  rw [← hh] at hc
  have hs := core_square (x ^ 4).left hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
  rw [show (x ^ 4).left.b4 * (x ^ 4).left.b5 =
    (parity x.right).toAdd * x.left.b0 from hc.2.2.2.2] at hs
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, pow_two]
  apply SemidirectProduct.ext
  · change (x ^ 4).left * Core.complementAction (SemidirectProduct.inr (x ^ 4).right)
      (x ^ 4).left = _
    rw [hr, map_one, map_one, MulAut.one_apply]
    exact hs
  · change (x ^ 4).right * (x ^ 4).right = 1
    rw [hr, one_mul]

end EighthPower

/-- Nontrivial eighth powers form the fiber where parity and root 3 are both nontrivial. -/
public theorem eighth_power_ne_one_iff (x : SylowModel) : x ^ 8 ≠ 1 ↔
    character x = FiveFour.generator 2 ∧ rootThreeCharacter x = FiveFour.generator 2 := by
  have hz (c : ZMod 2) :
      (SemidirectProduct.inl (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, c⟩ : Core) : SylowModel) = 1 ↔ c = 0 := by
    constructor
    · intro h
      exact congrArg (fun y : SylowModel => y.left.b9) h
    · rintro rfl
      rfl
  rw [EighthPower.eighth_eq, ne_eq, hz]
  exact (by decide +kernel : ∀ (u : FiveFour.Cyclic 2) (v : ZMod 2),
    ¬ u.toAdd * v = 0 ↔
      u = FiveFour.generator 2 ∧ Multiplicative.ofAdd v = FiveFour.generator 2)
    (parity x.right) x.left.b0

end ReeTwo.SylowModel
