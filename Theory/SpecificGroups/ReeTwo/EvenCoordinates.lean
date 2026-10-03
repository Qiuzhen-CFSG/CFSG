module
public import Theory.SpecificGroups.ReeTwo.Sylow
/-!
# Polynomial multiplication on the even complement of the Ree two model

The cyclic-four coordinate is even precisely when it is twice a binary
coordinate. Its action on the core is either the identity or the polynomial
map below. Multiplicativity and agreement on the ten roots identify the map
with the verified square of the complement automorphism. This gives a small
formula for multiplying any two even elements, useful for finite intrinsic
profile calculations.

Source: Shinoda (1975), (2.3), pp. 81–82, through `Core` and `RootAction`.
The action proof follows the private calculation in `ParityFrattiniPowerCounts`.
-/

namespace ReeTwo.SylowModel

/-- The polynomial action of the even nonidentity complement element. -/
@[expose] public def evenCoreAction (x : Core) : Core where
  b0 := x.b0
  b1 := x.b1
  b2 := x.b0 + x.b2
  b3 := x.b0 + x.b3
  b4 := x.b0 + x.b1 + x.b4
  b5 := x.b0 + x.b5
  b6 := x.b0 + x.b0 * x.b1 + x.b6
  b7 := x.b0 + x.b0 * x.b1 + x.b0 * x.b2 + x.b5 + x.b7
  b8 := x.b1 + x.b0 * x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b0 * x.b3 + x.b5 + x.b6 + x.b8
  b9 := x.b0 + x.b1 + x.b0 * x.b2 + x.b0 * x.b3 + x.b0 * x.b1 * x.b3 + x.b0 * x.b4 + x.b5 + x.b9
private def evenCoreHom : Core →* Core where
  toFun := evenCoreAction
  map_one' := by decide +kernel
  map_mul' x y := by
    change evenCoreAction (Core.mul x y) = Core.mul (evenCoreAction x) (evenCoreAction y)
    apply Core.ext <;> simp only [evenCoreAction, Core.mul] <;> ring_nf
    all_goals reduce_mod_char
    all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
set_option maxRecDepth 8192 in
/-- The polynomial map is the square of the verified complement action. -/
public theorem evenCoreAction_eq (x : Core) : evenCoreAction x = (Core.a ^ 2) x := by
  have h : evenCoreHom = (Core.a ^ 2).toMonoidHom := by
    apply Core.hom_ext
    exact (by decide +kernel : ∀ i : CoreRoot, evenCoreHom (Core.root i) = (Core.a ^ 2) (Core.root i))
  exact DFunLike.congr_fun h x
/-- An even complement acts by either the identity or the displayed polynomial. -/
public theorem evenCoreAction_complement (b : ZMod 2) (x : Core) :
    Core.complementAction (SemidirectProduct.inr
      (Multiplicative.ofAdd (2 * b.val) : FiveFour.Cyclic 4)) x =
      if b = 0 then x else evenCoreAction x := by
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl
  · have h : (Multiplicative.ofAdd (2 * (0 : ZMod 2).val) : FiveFour.Cyclic 4) = 1 := rfl
    rw [h, map_one, map_one, MulAut.one_apply, if_pos rfl]
  · have h : (Multiplicative.ofAdd (2 * (1 : ZMod 2).val) : FiveFour.Cyclic 4) =
        FiveFour.generator 4 ^ 2 := by decide
    rw [h, map_pow, map_pow]
    change (Core.complementAction FiveFour.a ^ 2) x = _
    rw [Core.complementAction_a, ← evenCoreAction_eq, if_neg (by decide)]
/-- Construct an ambient element with even complement coordinate. -/
@[expose] public def evenElement (t : ZMod 2) (b : Core) : SylowModel :=
  ⟨b, Multiplicative.ofAdd (2 * t.val)⟩
/-- Multiplication of even elements uses only the polynomial core operations. -/
public theorem evenElement_mul (t s : ZMod 2) (x y : Core) :
    evenElement t x * evenElement s y =
      evenElement (t + s) (Core.mul x (if t = 0 then y else evenCoreAction y)) := by
  apply SemidirectProduct.ext
  · change x * Core.complementAction (SemidirectProduct.inr
        (Multiplicative.ofAdd (2 * t.val) : FiveFour.Cyclic 4)) y =
      Core.mul x (if t = 0 then y else evenCoreAction y)
    rw [evenCoreAction_complement]
    rfl
  · exact (by decide : ∀ t s : ZMod 2,
      (Multiplicative.ofAdd (2 * t.val) : FiveFour.Cyclic 4) *
        (Multiplicative.ofAdd (2 * s.val) : FiveFour.Cyclic 4) =
          (Multiplicative.ofAdd (2 * (t + s).val) : FiveFour.Cyclic 4)) t s
/-- Core coordinates together with the even complement bit. -/
public abbrev EvenPair := Core × ZMod 2

/-- Interpret an even pair in the existing Sylow group. -/
@[expose] public def evenPairElement (x : EvenPair) : SylowModel :=
  ⟨x.1, Multiplicative.ofAdd (2 * x.2.val)⟩

/-- Collected multiplication of even pairs. -/
@[expose] public def evenPairMul (x y : EvenPair) : EvenPair :=
  (x.1 * (if x.2 = 0 then y.1 else evenCoreAction y.1), x.2 + y.2)

/-- The polynomial operation agrees with the verified Sylow multiplication. -/
public theorem evenPairElement_mul (x y : EvenPair) :
    evenPairElement (evenPairMul x y) = evenPairElement x * evenPairElement y := by
  apply SemidirectProduct.ext
  · change _ = x.1 * Core.complementAction (SemidirectProduct.inr
      (Multiplicative.ofAdd (2 * x.2.val))) y.1
    rw [evenCoreAction_complement]
    rfl
  · exact (by decide : ∀ a b : ZMod 2,
      (Multiplicative.ofAdd (2 * (a + b).val) : FiveFour.Cyclic 4) =
        (Multiplicative.ofAdd (2 * a.val) : FiveFour.Cyclic 4) *
        (Multiplicative.ofAdd (2 * b.val) : FiveFour.Cyclic 4)) x.2 y.2

/-- Even coordinates are faithful. -/
public theorem evenPairElement_injective : Function.Injective evenPairElement := by
  intro x y h
  apply Prod.ext
  · exact congrArg SemidirectProduct.left h
  · have ht := congrArg SemidirectProduct.right h
    exact (by decide : ∀ a b : ZMod 2,
      (Multiplicative.ofAdd (2 * a.val) : FiveFour.Cyclic 4) =
        (Multiplicative.ofAdd (2 * b.val) : FiveFour.Cyclic 4) → a = b) x.2 y.2 ht

/-- The empty even word is the identity. -/
public theorem evenPairElement_one : evenPairElement (1, 0) = 1 := rfl

/-- Evaluate a word using the polynomial operation. -/
@[expose] public def evenPairProd : List EvenPair → EvenPair
  | [] => (1, 0)
  | x :: xs => evenPairMul x (evenPairProd xs)

/-- Polynomial word evaluation agrees with group word evaluation. -/
public theorem evenPairElement_prod (xs : List EvenPair) :
    evenPairElement (evenPairProd xs) = (xs.map evenPairElement).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [evenPairProd, evenPairElement_mul, ih, List.map_cons,
      List.prod_cons]

end ReeTwo.SylowModel
