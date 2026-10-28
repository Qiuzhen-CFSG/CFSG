module

public import Theory.SpecificGroups.ReeTwo.ParityFrattiniCoordinates

/-!
# Power-fiber counts for the Ree two parity projection

The seven-bit parametrization of each parity fiber reduces the required counts
of solutions of x² = 1 and x⁴ = 1 to finite coordinate calculations. To keep
these calculations small, we first give polynomial formulas for the even
complement action and for ordinary and twisted squares. The action formula is
proved multiplicative and checked on the ten generating roots, linking it to
the verified `Core`, `RootAction`, and `Sylow` operations. The square formulas
are polynomial identities over ZMod 2.

An explicit equivalence replaces the seven-bit function space by a product of
seven binary fields. Kernel reduction then certifies both counts in all sixteen
fibers against `parityProfile`; cardinality transport gives the public theorem.
No identification of the projection kernel as the Frattini subgroup is used.

Source: Shinoda (1975), (2.3), pp. 81–82, with root indices shifted by three.
The quotient and ordered basis conventions are those of
`ParityFrattiniCoordinates` and `MaximalParityProfiles`.
-/

namespace ReeTwo.SylowModel

private def evenAction (x : Core) : Core where
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

private def evenHom : Core →* Core where
  toFun := evenAction
  map_one' := by decide +kernel
  map_mul' x y := by
    change evenAction (Core.mul x y) = Core.mul (evenAction x) (evenAction y)
    apply Core.ext <;> simp only [evenAction, Core.mul] <;> ring_nf
    all_goals reduce_mod_char
    all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

set_option maxRecDepth 8192 in
private theorem evenAction_eq (x : Core) :
    evenAction x = (Core.a ^ 2) x := by
  have h : evenHom = (Core.a ^ 2).toMonoidHom := by
    apply Core.hom_ext
    exact (by decide +kernel : ∀ i : CoreRoot, evenHom (Core.root i) = (Core.a ^ 2) (Core.root i))
  exact DFunLike.congr_fun h x

private theorem even_complement (b : ZMod 2) (x : Core) :
    Core.complementAction (SemidirectProduct.inr
      (Multiplicative.ofAdd (2 * b.val) : FiveFour.Cyclic 4)) x =
      if b = 0 then x else evenAction x := by
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl
  · have h : (Multiplicative.ofAdd (2 * (0 : ZMod 2).val) : FiveFour.Cyclic 4) = 1 := rfl
    rw [h, map_one, map_one, MulAut.one_apply, if_pos rfl]
  · have h : (Multiplicative.ofAdd (2 * (1 : ZMod 2).val) : FiveFour.Cyclic 4) =
        FiveFour.generator 4 ^ 2 := by decide
    rw [h, map_pow, map_pow]
    change (Core.complementAction FiveFour.a ^ 2) x = _
    rw [Core.complementAction_a, ← evenAction_eq, if_neg (by decide)]

private def fiberCore (v : ParityQuotient) (w : Fin 7 → ZMod 2) : Core :=
  ⟨v.toAdd 1, v.toAdd 2, v.toAdd 3 + w 0, w 0,
    w 1, w 2, w 3, w 4, w 5, w 6⟩

private def squareCore (v : ParityQuotient) (w : Fin 7 → ZMod 2) : Core :=
  let x := fiberCore v w
  x * (if v.toAdd 0 = 0 then x else evenAction x)

private theorem parityElement_square (v : ParityQuotient) (w : Fin 7 → ZMod 2) :
    ((parityElement v w : ParityKernel) : SylowModel) ^ 2 =
      SemidirectProduct.inl (squareCore v w) := by
  rw [pow_two]
  apply SemidirectProduct.ext
  · change fiberCore v w * Core.complementAction (SemidirectProduct.inr
        (Multiplicative.ofAdd (2 * (v.toAdd 0).val))) (fiberCore v w) = _
    rw [even_complement]
    rfl
  · exact (by decide : ∀ b : ZMod 2,
      (Multiplicative.ofAdd (2 * b.val) : FiveFour.Cyclic 4) *
        (Multiplicative.ofAdd (2 * b.val) : FiveFour.Cyclic 4) = 1) _

private theorem square_test (v : ParityQuotient) (w : Fin 7 → ZMod 2) :
    parityElement v w ^ 2 = 1 ↔ squareCore v w = 1 := by
  rw [← Subtype.coe_inj]
  change ((parityElement v w : ParityKernel) : SylowModel) ^ 2 = 1 ↔ _
  rw [parityElement_square, ← map_one (SemidirectProduct.inl : Core →* SylowModel),
    SemidirectProduct.inl_inj]

private theorem fourth_test (v : ParityQuotient) (w : Fin 7 → ZMod 2) :
    parityElement v w ^ 4 = 1 ↔ squareCore v w * squareCore v w = 1 := by
  rw [← Subtype.coe_inj]
  change ((parityElement v w : ParityKernel) : SylowModel) ^ 4 = 1 ↔ _
  change ((parityElement v w : ParityKernel) : SylowModel) ^ (2 * 2) = 1 ↔ _
  rw [pow_mul, parityElement_square, ← map_pow,
    ← map_one (SemidirectProduct.inl : Core →* SylowModel), SemidirectProduct.inl_inj,
    pow_two]

private abbrev SevenBits := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2

private def bitsEquiv : SevenBits ≃ (Fin 7 → ZMod 2) where
  toFun w := ![w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1, w.2.2.2.2.2.2]
  invFun w := (w 0, w 1, w 2, w 3, w 4, w 5, w 6)
  left_inv _ := rfl
  right_inv w := by funext i; fin_cases i <;> rfl

private def plainSquare (x : Core) : Core where
  b0 := 0
  b1 := 0
  b2 := 0
  b3 := 0
  b4 := 0
  b5 := x.b1 + x.b0 * x.b2 + x.b0 * x.b3
  b6 := x.b1 * x.b2 + x.b0 * x.b3 + x.b0 * x.b4
  b7 := x.b2 * x.b3 + x.b0 * x.b4 + x.b1 * x.b4
  b8 := x.b3 + x.b1 * x.b4 + x.b2 * x.b4
  b9 := x.b2 + x.b1 * x.b4 + x.b0 * x.b1 * x.b4 + x.b0 * x.b3 * x.b4 + x.b4 * x.b5 + x.b3 * x.b6 +
    x.b1 * x.b7 + x.b0 * x.b8

private theorem plainSquare_eq (x : Core) : x * x = plainSquare x := by
  change Core.mul x x = _
  apply Core.ext <;> simp only [Core.mul, plainSquare] <;> ring_nf
  all_goals reduce_mod_char
  all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
  all_goals ring_nf
  all_goals reduce_mod_char

private def twistedSquare (x : Core) : Core where
  b0 := 0
  b1 := 0
  b2 := x.b0
  b3 := x.b0
  b4 := x.b0 + x.b1
  b5 := x.b0 + x.b1 + x.b0 * x.b2 + x.b0 * x.b3
  b6 := x.b0 + x.b0 * x.b1 + x.b1 * x.b2 + x.b0 * x.b3 + x.b0 * x.b4
  b7 := x.b0 + x.b0 * x.b1 + x.b0 * x.b2 + x.b0 * x.b3 + x.b2 * x.b3 + x.b0 * x.b4 + x.b1 * x.b4 +
    x.b5
  b8 := x.b1 + x.b0 * x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b3 + x.b0 * x.b4 + x.b1 * x.b4 +
    x.b2 * x.b4 + x.b5 + x.b6
  b9 := x.b0 + x.b0 * x.b1 + x.b2 + x.b0 * x.b2 + x.b0 * x.b3 + x.b1 * x.b4 + x.b0 * x.b1 * x.b4 +
    x.b0 * x.b3 * x.b4 + x.b5 + x.b0 * x.b5 + x.b1 * x.b5 + x.b4 * x.b5 + x.b0 * x.b6 +
    x.b3 * x.b6 + x.b1 * x.b7 + x.b0 * x.b8

private theorem twistedSquare_eq (x : Core) : x * evenAction x = twistedSquare x := by
  change Core.mul x (evenAction x) = _
  apply Core.ext <;> simp only [Core.mul, evenAction, twistedSquare] <;> ring_nf
  all_goals reduce_mod_char
  all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide,
    show ∀ z : ZMod 2, z ^ 3 = z from by decide]
  all_goals ring_nf
  all_goals reduce_mod_char

private def fastSquare (v : ParityQuotient) (w : Fin 7 → ZMod 2) : Core :=
  if v.toAdd 0 = 0 then plainSquare (fiberCore v w) else twistedSquare (fiberCore v w)

private theorem squareCore_eq (v : ParityQuotient) (w : Fin 7 → ZMod 2) :
    squareCore v w = fastSquare v w := by
  dsimp [squareCore, fastSquare]
  split
  · rw [plainSquare_eq]
  · rw [twistedSquare_eq]

set_option maxRecDepth 8192 in
private theorem counts : ∀ v : ParityQuotient,
    (Fintype.card {w : SevenBits // fastSquare v (bitsEquiv w) = 1},
      Fintype.card {w : SevenBits // plainSquare (fastSquare v (bitsEquiv w)) = 1}) =
      parityProfile v := by decide +kernel

private theorem square_card (v : ParityQuotient) :
    Nat.card {w : Fin 7 → ZMod 2 // parityElement v w ^ 2 = 1} =
      Fintype.card {w : SevenBits // fastSquare v (bitsEquiv w) = 1} := by
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact (bitsEquiv.subtypeEquiv (fun w =>
    ((square_test v (bitsEquiv w)).trans (by rw [squareCore_eq])).symm)).symm

private theorem fourth_card (v : ParityQuotient) :
    Nat.card {w : Fin 7 → ZMod 2 // parityElement v w ^ 4 = 1} =
      Fintype.card {w : SevenBits // plainSquare (fastSquare v (bitsEquiv w)) = 1} := by
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact (bitsEquiv.subtypeEquiv (fun w =>
    ((fourth_test v (bitsEquiv w)).trans (by rw [squareCore_eq, plainSquare_eq])).symm)).symm

/-- The square and fourth-power solution counts in every parity-projection fiber. -/
public theorem parityProjection_powerFiberCounts : ∀ v,
    (parityProjection.powerFiberCard v 2, parityProjection.powerFiberCard v 4) =
      parityProfile v := by
  intro v
  rw [parityProjection_powerFiberCard, parityProjection_powerFiberCard,
    square_card, fourth_card]
  exact counts v

end ReeTwo.SylowModel
