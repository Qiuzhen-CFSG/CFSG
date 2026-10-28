module

public import Theory.SpecificGroups.ReeTwo.MaximalParityProfiles

/-!
# Binary coordinates for the Ree two parity kernel

The parity kernel has even cyclic-four coordinate `t`. Its rank-four binary
quotient records `(t/2, b₀, b₁, b₂+b₃)`. The last three coordinates are additive
on the core and invariant under the even complement action; invariance is
proved on the ten generating roots using the verified action in `RootAction`.
The chosen lifts are rootOne², root 0, root 1, and root 2.

Each quotient fiber has seven independent binary parameters. Explicit inverse
maps give the fiber cardinality 128 and reduce every power-fiber count to a
power equation in those seven parameters. Identifying the kernel as Frattini
and evaluating the power counts are separate mathematical steps.

Source: Shinoda (1975), (2.3), pp. 81–82, with root indices shifted by three,
as realized by `Core`, `RootAction`, `Sylow`, and `MaximalCharacters`.
-/

namespace ReeTwo.SylowModel
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The kernel of parity on the cyclic-four factor. -/
public abbrev ParityKernel := (maximalCharacter 1 0 0).ker

/-- The three core coordinates fixed by the even complement action. -/
@[expose] public def parityCoreCoordinates : Core →* Multiplicative (Fin 3 → ZMod 2) where
  toFun x := Multiplicative.ofAdd ![x.b0, x.b1, x.b2 + x.b3]
  map_one' := by ext i; fin_cases i <;> rfl
  map_mul' x y := by
    change (![x.b0 + y.b0, x.b1 + y.b1, (x.b2 + y.b2) + (x.b3 + y.b3)] : Fin 3 → ZMod 2) = _ + _
    funext i
    fin_cases i
    · rfl
    · rfl
    · change (x.b2 + y.b2) + (x.b3 + y.b3) = (x.b2 + x.b3) + (y.b2 + y.b3)
      ring

/-- The even complement acts trivially on the three core coordinates. -/
public theorem parityCoreCoordinates_action (t : FiveFour.Cyclic 4) (ht : parity t = 1)
    (x : Core) : parityCoreCoordinates (Core.complementAction (SemidirectProduct.inr t) x) =
      parityCoreCoordinates x := by
  have hh : parityCoreCoordinates.comp
      (Core.complementAction (SemidirectProduct.inr t)).toMonoidHom = parityCoreCoordinates := by
    apply Core.hom_ext
    exact (by decide +kernel : ∀ t : FiveFour.Cyclic 4, parity t = 1 → ∀ i : CoreRoot,
      parityCoreCoordinates (Core.complementAction (SemidirectProduct.inr t) (Core.root i)) =
        parityCoreCoordinates (Core.root i)) t ht
  exact DFunLike.congr_fun hh x

/-- Membership in the maximal-character kernel is exactly even complement parity. -/
public theorem mem_parityKernel (x : SylowModel) : x ∈ (maximalCharacter 1 0 0).ker ↔
    parity x.right = 1 := by
  simp [maximalCharacter, character, MonoidHom.mem_ker, show (1 : ZMod 2).val = 1 from rfl]

/-- Read the four quotient coordinates from a Sylow element. -/
@[expose] public def parityCoordinates (x : SylowModel) : ParityQuotient :=
  Multiplicative.ofAdd ![(x.right.toAdd.val / 2 : ℕ), x.left.b0, x.left.b1,
    x.left.b2 + x.left.b3]

/-- The binary rank-four quotient map on the parity kernel. -/
@[expose] public def parityProjection : ParityKernel →* ParityQuotient where
  toFun x := parityCoordinates x
  map_one' := by ext i; fin_cases i <;> rfl
  map_mul' x y := by
    have hx := (mem_parityKernel x).mp x.property
    have hy := (mem_parityKernel y).mp y.property
    have hact := congrArg Multiplicative.toAdd (parityCoreCoordinates_action x.val.right hx y.val.left)
    have h0 := congrFun hact 0
    have h1 := congrFun hact 1
    have h2 := congrFun hact 2
    change (![_, _, _, _] : Fin 4 → ZMod 2) = _ + _
    funext i
    fin_cases i
    · exact (by decide : ∀ t s : FiveFour.Cyclic 4, parity t = 1 → parity s = 1 →
        (((t * s).toAdd.val / 2 : ℕ) : ZMod 2) =
          (t.toAdd.val / 2 : ℕ) + (s.toAdd.val / 2 : ℕ)) x.val.right y.val.right hx hy
    · change x.val.left.b0 + _ = x.val.left.b0 + y.val.left.b0
      exact congrArg (x.val.left.b0 + ·) h0
    · change x.val.left.b1 + _ = x.val.left.b1 + y.val.left.b1
      exact congrArg (x.val.left.b1 + ·) h1
    · change (x.val.left.b2 + _) + (x.val.left.b3 + _) =
        (x.val.left.b2 + x.val.left.b3) + (y.val.left.b2 + y.val.left.b3)
      calc
        _ = (x.val.left.b2 + x.val.left.b3) +
            ((Core.complementAction (SemidirectProduct.inr x.val.right) y.val.left).b2 +
              (Core.complementAction (SemidirectProduct.inr x.val.right) y.val.left).b3) := by simp only [MonoidHom.comp_apply]; ring
        _ = _ := congrArg ((x.val.left.b2 + x.val.left.b3) + ·) h2

/-- Seven independent coordinates within each quotient fiber. -/
@[expose] public def parityElement (v : ParityQuotient) (w : Fin 7 → ZMod 2) : ParityKernel :=
  ⟨⟨⟨v.toAdd 1, v.toAdd 2, v.toAdd 3 + w 0, w 0,
      w 1, w 2, w 3, w 4, w 5, w 6⟩,
      Multiplicative.ofAdd (2 * (v.toAdd 0).val)⟩,
    (mem_parityKernel _).mpr ((by decide : ∀ b : ZMod 2,
      parity (Multiplicative.ofAdd (2 * b.val)) = 1) (v.toAdd 0))⟩

/-- The explicit fiber element has the specified quotient coordinate. -/
public theorem parityProjection_element (v : ParityQuotient) (w : Fin 7 → ZMod 2) :
    parityProjection (parityElement v w) = v := by
  change (![_, _, _, _] : Fin 4 → ZMod 2) = v.toAdd
  funext i
  fin_cases i
  · exact (by decide : ∀ b : ZMod 2, (((2 * b.val : ZMod 4).val / 2 : ℕ) : ZMod 2) = b) _
  · rfl
  · rfl
  · change (v.toAdd 3 + w 0) + w 0 = v.toAdd 3
    simp [add_assoc, ← two_mul, show (2 : ZMod 2) = 0 by decide]

/-- All sixteen quotient values occur. -/
public theorem parityProjection_surjective : Function.Surjective parityProjection :=
  fun v => ⟨parityElement v 0, parityProjection_element v 0⟩

/-- The seven free coordinates in a fiber of `parityProjection`. -/
@[expose] public def parityRemainder (x : ParityKernel) : Fin 7 → ZMod 2 :=
  ![x.val.left.b3, x.val.left.b4, x.val.left.b5, x.val.left.b6,
    x.val.left.b7, x.val.left.b8, x.val.left.b9]

/-- The quotient and remainder coordinates reconstruct every kernel element. -/
public theorem parityElement_coordinates (x : ParityKernel) :
    parityElement (parityProjection x) (parityRemainder x) = x := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · apply Core.ext
    all_goals first | rfl | skip
    change (x.val.left.b2 + x.val.left.b3) + x.val.left.b3 = x.val.left.b2
    simp [add_assoc, ← two_mul, show (2 : ZMod 2) = 0 by decide]
  · exact (by decide : ∀ t : FiveFour.Cyclic 4, parity t = 1 →
      Multiplicative.ofAdd (2 * ((((t.toAdd.val / 2 : ℕ) : ZMod 2).val) : ZMod 4)) = t)
      x.val.right ((mem_parityKernel x).mp x.property)

/-- Every quotient fiber is parametrized by seven independent bits. -/
@[expose] public def parityFiberEquiv (v : ParityQuotient) :
    {x : ParityKernel // parityProjection x = v} ≃ (Fin 7 → ZMod 2) where
  toFun x := parityRemainder x.val
  invFun w := ⟨parityElement v w, parityProjection_element v w⟩
  left_inv x := by
    apply Subtype.ext
    change parityElement v (parityRemainder x.val) = x.val
    simpa only [x.property] using parityElement_coordinates x.val
  right_inv w := by funext i; fin_cases i <;> rfl

/-- The kernel of the explicit quotient map has order 128. -/
public theorem parityProjection_ker_card : Nat.card parityProjection.ker = 128 := by
  change Nat.card {x : ParityKernel // parityProjection x = 1} = 128
  rw [Nat.card_congr (parityFiberEquiv 1), Nat.card_fun]
  simp

/-- Power-equation solutions correspond to seven-bit coordinate solutions. -/
@[expose] public def parityPowerFiberEquiv (v : ParityQuotient) (n : ℕ) :
    {x : ParityKernel // parityProjection x = v ∧ x ^ n = 1} ≃
      {w : Fin 7 → ZMod 2 // parityElement v w ^ n = 1} where
  toFun x := ⟨parityRemainder x.val, by
    have h : parityElement v (parityRemainder x.val) = x.val := by
      simpa only [x.property.1] using parityElement_coordinates x.val
    rw [h]
    exact x.property.2⟩
  invFun w := ⟨parityElement v w.val, parityProjection_element v w.val, w.property⟩
  left_inv x := by
    apply Subtype.ext
    change parityElement v (parityRemainder x.val) = x.val
    simpa only [x.property.1] using parityElement_coordinates x.val
  right_inv w := by
    apply Subtype.ext
    funext i; fin_cases i <;> rfl

/-- Power-fiber counts reduce to the seven free binary coordinates. -/
public theorem parityProjection_powerFiberCard (v : ParityQuotient) (n : ℕ) :
    parityProjection.powerFiberCard v n =
      Nat.card {w : Fin 7 → ZMod 2 // parityElement v w ^ n = 1} :=
  Nat.card_congr (parityPowerFiberEquiv v n)

/-- A core root regarded as an element of the parity kernel. -/
@[expose] public def parityRoot (i : CoreRoot) : ParityKernel :=
  ⟨root i, (mem_parityKernel _).mpr rfl⟩

/-- The square of root one in the parity kernel. -/
@[expose] public def parityRootOneSquare : ParityKernel :=
  ⟨rootOne ^ 2, by decide +kernel⟩

/-- The ordered lifts rootOne², root 0, root 1, root 2. -/
@[expose] public def parityBasisLift (i : Fin 4) : ParityKernel :=
  ![parityRootOneSquare, parityRoot 0, parityRoot 1, parityRoot 2] i

/-- The ordered lifts map to the standard basis in the profile convention. -/
public theorem parityProjection_basis : ∀ i : Fin 4,
    parityProjection (parityBasisLift i) =
      Multiplicative.ofAdd (fun j => if j = i then 1 else 0) := by decide +kernel

/-- The projection kernel has trivial complement and the indicated leading coordinates. -/
public theorem mem_parityProjection_ker (x : ParityKernel) :
    x ∈ parityProjection.ker ↔ x.val.right = 1 ∧ x.val.left.b0 = 0 ∧
      x.val.left.b1 = 0 ∧ x.val.left.b2 = x.val.left.b3 := by
  change parityProjection x = 1 ↔ _
  constructor
  · intro h
    have h0 := congrArg (fun v : ParityQuotient => v.toAdd 0) h
    have h1 := congrArg (fun v : ParityQuotient => v.toAdd 1) h
    have h2 := congrArg (fun v : ParityQuotient => v.toAdd 2) h
    have h3 := congrArg (fun v : ParityQuotient => v.toAdd 3) h
    refine ⟨?_, h1, h2, ?_⟩
    · exact (by decide : ∀ t : FiveFour.Cyclic 4, parity t = 1 →
        ((t.toAdd.val / 2 : ℕ) : ZMod 2) = 0 → t = 1)
        x.val.right ((mem_parityKernel x).mp x.property) h0
    · exact (by decide : ∀ a b : ZMod 2, a + b = 0 → a = b) _ _ h3
  · rintro ⟨hr, h0, h1, h23⟩
    change (![_, _, _, _] : Fin 4 → ZMod 2) = 0
    funext i
    fin_cases i
    · change ((x.val.right.toAdd.val / 2 : ℕ) : ZMod 2) = 0
      rw [hr]
      rfl
    · exact h0
    · exact h1
    · change x.val.left.b2 + x.val.left.b3 = 0
      rw [h23]
      exact (by decide : ∀ b : ZMod 2, b + b = 0) _

end ReeTwo.SylowModel
