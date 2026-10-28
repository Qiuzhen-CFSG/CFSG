module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityProfiles

/-!
# Coordinate functions for the eight rank-four parity candidates

The four coordinates use the binary core coordinates and the low and high
bits of the cyclic-four coordinate. Row 7 requires the quadratic correction
`b₆ t₁`. The chosen root words belong to the exact generator closures and
give a section of each coordinate function, proving surjectivity.

This module does not assert that the functions preserve multiplication or
that their identity fibers are Frattini subgroups. Those are separate
obligations, as are the intrinsic profile counts.

Source: the verified root multiplication of Shinoda (1975), (2.3),
pp. 81–82, in `Core`, `RootAction`, and `Sylow`. The basis order is the one
specified in `SmallParityProfiles`; all section identities are kernel checked.
-/

namespace ReeTwo.SylowModel
set_option maxRecDepth 16384

/-- Read the proposed quotient coordinates on the ambient Sylow group. -/
@[expose] public def smallParityFourCoordinates (i : Fin 8) (x : SylowModel) :
    SmallParityFourQuotient :=
  let b := x.left
  let t₀ : ZMod 2 := x.right.toAdd.val
  let t₁ : ZMod 2 := (x.right.toAdd.val / 2 : ℕ)
  Multiplicative.ofAdd
    ((![![b.b2 + b.b3, t₀, b.b2, b.b6],
        ![b.b2 + b.b3, t₀, b.b2, b.b6 + t₀ + t₁],
        ![b.b2, t₀, b.b5, b.b2 + b.b4],
        ![b.b2 + b.b5, t₀, b.b5, b.b2 + b.b4 + b.b6],
        ![b.b2, t₀, b.b6, b.b2 + b.b4],
        ![b.b2, t₀, b.b6 + t₀ + t₁, b.b2 + b.b4],
        ![b.b3, t₀, b.b7, b.b7 + b.b9],
        ![b.b2, t₀, b.b2 + b.b4, b.b7 + b.b6 * t₁]]) i)

/-- Root-word lifts in the precise basis convention of the profile tables. -/
@[expose] public def smallParityFourBasis (i : Fin 8) : Fin 4 → SylowModel :=
  (![![root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 7,
          root 6 * root 7 * root 8],
      ![root 3, rootOne ^ 3 * root 5 * root 8,
          root 2 * root 3 * root 4 * root 7, rootOne ^ 2],
      ![root 2 * root 4 * root 8, rootOne ^ 3, root 5 * root 8, root 4],
      ![root 2 * root 4 * root 8, rootOne ^ 3,
          root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, root 4],
      ![root 2 * root 4 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, root 4],
      ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8,
          root 6 * root 7 * root 8, root 4 * root 9],
      ![root 3, rootOne ^ 3, root 7 * root 8 * root 9, root 9],
      ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8,
          root 4 * root 9, root 7]]) i

/-- Every basis lift belongs to the original subgroup, without any order assumption. -/
public theorem smallParityFourBasis_mem (i : Fin 8) (j : Fin 4) :
    smallParityFourBasis i j ∈ smallParityTwoCandidate (smallParityFourIndex i) := by
  fin_cases i <;> fin_cases j <;> apply Subgroup.subset_closure
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-- The selected lifts have the required quotient labels. -/
public theorem smallParityFourCoordinates_basis : ∀ (i : Fin 8) (j : Fin 4),
    smallParityFourCoordinates i (smallParityFourBasis i j) =
      Multiplicative.ofAdd (fun k => if k = j then 1 else 0) := by decide +kernel

/-- A word realizing a prescribed binary quotient value. -/
@[expose] public def smallParityFourSection (i : Fin 8) (v : SmallParityFourQuotient) :
    SylowModel :=
  smallParityFourBasis i 0 ^ (v.toAdd 0).val *
    smallParityFourBasis i 1 ^ (v.toAdd 1).val *
    smallParityFourBasis i 2 ^ (v.toAdd 2).val *
    smallParityFourBasis i 3 ^ (v.toAdd 3).val

/-- The section words lie in the exact candidate closures. -/
public theorem smallParityFourSection_mem (i : Fin 8) (v : SmallParityFourQuotient) :
    smallParityFourSection i v ∈ smallParityTwoCandidate (smallParityFourIndex i) := by
  unfold smallParityFourSection
  repeat apply Subgroup.mul_mem
  all_goals exact Subgroup.pow_mem _ (smallParityFourBasis_mem i _) _

/-- All sixteen coordinate values occur, checked using the verified root multiplication. -/
public theorem smallParityFourCoordinates_section : ∀ (i : Fin 8)
    (v : SmallParityFourQuotient),
    smallParityFourCoordinates i (smallParityFourSection i v) = v := by decide +kernel

/-- The coordinate function restricted to the original candidate. -/
@[expose] public def smallParityFourMap (i : Fin 8)
    (x : smallParityTwoCandidate (smallParityFourIndex i)) : SmallParityFourQuotient :=
  smallParityFourCoordinates i x.val

/-- Surjectivity does not require an external subgroup-order calculation. -/
public theorem smallParityFourMap_surjective (i : Fin 8) :
    Function.Surjective (smallParityFourMap i) := by
  intro v
  exact ⟨⟨smallParityFourSection i v, smallParityFourSection_mem i v⟩,
    smallParityFourCoordinates_section i v⟩

/-- Proposed decidable carrier equations; identification with the generator closures
is a separate algebraic certificate. -/
@[expose] public def smallParityFourCarrier (i : Fin 8) (x : SylowModel) : Prop :=
  let b := x.left
  let t₀ : ZMod 2 := x.right.toAdd.val
  let t₁ : ZMod 2 := (x.right.toAdd.val / 2 : ℕ)
  b.b0 = 0 ∧ b.b1 = 0 ∧
    ((![b.b5 = 0,
        b.b5 = t₀,
        b.b3 = 0,
        b.b3 = b.b5,
        b.b3 = 0 ∧ b.b5 = 0,
        b.b3 = 0 ∧ b.b5 = t₀,
        b.b2 = 0 ∧ b.b5 = 0 ∧ b.b6 = 0,
        b.b3 = 0 ∧ b.b5 = t₀ ∧ b.b5 + b.b6 + t₁ = 0]) i)

/-- Intrinsic counts for the fixed coordinate functions, before multiplicativity is proved. -/
@[expose] public noncomputable def smallParityFourCoordinateProfile (i : Fin 8)
    (v : SmallParityFourQuotient) : ℕ × ℕ × ℕ :=
  (Nat.card {x : smallParityTwoCandidate (smallParityFourIndex i) //
      smallParityFourMap i x = v ∧ MulAut.orderCentralizerTest (smallParityFourTests i 0) x},
    Nat.card {x : smallParityTwoCandidate (smallParityFourIndex i) //
      smallParityFourMap i x = v ∧ MulAut.orderCentralizerTest (smallParityFourTests i 1) x},
    Nat.card {x : smallParityTwoCandidate (smallParityFourIndex i) //
      smallParityFourMap i x = v ∧ MulAut.orderCentralizerTest (smallParityFourTests i 2) x})

end ReeTwo.SylowModel
