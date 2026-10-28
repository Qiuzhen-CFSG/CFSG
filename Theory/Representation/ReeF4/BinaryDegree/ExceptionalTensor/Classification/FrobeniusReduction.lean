module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicWeights
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.CyclicOrder
public import Theory.Representation.IrreducibleTraceEquivalence

/-!
# Character periods from exceptional tensor parameters

The actual factors are indexed by the odd cyclic group of order `2*k+1`.
Ordinary coefficient Frobenius shifts the exponents of the exceptional
endomorphism by two; the factor arriving at index `i` therefore came from
`i-2*r`. Assuming that compatibility and the genuine restriction and uniqueness
theorems, equality of irreducible characters gives an intertwining equivalence.
Parameter uniqueness then identifies the algebraic factors and their dimensions.
The shift by `2*k+1` is the identity and gives the full character period.

`HasBasicHighestWeight` names the specified weight in the existing basicness
predicate so that the separate algebraic-uniqueness and coefficient-Frobenius
proofs can share an exact contract. No representation classification is assumed
as a structure or asserted unconditionally here.

Source: GLS3, Corollary 2.8.6(b) and Remark 2.8.8. The trace-to-equivalence
theorem used here is valid in characteristic two.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] {k : ℕ}

/-- A specified exceptional basic highest weight, for the actual root and coroot actions. -/
@[expose] def HasBasicHighestWeight (B : AlgebraicFactor F) (weight : Fin 2 × Fin 2) : Prop :=
  ∃ v : B.Space, v ≠ 0 ∧
    (∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → ∀ t : F,
      (B.action.action (algebraicRootElement r t) : Module.End F B.Space) v = v) ∧
    (∀ (i : Fin 4) (t : Fˣ),
      (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
        Module.End F B.Space) v = ((t : F) ^ basicCoefficient weight i) • v)

/-- Relating a specified weight to the existing basicness interface. -/
theorem isExceptionalBasic_iff (B : AlgebraicFactor F) :
    B.IsExceptionalBasic ↔ ∃ weight, HasBasicHighestWeight B weight := Iff.rfl

/-- After r ordinary Frobenius steps the factor at i came from i - 2*r. -/
@[expose] def shiftFactors (B : ZMod (2 * k + 1) → AlgebraicFactor F) (r : ℕ) :
    ZMod (2 * k + 1) → AlgebraicFactor F :=
  fun i => B (i - 2 * (r : ZMod (2 * k + 1)))

@[simp] theorem shiftFactors_fieldPeriod (B : ZMod (2 * k + 1) → AlgebraicFactor F) :
    shiftFactors B (2 * k + 1) = B := by
  funext i
  simp [shiftFactors]

/-- Coefficient Frobenius and uniqueness of the restricted tensor parameters
convert a fixed character into equality of the corresponding factor dimensions.
The representation-theoretic premises remain explicit. -/
theorem character_fixed_and_factor_period_of_shift
    (ι : SplitGroup k →* Variety.Point (F4Chevalley.Carrier (k := F)))
    (hirr : ∀ B : ZMod (2 * k + 1) → AlgebraicFactor F,
      (∀ i, (B i).IsExceptionalBasic) → Representation.IsIrreducible (exceptionalTensor ι B).ρ)
    (hunique : ∀ B C : ZMod (2 * k + 1) → AlgebraicFactor F,
      (∀ i, (B i).IsExceptionalBasic) → (∀ i, (C i).IsExceptionalBasic) →
      Nonempty (Representation.Equiv (exceptionalTensor ι B).ρ (exceptionalTensor ι C).ρ) →
      ∀ i, AreEquivalentRepresentations (B i).action (C i).action)
    (B : ZMod (2 * k + 1) → AlgebraicFactor F)
    (hbasic : ∀ i, (B i).IsExceptionalBasic)
    (hFrob : ∀ (r : ℕ) (g : Model k),
      (Representation.character (exceptionalTensor ι B).ρ) g ^ (2 ^ r) =
        (Representation.character (exceptionalTensor ι (shiftFactors B r)).ρ) g) :
    (∀ g, (Representation.character (exceptionalTensor ι B).ρ) g ^ (2 ^ (2 * k + 1)) =
      (Representation.character (exceptionalTensor ι B).ρ) g) ∧
    (∀ r : ℕ, (∀ g, (Representation.character (exceptionalTensor ι B).ρ) g ^ (2 ^ r) =
      (Representation.character (exceptionalTensor ι B).ρ) g) →
      ∀ i, Module.finrank F (B (i + 2 * (r : ZMod (2 * k + 1)))).Space =
        Module.finrank F (B i).Space) := by
  constructor
  · intro g
    exact (hFrob (2 * k + 1) g).trans
      (congrArg (fun C => Representation.character (exceptionalTensor ι C).ρ g)
        (shiftFactors_fieldPeriod B))
  · intro r hr i
    have hshiftbasic : ∀ j, ((shiftFactors B r) j).IsExceptionalBasic := fun j => hbasic _
    let _ := hirr B hbasic
    let _ := hirr (shiftFactors B r) hshiftbasic
    have heq : (Representation.character (exceptionalTensor ι B).ρ) =
        (Representation.character (exceptionalTensor ι (shiftFactors B r)).ρ) := by
      funext g
      exact (hr g).symm.trans (hFrob r g)
    have he := (Representation.character_eq_iff_equiv_of_irreducible
      (exceptionalTensor ι B).ρ (exceptionalTensor ι (shiftFactors B r)).ρ).mp heq
    obtain ⟨e, _⟩ := hunique B (shiftFactors B r) hbasic hshiftbasic he
      (i + 2 * (r : ZMod (2 * k + 1)))
    exact e.finrank_eq.trans
      (congrArg (fun j => Module.finrank F (B j).Space) (add_sub_cancel_right i _))

end ReeF4.BinaryDegree.ExceptionalTensor.Classification
