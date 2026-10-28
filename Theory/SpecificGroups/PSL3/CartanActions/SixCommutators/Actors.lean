module

public import Theory.SpecificGroups.PSL3.CartanActions

/-!
# Concrete linear, field and graph factors for the degree-six calculation

The graph representative is inverse transpose followed by coordinate reversal,
so it preserves the upper unitriangular subgroup. The displayed standard actors
include the full GL₃ conjugation factor, including inner and diagonal factors.
The two coverage propositions are raw automorphism-classification inputs; they
assert neither triangularity of that factor nor any action on a Borel quotient.

Source: GLS3, Theorem 2.5.12 and §2.7, `refs/KGroup/GLS3/chapter2.tex`, especially
the matrix description of A₂ automorphisms. Application: Aschbacher–Smith,
proof of 13.8.20, printed p.954. Coverage is left explicit as an earlier input.
-/

@[expose] public section

open scoped MatrixGroups
open Matrix Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
namespace Matrix.PSL3.CartanActions.SixCommutators
variable (F : Type*) [Field F]

/-- The upper-unipotent-preserving graph representative on SL₃. -/
def oppositionGraphSL : MulAut SL(3,F) :=
  linearConjSL F (reversalGL F) * graphSL F

/-- The actual standard actor on SL₃, with its entire linear factor retained. -/
def specialActor (m : GL (Fin 3) F) (σ : F ≃+* F) (graphPart : Bool) :
    MulAut SL(3,F) :=
  linearConjSL F m * Atlas.fieldEquivSL 3 σ *
    (if graphPart then oppositionGraphSL F else 1)

/-- The actual standard actor on PSL₃, acting on the specified central quotient. -/
def projectiveActor (m : GL (Fin 3) F) (σ : F ≃+* F) (graphPart : Bool) :
    MulAut PSL(3,F) :=
  linearConj F m * fieldAction F σ *
    (if graphPart then oppositionGraph F else 1)

/-- Raw standard-automorphism coverage on SL₃. No local-action conclusion is included. -/
def SpecialCoverage : Prop :=
  ∀ α : MulAut SL(3,F), ∃ (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool),
    α = specialActor F m σ ε

/-- Raw standard-automorphism coverage on PSL₃. No local-action conclusion is included. -/
def ProjectiveCoverage : Prop :=
  ∀ α : MulAut PSL(3,F), ∃ (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool),
    α = projectiveActor F m σ ε

theorem field_torusSL (σ : F ≃+* F) (d : Fˣ × Fˣ) :
    Atlas.fieldEquivSL 3 σ (torusSL F d) =
      torusSL F (Units.map σ.toMonoidHom d.1, Units.map σ.toMonoidHom d.2) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Atlas.fieldEquivSL, SpecialLinearGroup.map_apply_coe, torusSL_val]

theorem oppositionGraphSL_torusSL (d : Fˣ × Fˣ) :
    oppositionGraphSL F (torusSL F d) = torusSL F (d.2⁻¹,d.1⁻¹) := by
  change linearConjSL F (reversalGL F) (graphSL F (torusSL F d)) = _
  rw [graphSL_torusSL, linearConjSL_reversal_torusSL]
  rfl

end Matrix.PSL3.CartanActions.SixCommutators
