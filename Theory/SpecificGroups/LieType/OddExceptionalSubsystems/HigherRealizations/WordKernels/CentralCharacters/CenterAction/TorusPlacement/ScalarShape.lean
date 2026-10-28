module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ResidueDiagonal
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.FixedRows

/-!
# Assembly of the scalar shape from diagonal root entries

The Cartan entries of a diagonal central evaluated word are already one by
`ScalarShape.FixedRows`. Consequently the remaining root-entry identities
assemble to equality with the literal residue diagonal, in both E7 and E8.

The two inputs still requiring proof are diagonality of each central word
and the common residue parameter on its root entries. Both remain explicit
here. In particular these conditional applications do not establish the
unconditional scalar-shape theorem, and they assume no cubic constraint.

Sources: GLS3 §§1.12.5–6 and 2.6.2, and the subsystem embeddings used in
Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
noncomputable section

namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement

open ScalarShape
attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

/-- Cartan normalization completes the E7 scalar shape from diagonal root entries. -/
theorem e7Six_eq_residueDiagonal_of_root_entries (F : Type*) [Field F]
    (hodd : Odd (ringChar F)) (w : SixNodeWord F)
    (hc : ∀ z, Commute (e7Six F w) (e7Six F z))
    (hd : (e7Six F w).val.val.IsDiag) (u : Fˣ)
    (hr : ∀ r : typeE7Roots, (e7Six F w).val.val (Sum.inr r) (Sum.inr r) =
      ((u ^ balancedResidue (centralExponent e7Node (Sum.inr r)) : Fˣ) : F)) :
    (e7Six F w).val = residueDiagonal F e7Node u := by
  apply Units.ext
  rw [← hd.diagonal_diag]
  change Matrix.diagonal _ = Matrix.diagonal _
  congr 1
  funext a
  cases a with
  | inl k =>
    simp only [Matrix.diag_apply, e7Six_diagonal_cartan_eq_one F hodd w hc hd k,
      centralExponent, chevalleyBasisWeight]
    norm_num [balancedResidue]
  | inr r => exact hr r

/-- Cartan normalization completes the E8 scalar shape from diagonal root entries. -/
theorem e8Six_eq_residueDiagonal_of_root_entries (F : Type*) [Field F]
    (hodd : Odd (ringChar F)) (w : SixNodeWord F)
    (hc : ∀ z, Commute (e8Six F w) (e8Six F z))
    (hd : (e8Six F w).val.val.IsDiag) (u : Fˣ)
    (hr : ∀ r : typeE8Roots, (e8Six F w).val.val (Sum.inr r) (Sum.inr r) =
      ((u ^ balancedResidue (centralExponent e8Node (Sum.inr r)) : Fˣ) : F)) :
    (e8Six F w).val = residueDiagonal F e8Node u := by
  apply Units.ext
  rw [← hd.diagonal_diag]
  change Matrix.diagonal _ = Matrix.diagonal _
  congr 1
  funext a
  cases a with
  | inl k =>
    simp only [Matrix.diag_apply, e8Six_diagonal_cartan_eq_one F hodd w hc hd k,
      centralExponent, chevalleyBasisWeight]
    norm_num [balancedResidue]
  | inr r => exact hr r

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement
