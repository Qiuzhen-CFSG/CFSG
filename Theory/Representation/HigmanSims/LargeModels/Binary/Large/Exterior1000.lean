module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Ambient
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Surjectivity
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Rank
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Descent

/-!
# Degree-1000 HS descent from the literal exterior-square(56) action

The ambient action is the actual exterior functor on the supplied marked
56-dimensional action, in the ordered 1540-dimensional coordinates. Its two
matrices are proved in `Ambient`. The fixed lifted rows and pivot inverse are
in `Data`. The generator identities in `Intertwining` and the pivot inverse
identity in `Rank` supply invariance and surjectivity. `Descent` transports the
quotient by `ker U` to the literal target coordinates. This is the dual of the
invariant right row construction and retains the raw left target matrices.

`markedAction` discharges all numerical premises of the retained conditional
assembly. Its only input is the marked degree-56 action. Absolute irreducibility
is a separate matrix-algebra calculation.

Source: R. A. Wilson et al., ATLAS HSG1-f2r56B0/HSG1-f2r1000B0 and the
exterior-section candidate documented in `Binary/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000

/-- The actual exterior action feeds the literal invariant-row descent theorem.
The remaining premises are exactly the two generator identities and the checked
pivot-minor inverse, with the fixed candidate rows. -/
theorem markedAction_of_certificates (C56 : MarkedAction 0)
    (ha : U * ambientA = targetA * U)
    (hb : U * ambientB = targetB * U)
    (hR : pivotMinor * pivotInverse = 1) : Nonempty (MarkedAction 3) := by
  apply Descent.markedAction_of_invariantRows 3 1540 (ambientAction C56) U
  · rw [ambientAction_a]
    exact ha
  · rw [ambientAction_b]
    exact hb
  · exact surjective_of_pivot_certificate hR

/-- The marked degree-1000 HS action obtained from the actual exterior square
of the marked degree-56 action, with every section certificate proved. -/
theorem markedAction (C56 : MarkedAction 0) : Nonempty (MarkedAction 3) :=
  markedAction_of_certificates C56 u_mul_ambientA u_mul_ambientB
    pivotMinor_mul_pivotInverse

end Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000
