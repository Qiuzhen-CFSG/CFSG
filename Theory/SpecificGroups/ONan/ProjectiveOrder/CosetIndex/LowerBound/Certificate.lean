module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.LowerBound.Certificate.PackedData

/-!
# Assembly of the concrete fixed-plane tree certificate

The common packed-data interface separates the numerical edge checks from the
checks of reduced bases and matrix distinctness. The constructor below converts
these exact obligations into the spanning-tree contract. The unconditional
`fixedPlaneOrbitTree` still requires the concrete data and its numerical proofs.
See `LowerBound/source/README.md` for the untrusted producer and provenance.
-/

@[expose] public section

namespace ONan.OrderCertificate

/-- Assemble checked packed data into the fixed-plane orbit tree.
The edge hypotheses are identities in the original 45-dimensional matrix model. -/
def PackedOrbitData.toTree (D : PackedOrbitData)
    (root : D.rows 0 = fixedPlaneRows)
    (parent_lt : ∀ i, i ≠ 0 → D.parent i < i)
    (edge : ∀ i, i ≠ 0 → D.rows (D.parent i) *
      (linearCosetGenerator (D.letter i) : Matrix (Fin 45) (Fin 45) (ZMod 7)) =
        D.coefficient i * D.rows i)
    (reduced : ∀ i, Matrix.IsReducedRowBasis (D.rows i) (D.pivot i))
    (distinct : Function.Injective D.rows) : FixedPlaneOrbitTree where
  rows := D.rows
  root_rows := root
  parent := D.parent
  parent_lt := parent_lt
  letter := D.letter
  coefficient := D.coefficient
  edge := edge
  independent := D.independent reduced
  distinct := D.distinct reduced distinct

end ONan.OrderCertificate
