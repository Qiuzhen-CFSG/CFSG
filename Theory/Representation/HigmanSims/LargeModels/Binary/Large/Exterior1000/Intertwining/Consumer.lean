module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000

/-!
# Application of packed products to the original marked-action consumer

The unconditional intertwining identities discharge exactly the generator
premises of `markedAction_of_certificates`. The independent pivot identity
remains explicit; the original application from product families is retained.
Keeping this application outside the Intertwining import closure lets the parent
Exterior1000 module import its unconditional matrix identities without
an import cycle. Source: ATLAS HSG1-f2r56B0/HSG1-f2r1000B0 and
`Binary/source/section1000.json`; attribution is in `Binary/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining

/-- The actual source consumer, with only the two finite product families and
independent pivot certificate still explicit. -/
theorem markedAction_of_packed_products (C56 : MarkedAction 0)
    (ha : ∀ i : Fin 1000, Tables.a.product liftRows[i.val]! =
      Tables.lifts.product D1000.aRows[i.val]!)
    (hb : ∀ i : Fin 1000, Tables.b.product liftRows[i.val]! =
      Tables.lifts.product D1000.bRows[i.val]!)
    (hR : pivotMinor * pivotInverse = 1) : Nonempty (MarkedAction 3) :=
  markedAction_of_certificates C56 (matrixA_of_products ha) (matrixB_of_products hb) hR

/-- Both generator premises of the actual descent consumer are discharged.
The independent rank certificate remains with the exterior1000 assembly owner. -/
theorem markedAction_of_pivot_certificate (C56 : MarkedAction 0)
    (hR : pivotMinor * pivotInverse = 1) : Nonempty (MarkedAction 3) :=
  markedAction_of_certificates C56 u_mul_ambientA u_mul_ambientB hR

end Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining
