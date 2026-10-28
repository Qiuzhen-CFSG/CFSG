module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.Bounds
public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.FixedPlane

/-!
# Certificates for the index of the O'Nan local subgroup

A projective coset cover and a sufficiently large orbit of an object fixed by
the two local generators certify the index independently of subgroup order.
`FixedPlane` supplies a kernel-checked eight-dimensional row-space witness for
such an object. The two numerical certificates are still separate obligations:
no orbit enumeration or coset-cover equality is assumed without a proof.

See `ProjectiveOrder/Setup.lean` for the source of the subgroup words and
`CosetIndex/FixedPlane.lean` for the matrix witness and its source.
-/

namespace ONan.OrderCertificate

/-- Combine independent cover and fixed-object certificates for the exact index. -/
public theorem localSubgroup_index_of_cover_of_action
    (C : Subgroup.GeneratorCosetCover localSubgroup cosetGenerators (Fin 122760))
    {X : Type*} [MulAction Model X] (x : X)
    (ha : localA • x = x) (hb : localB • x = x)
    (repr : Fin 122760 → Model)
    (hinj : Function.Injective (fun i => repr i • x)) :
    localSubgroup.index = 122760 :=
  Nat.le_antisymm (localSubgroup_index_le_of_cover C)
    (localSubgroup_index_ge_of_action x ha hb repr hinj)

end ONan.OrderCertificate
