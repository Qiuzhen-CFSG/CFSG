module

public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport
public import Theory.SpecificGroups.SymplecticFour.Binary.PointModel
public import Theory.SpecificGroups.SymplecticFour.Binary.PlaneModel
public import Theory.SpecificGroups.SymplecticFour.LocalFactors

/-!
# Binary symplectic local products

The required local product is `Perm (Fin 2) × Perm (Fin 4)`, namely
`C₂ × S₄`. An identification of a concrete parabolic over `ZMod 2` extends
to every field of order two using entrywise field transport. The already
proved determinant-kernel equalities then identify the actual local factors.

The concrete binary models are constructed in `PointModel` and `PlaneModel`:
the former uses coordinate permutations and a central transvection after a
change of symplectic basis; the latter uses affine permutations of the four
vectors in the isotropic plane and a central binary coordinate. Both maps
are proved multiplicative and bijective onto the actual matrix stabilizers.
The unconditional equivalences below assemble these models with field transport.

Source: the binary local products in Aschbacher--Smith F.1.12(I)(2), printed
pp.262--264. For the source's groups `LᵢS`, the CFSG assembly uses the proved
`pointLocal_sup_of_card_two` and `planeLocal_sup_of_card_two` in the CFSG
symplectic-four amalgam module; the local factors and those joins are not
identified by definition.
-/

@[expose] public section
noncomputable section

namespace Theory.SpecificGroups.SymplecticFour.Binary

/-- The product `C₂ × S₄`, using the two-letter symmetric group for `C₂`. -/
abbrev LocalProduct := Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4)

variable {F : Type*} [Field F] [Finite F]

/-- Extend an actual binary point-parabolic model to any field of order two. -/
def pointParabolicEquivProdOfZMod (hF : Nat.card F = 2)
    (e₂ : pointParabolic (F := ZMod 2) ≃* LocalProduct) :
    pointParabolic (F := F) ≃* LocalProduct :=
  (pointParabolicEquivZModTwo hF).trans e₂

/-- Extend an actual binary plane-parabolic model to any field of order two. -/
def planeParabolicEquivProdOfZMod (hF : Nat.card F = 2)
    (e₂ : planeParabolic (F := ZMod 2) ≃* LocalProduct) :
    planeParabolic (F := F) ≃* LocalProduct :=
  (planeParabolicEquivZModTwo hF).trans e₂

/-- The point local factor, using its proved equality with the binary parabolic. -/
def pointLocalEquivProdOfZMod (hF : Nat.card F = 2)
    (e₂ : pointParabolic (F := ZMod 2) ≃* LocalProduct) :
    pointLocal (F := F) ≃* LocalProduct :=
  (MulEquiv.subgroupCongr (pointLocal_eq_of_card_two hF)).trans
    (pointParabolicEquivProdOfZMod hF e₂)

/-- The plane local factor, using its proved equality with the binary parabolic. -/
def planeLocalEquivProdOfZMod (hF : Nat.card F = 2)
    (e₂ : planeParabolic (F := ZMod 2) ≃* LocalProduct) :
    planeLocal (F := F) ≃* LocalProduct :=
  (MulEquiv.subgroupCongr (planeLocal_eq_of_card_two hF)).trans
    (planeParabolicEquivProdOfZMod hF e₂)

/-- The actual point parabolic over any field of order two is `C₂ × S₄`. -/
def pointParabolicEquivProd (hF : Nat.card F = 2) :
    pointParabolic (F := F) ≃* LocalProduct :=
  pointParabolicEquivProdOfZMod hF pointParabolicZModEquivProd

/-- The actual plane parabolic over any field of order two is `C₂ × S₄`. -/
def planeParabolicEquivProd (hF : Nat.card F = 2) :
    planeParabolic (F := F) ≃* LocalProduct :=
  planeParabolicEquivProdOfZMod hF planeParabolicZModEquivProd

/-- The point determinant kernel over a binary field, transported along its
proved equality with the point parabolic. -/
def pointLocalEquivProd (hF : Nat.card F = 2) :
    pointLocal (F := F) ≃* LocalProduct :=
  pointLocalEquivProdOfZMod hF pointParabolicZModEquivProd

/-- The plane determinant kernel over a binary field, transported along its
proved equality with the plane parabolic. -/
def planeLocalEquivProd (hF : Nat.card F = 2) :
    planeLocal (F := F) ≃* LocalProduct :=
  planeLocalEquivProdOfZMod hF planeParabolicZModEquivProd

end Theory.SpecificGroups.SymplecticFour.Binary
