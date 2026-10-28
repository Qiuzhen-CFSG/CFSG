module

public import Theory.PGL2.Defs

/-!
# Field transport for the actual projective general linear group

The matrix-entry ring maps descend through scalar matrices. Applying inverse
field maps gives the corresponding group equivalence, retaining the concrete
projective general linear carrier.
-/

public section
namespace Matrix.ProjGenLinGroup
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Entrywise field transport on the projective general linear group. -/
def mapEquiv (e : R ≃+* S) : ProjGenLinGroup n R ≃* ProjGenLinGroup n S where
  toFun := map e.toRingHom
  invFun := map e.symm.toRingHom
  left_inv x := by
    change ((map e.symm.toRingHom).comp (map e.toRingHom)) x = x
    rw [← map_comp]
    simp
  right_inv x := by
    change ((map e.toRingHom).comp (map e.symm.toRingHom)) x = x
    rw [← map_comp]
    simp
  map_mul' := (map e.toRingHom).map_mul

end Matrix.ProjGenLinGroup
