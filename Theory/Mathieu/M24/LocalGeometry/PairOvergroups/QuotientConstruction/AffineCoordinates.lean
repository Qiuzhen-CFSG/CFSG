module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Trio
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Binary affine coordinates on the standard octad trio

The displayed point table labels each octad of the native W24 standard trio
by the eight vectors of F₂³. The bijection and its agreement with all three
literal octads are checked by the kernel.

The labels were found by matching complementary tetrads across pairs of
standard octads whose unions are Golay octads. This module only establishes
the coordinate bijection; invariance of the affine structures under the trio
stabilizer is a separate obligation.

Source context: Aschbacher, *Sporadic Groups*, Chapter 7, Lemma 20.2,
printed p.97. The coordinates refer directly to the native Golay basis in
`Theory.Mathieu.M24.Block`, so no alternate group carrier is used.
-/

@[expose] public section

namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction

/-- The vector space labelling each of the three octads. -/
abbrev Vector := Fin 3 → ZMod 2

/-- Coordinate labels, listed in binary order within each octad. -/
def pointTable : Fin 3 → Fin 8 → Fin 24 :=
  ![![0, 16, 22, 2, 23, 1, 3, 10],
    ![7, 19, 6, 20, 14, 15, 12, 9],
    ![4, 13, 21, 11, 18, 5, 17, 8]]

/-- The little-endian binary index of a vector. -/
def vectorIndex (v : Vector) : Fin 8 :=
  ⟨(v 0).val + 2 * (v 1).val + 4 * (v 2).val, by
    have := ZMod.val_lt (v 0)
    have := ZMod.val_lt (v 1)
    have := ZMod.val_lt (v 2)
    omega⟩

/-- A checked bijection onto the original 24-point carrier. -/
noncomputable def point : (Fin 3 × Vector) ≃ Fin 24 :=
  Equiv.ofBijective (fun p => pointTable p.1 (vectorIndex p.2)) (by decide +kernel)

theorem point_mem_octad (i : Fin 3) (v : Vector) :
    point (i,v) ∈ standardTrioOctad i := by
  revert i v
  decide +kernel

theorem point_mem_octad_iff (i j : Fin 3) (v : Vector) :
    point (i,v) ∈ standardTrioOctad j ↔ i = j := by
  revert i j v
  decide +kernel

theorem point_image (i : Fin 3) :
    Finset.univ.image (fun v : Vector => point (i,v)) = standardTrioOctad i := by
  revert i
  decide +kernel

theorem point_apply (i : Fin 3) (v : Vector) :
    point (i,v) = pointTable i (vectorIndex v) := rfl

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
