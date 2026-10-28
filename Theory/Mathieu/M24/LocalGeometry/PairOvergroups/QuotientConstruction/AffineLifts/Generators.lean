module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineQuotient
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineLifts.CodePreservation

/-!
# Four native affine lifts in the M₂₄ trio stabilizer

The octad swap and cycle, and the common cyclic permutation of vector
coordinates, have zero translation. The elementary map adding coordinate 1
to coordinate 0 requires translation (0,0,1) on the third octad. The displayed
permutation tables are checked against the fixed native affine coordinates.
Their membership in M₂₄ follows by checking all twelve Golay row images.

These are generators for the quotient coordinates, not an asserted splitting.
Source context: Aschbacher, *Sporadic Groups*, Chapter 7, Lemma 20.2,
printed p.97; GLS3, Table 5.3e. All finite identities use kernel reduction.
-/

public section

open scoped Pointwise Matrix
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction.AffineLiftConstruction

/-- The common cyclic map (v₀,v₁,v₂) ↦ (v₂,v₀,v₁). -/
@[expose] def linearCycle : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide +kernel⟩

/-- The elementary map (v₀,v₁,v₂) ↦ (v₀+v₁,v₁,v₂). -/
@[expose] def linearTransvection : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide +kernel⟩

/-- Two generators in each factor of S₃ × SL₃(2). -/
@[expose] def generatorQuotient : Fin 4 → QuotientModel :=
  ![(Equiv.swap 0 1, 1), (Equiv.swap 0 1 * Equiv.swap 1 2, 1),
    (1, linearCycle), (1, linearTransvection)]

private def permTable : Fin 4 → Fin 24 → Fin 24 :=
  ![![7, 15, 20, 12, 4, 5, 22, 0, 8, 10, 9, 11, 3, 13, 23, 1, 19, 17, 18, 16, 2, 21, 6, 14],
    ![7, 15, 20, 12, 0, 1, 21, 4, 10, 8, 9, 2, 17, 16, 18, 5, 19, 3, 23, 13, 11, 22, 6, 14],
    ![0, 2, 3, 1, 4, 11, 14, 7, 8, 9, 10, 17, 15, 21, 19, 20, 22, 5, 13, 6, 12, 18, 23, 16],
    ![0, 1, 22, 10, 18, 13, 20, 7, 21, 12, 3, 17, 9, 5, 14, 15, 16, 11, 4, 19, 6, 8, 2, 23]]

private def inverseTable : Fin 4 → Fin 24 → Fin 24 :=
  ![![7, 15, 20, 12, 4, 5, 22, 0, 8, 10, 9, 11, 3, 13, 23, 1, 19, 17, 18, 16, 2, 21, 6, 14],
    ![4, 5, 11, 17, 7, 15, 22, 0, 9, 10, 8, 20, 3, 19, 23, 1, 13, 12, 14, 16, 2, 6, 21, 18],
    ![0, 3, 1, 2, 4, 17, 19, 7, 8, 9, 10, 5, 20, 18, 6, 12, 23, 11, 21, 14, 15, 13, 16, 22],
    ![0, 1, 22, 10, 18, 13, 20, 7, 21, 12, 3, 17, 9, 5, 14, 15, 16, 11, 4, 19, 6, 8, 2, 23]]

/-- The four permutations on the native 24-point carrier. -/
private def generatorPerm (k : Fin 4) : Equiv.Perm (Fin 24) where
  toFun := permTable k
  invFun := inverseTable k
  left_inv := by revert k; decide +kernel
  right_inv := by revert k; decide +kernel

private def rowMessage : Fin 4 → Fin 12 → Fin 4096 :=
  ![![142, 578, 584, 580, 538, 32, 76, 591, 774, 524, 1098, 2118],
    ![1192, 2664, 584, 3656, 2601, 2058, 3136, 1648, 3616, 1792, 108, 3168],
    ![33, 100, 2088, 2146, 112, 3168, 2112, 128, 2368, 2560, 2080, 64],
    ![1857, 1294, 1564, 1116, 1544, 3344, 852, 716, 88, 856, 1812, 356]]

private theorem row_images (k : Fin 4) (i : Fin 12) :
    m24PermuteMask (generatorPerm k) (m24GolayRow i) =
      m24GolayCode (rowMessage k i) := by
  revert k i
  decide +kernel

/-- The explicit permutations preserve the native Witt design. -/
private theorem generatorPerm_mem (k : Fin 4) : generatorPerm k ∈ M24 :=
  mem_M24_of_rows _ (fun i => ⟨rowMessage k i, row_images k i⟩)

/-- The four permutations as elements of the actual trio stabilizer. -/
noncomputable def generatorLift (k : Fin 4) : trioStabilizer standardTrio :=
  ⟨⟨generatorPerm k, generatorPerm_mem k⟩, by
    apply (mem_trioStabilizer_iff _ _).mpr
    intro A hA
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    change generatorPerm k • standardTrioOctad i ∈ standardTrio.parts
    revert k i
    decide +kernel⟩

/-- The necessary translation on the third octad for the transvection. -/
def generatorTranslation (k : Fin 4) : Fin 3 → Vector :=
  if k = 3 then ![0, 0, ![0, 0, 1]] else 0

/-- The coordinate formula is checked on every native point. -/
theorem generatorLift_hasAffineForm (k : Fin 4) :
    HasAffineForm (generatorLift k) (generatorQuotient k) (generatorTranslation k) := by
  change ∀ i v, generatorPerm k (point (i,v)) =
    point ((generatorQuotient k).1 i,
      Matrix.SpecialLinearGroup.toLin' (generatorQuotient k).2 v + generatorTranslation k i)
  revert k
  decide +kernel

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction.AffineLiftConstruction
