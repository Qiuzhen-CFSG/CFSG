module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexSetup
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# A seven-dimensional candidate for Lyons coset separation

The displayed column basis has an identity block in its first seven rows.
It was obtained as the annihilator of a 104-dimensional invariant row space
found by GAP's MeatAxe for the literal ATLAS local generators. The two small
matrices are candidates for the induced local actions. Their invertibility
is checked here; the identities connecting them to the actual local words
remain explicit premises of `separationPlane_fixed_of_matrix_identities`.

The ambient action is literal matrix multiplication on column vectors and
its induced action on sets. Thus separation of translates of this plane,
together with the two matrix identities, proves a bound for the fixed matrix
group without an assumed permutation representation or subgroup identification.

Source matrices: `Atlas111Source/`. Subgroup words: `Atlas111OrderSource/`.
Reproducible exploratory data and attribution: `Atlas111SeparationSource/`.
-/

namespace Lyons.OrderCertificate

open Matrix
open scoped Pointwise

/-- The natural column-vector space of the fixed matrix representation. -/
public abbrev SeparationVector := Fin 111 → ZMod 5

/-- The natural action uses exactly the matrices defining `LyonsGroup`. -/
public instance separationColumnAction : MulAction LyonsGroup SeparationVector where
  smul g v := matrixRepresentation g *ᵥ v
  one_smul v := by
    change matrixRepresentation 1 *ᵥ v = v
    rw [map_one, one_mulVec]
  mul_smul g h v := by
    change matrixRepresentation (g * h) *ᵥ v =
      matrixRepresentation g *ᵥ (matrixRepresentation h *ᵥ v)
    rw [map_mul, mulVec_mulVec]

/-- The seven columns of the candidate plane, in the original ATLAS coordinates. -/
@[expose] public def separationPlaneColumns : Matrix (Fin 111) (Fin 7) (ZMod 5) :=
  ![![1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 3, 0, 0, 3],
    ![4, 0, 0, 0, 1, 4, 0],
    ![2, 3, 4, 3, 2, 0, 0],
    ![0, 2, 2, 3, 3, 4, 3],
    ![3, 1, 0, 0, 3, 1, 3],
    ![3, 0, 0, 0, 0, 3, 0],
    ![4, 4, 0, 3, 3, 2, 0],
    ![4, 0, 0, 2, 2, 1, 3],
    ![3, 3, 3, 2, 2, 2, 2],
    ![4, 4, 0, 4, 2, 3, 4],
    ![3, 0, 1, 2, 1, 4, 0],
    ![3, 1, 2, 0, 2, 0, 0],
    ![3, 3, 4, 2, 0, 1, 1],
    ![2, 0, 2, 1, 4, 0, 0],
    ![2, 1, 1, 2, 0, 2, 4],
    ![2, 0, 2, 4, 1, 4, 2],
    ![4, 2, 3, 1, 3, 3, 2],
    ![4, 0, 0, 1, 3, 4, 2],
    ![3, 0, 3, 2, 3, 1, 1],
    ![4, 0, 0, 0, 2, 1, 3],
    ![1, 0, 0, 4, 4, 3, 1],
    ![2, 2, 2, 4, 2, 3, 1],
    ![0, 2, 1, 0, 1, 0, 4],
    ![3, 0, 4, 2, 0, 4, 3],
    ![4, 3, 4, 0, 3, 0, 3],
    ![1, 0, 1, 1, 2, 0, 0],
    ![0, 2, 2, 4, 0, 0, 0],
    ![2, 4, 0, 3, 4, 1, 0],
    ![3, 3, 2, 4, 3, 2, 3],
    ![4, 3, 0, 0, 1, 2, 2],
    ![2, 4, 0, 1, 2, 0, 1],
    ![4, 3, 1, 0, 2, 3, 0],
    ![0, 4, 1, 3, 3, 2, 2],
    ![2, 2, 0, 1, 0, 4, 3],
    ![1, 3, 2, 4, 0, 2, 0],
    ![0, 3, 0, 0, 1, 4, 4],
    ![0, 0, 4, 0, 3, 4, 3],
    ![3, 2, 2, 3, 4, 0, 4],
    ![2, 1, 0, 0, 3, 4, 0],
    ![2, 0, 3, 1, 0, 3, 3],
    ![0, 3, 2, 3, 4, 1, 1],
    ![3, 1, 3, 4, 3, 0, 2],
    ![3, 1, 2, 2, 3, 2, 1],
    ![2, 3, 0, 4, 2, 2, 1],
    ![4, 4, 1, 3, 3, 1, 1],
    ![0, 2, 4, 4, 2, 2, 0],
    ![3, 0, 3, 1, 0, 1, 1],
    ![4, 1, 0, 3, 4, 4, 4],
    ![3, 4, 3, 4, 0, 1, 3],
    ![4, 4, 3, 1, 3, 2, 3],
    ![1, 1, 1, 1, 4, 0, 3],
    ![2, 4, 2, 1, 3, 3, 2],
    ![3, 3, 0, 0, 2, 4, 2],
    ![1, 4, 3, 4, 1, 1, 4],
    ![0, 4, 1, 1, 3, 0, 0],
    ![1, 1, 3, 0, 3, 3, 0],
    ![0, 2, 4, 1, 1, 4, 3],
    ![2, 2, 1, 2, 1, 4, 0],
    ![2, 4, 2, 3, 3, 4, 2],
    ![2, 2, 3, 0, 2, 2, 2],
    ![3, 3, 1, 4, 0, 0, 4],
    ![2, 3, 3, 1, 3, 2, 0],
    ![4, 3, 2, 3, 4, 4, 2],
    ![1, 1, 2, 0, 1, 0, 2],
    ![0, 4, 4, 2, 3, 1, 4],
    ![4, 3, 0, 4, 0, 1, 3],
    ![0, 3, 2, 1, 2, 3, 3],
    ![3, 0, 1, 1, 0, 4, 2],
    ![3, 0, 3, 0, 3, 0, 0],
    ![3, 4, 2, 2, 1, 0, 3],
    ![0, 3, 1, 1, 0, 2, 0],
    ![2, 3, 0, 3, 4, 1, 1],
    ![0, 1, 3, 0, 1, 4, 3],
    ![3, 4, 2, 1, 2, 1, 0],
    ![1, 4, 3, 0, 3, 0, 3],
    ![0, 1, 4, 1, 0, 1, 3],
    ![4, 3, 0, 3, 3, 2, 3],
    ![0, 1, 1, 4, 1, 4, 4],
    ![3, 1, 1, 1, 2, 3, 1],
    ![1, 3, 2, 1, 2, 4, 3],
    ![2, 2, 1, 1, 4, 4, 1],
    ![4, 2, 3, 3, 4, 4, 3],
    ![2, 1, 1, 1, 1, 0, 3],
    ![4, 4, 0, 0, 3, 0, 1],
    ![4, 2, 0, 1, 0, 2, 1],
    ![3, 1, 3, 2, 1, 3, 2],
    ![3, 1, 3, 4, 4, 3, 1],
    ![0, 3, 1, 3, 0, 0, 0],
    ![3, 2, 4, 0, 4, 4, 4],
    ![1, 0, 4, 0, 3, 2, 2],
    ![1, 1, 1, 0, 2, 2, 2],
    ![4, 0, 0, 2, 0, 1, 1],
    ![0, 2, 0, 0, 0, 2, 4],
    ![4, 0, 0, 0, 1, 3, 3],
    ![1, 0, 0, 3, 1, 2, 0],
    ![1, 3, 4, 3, 1, 3, 3],
    ![3, 1, 3, 2, 0, 1, 1],
    ![2, 0, 1, 3, 2, 2, 0],
    ![4, 0, 4, 3, 3, 4, 3],
    ![0, 1, 1, 4, 1, 3, 1],
    ![3, 3, 4, 3, 2, 3, 4],
    ![0, 3, 1, 0, 2, 2, 4],
    ![0, 0, 1, 4, 3, 4, 4],
    ![4, 1, 3, 0, 4, 0, 2]]

/-- The normalization makes the first seven coordinates recover the coefficients. -/
public theorem separationPlaneColumns_pivots (i j : Fin 7) :
    separationPlaneColumns (Fin.castLE (by decide) i) j = if i = j then 1 else 0 := by
  revert i j
  decide +kernel

/-- Candidate restriction of the first local generator to the seven columns. -/
@[expose] public def separationPlaneActionA : Matrix (Fin 7) (Fin 7) (ZMod 5) :=
  ![![4, 0, 1, 3, 4, 4, 2],
    ![2, 4, 3, 4, 4, 3, 4],
    ![1, 1, 2, 3, 3, 3, 3],
    ![1, 1, 4, 0, 2, 2, 0],
    ![0, 1, 0, 4, 4, 3, 3],
    ![0, 0, 4, 2, 1, 0, 3],
    ![3, 1, 3, 3, 0, 4, 0]]

/-- Candidate restriction of the second local generator to the seven columns. -/
@[expose] public def separationPlaneActionB : Matrix (Fin 7) (Fin 7) (ZMod 5) :=
  ![![0, 2, 3, 2, 4, 3, 0],
    ![4, 2, 1, 4, 1, 1, 4],
    ![0, 3, 4, 2, 1, 4, 3],
    ![4, 1, 0, 3, 0, 3, 2],
    ![2, 4, 4, 4, 1, 0, 0],
    ![1, 4, 4, 1, 4, 0, 1],
    ![4, 4, 1, 1, 4, 4, 1]]

/-- An inverse candidate for the small local action. -/
private def separationPlaneInverseA : Matrix (Fin 7) (Fin 7) (ZMod 5) :=
  ![![4, 0, 1, 3, 4, 4, 2],
    ![2, 4, 3, 4, 4, 3, 4],
    ![1, 1, 2, 3, 3, 3, 3],
    ![1, 1, 4, 0, 2, 2, 0],
    ![0, 1, 0, 4, 4, 3, 3],
    ![0, 0, 4, 2, 1, 0, 3],
    ![3, 1, 3, 3, 0, 4, 0]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem separationPlaneActionA_rightInverse :
    separationPlaneActionA * separationPlaneInverseA = 1 := by
  decide +kernel

/-- An inverse candidate for the small local action. -/
private def separationPlaneInverseB : Matrix (Fin 7) (Fin 7) (ZMod 5) :=
  ![![2, 3, 2, 4, 1, 0, 4],
    ![3, 3, 0, 4, 0, 1, 4],
    ![3, 2, 2, 2, 1, 2, 0],
    ![2, 3, 2, 1, 2, 0, 0],
    ![4, 2, 0, 4, 2, 3, 1],
    ![2, 3, 0, 1, 0, 0, 1],
    ![1, 1, 3, 0, 0, 2, 1]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem separationPlaneActionB_rightInverse :
    separationPlaneActionB * separationPlaneInverseB = 1 := by
  decide +kernel

/-- Taking the first seven coordinates recovers the column coefficients. -/
public theorem separationPlaneColumns_coordinates (x : Fin 7 → ZMod 5) (i : Fin 7) :
    (separationPlaneColumns *ᵥ x) (Fin.castLE (by decide) i) = x i := by
  simp [Matrix.mulVec, dotProduct, separationPlaneColumns_pivots]

/-- The displayed columns are independent. -/
public theorem separationPlaneColumns_injective :
    Function.Injective separationPlaneColumns.mulVec := by
  intro x y h
  funext i
  have hi := congrFun h (Fin.castLE (by decide : 7 ≤ 111) i)
  simpa only [separationPlaneColumns_coordinates] using hi

/-- The candidate plane, as a set of actual column vectors. -/
@[expose] public def separationPlane : Set SeparationVector :=
  Set.range separationPlaneColumns.mulVec

private theorem plane_fixed_of_intertwiner {k : ℕ}
    (U : Matrix (Fin 111) (Fin k) (ZMod 5))
    (g : LyonsGroup) (S T : Matrix (Fin k) (Fin k) (ZMod 5))
    (hST : S * T = 1) (h : matrixRepresentation g * U = U * S) :
    g • Set.range U.mulVec = Set.range U.mulVec := by
  ext v
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨S *ᵥ x, ?_⟩
    change U *ᵥ (S *ᵥ x) = matrixRepresentation g *ᵥ (U *ᵥ x)
    rw [mulVec_mulVec, mulVec_mulVec, h]
  · rintro ⟨x, rfl⟩
    refine ⟨U *ᵥ (T *ᵥ x), ⟨T *ᵥ x, rfl⟩, ?_⟩
    change matrixRepresentation g *ᵥ (U *ᵥ (T *ᵥ x)) = U *ᵥ x
    rw [mulVec_mulVec, h, mulVec_mulVec, Matrix.mul_assoc, hST, Matrix.mul_one]

/-- Two explicit matrix identities certify that the local generators fix the plane. -/
public theorem separationPlane_fixed_of_matrix_identities
    (ha : matrixRepresentation localA * separationPlaneColumns =
      separationPlaneColumns * separationPlaneActionA)
    (hb : matrixRepresentation localB * separationPlaneColumns =
      separationPlaneColumns * separationPlaneActionB) :
    localA • separationPlane = separationPlane ∧
      localB • separationPlane = separationPlane :=
  ⟨plane_fixed_of_intertwiner _ _ _ _ separationPlaneActionA_rightInverse ha,
    plane_fixed_of_intertwiner _ _ _ _ separationPlaneActionB_rightInverse hb⟩

/-- A translate can be computed by multiplying the displayed column matrix. -/
public theorem smul_separationPlane (g : LyonsGroup) :
    g • separationPlane = Set.range (matrixRepresentation g * separationPlaneColumns).mulVec := by
  ext v
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (mulVec_mulVec x _ _).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨separationPlaneColumns *ᵥ x, ⟨x, rfl⟩, mulVec_mulVec x _ _⟩

/-- Membership is decided by reconstructing a vector from its first seven coordinates. -/
public theorem mem_separationPlane_iff (v : SeparationVector) :
    v ∈ separationPlane ↔
      separationPlaneColumns *ᵥ (fun i : Fin 7 => v (Fin.castLE (by decide) i)) = v := by
  constructor
  · rintro ⟨x, rfl⟩
    congr 1
    funext i
    exact separationPlaneColumns_coordinates x i
  · intro h
    exact ⟨_, h⟩

private def movedColumn : SeparationVector :=
  atlasAMatrix *ᵥ (fun j => separationPlaneColumns j 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem movedColumn_mismatch :
    (separationPlaneColumns *ᵥ
      (fun i : Fin 7 => movedColumn (Fin.castLE (by decide) i))) 7 ≠ movedColumn 7 := by
  decide +kernel

/-- The plane is not globally invariant: ambient A moves its first column outside it. -/
public theorem generatorA_moves_separationPlane :
    generatorA • separationPlane ≠ separationPlane := by
  intro h
  have hcol : (fun j => separationPlaneColumns j 0) ∈ separationPlane := by
    apply (mem_separationPlane_iff _).mpr
    ext j
    simp [separationPlaneColumns_pivots, Matrix.mulVec, dotProduct]
  have hm : movedColumn ∈ generatorA • separationPlane := ⟨_, hcol, rfl⟩
  rw [h, mem_separationPlane_iff] at hm
  exact movedColumn_mismatch (congrFun hm 7)

end Lyons.OrderCertificate
