module

public import Theory.SpecificGroups.HaradaNorton.Order.LocalIndex.PackedColumns
public import Theory.SpecificGroups.HaradaNorton.Order.LocalIndex.Bounds
public import Theory.SpecificGroups.HaradaNorton.Order.LocalIndex.FixedVector

/-!
# The column action and the local-index lower bound

The faithful matrix interpretation acts on columns. The checked fixed-column
identities put the concrete local subgroup inside a stabilizer. Consequently,
1,140,000 distinct reachable columns suffice for the lower index bound, without
assuming that the local subgroup equals the full stabilizer.

The vector and its source attribution are in `FixedVector`; the abstract orbit
and index argument is in `Bounds`.
-/

namespace HaradaNorton.OrderCertificate
open Matrix

/-- The action of the fixed matrix carrier on its defining column space. -/
public instance indexColumnAction : MulAction HN (Fin 133 → ZMod 5) where
  smul g v := matrixHom g *ᵥ v
  one_smul v := by
    change matrixHom (1 : HN) *ᵥ v = v
    rw [map_one, Matrix.one_mulVec]
  mul_smul g h v := by
    change matrixHom (g * h) *ᵥ v = matrixHom g *ᵥ matrixHom h *ᵥ v
    rw [map_mul, Matrix.mulVec_mulVec]

/-- Every element of the actual word subgroup fixes the certified column. -/
public theorem localSubgroup_fixes_indexBaseVector (g : HN) (hg : g ∈ localSubgroup) :
    matrixHom g *ᵥ indexBaseVector = indexBaseVector := by
  have ha : a • indexBaseVector = indexBaseVector := aMatrix_mulVec_indexBaseVector
  have hb : localB • indexBaseVector = indexBaseVector := localB_mulVec_indexBaseVector
  exact localSubgroup_le_stabilizer indexBaseVector ha hb hg

/-- Distinct translates of the certified column provide the required lower bound. -/
public theorem localSubgroup_index_ge_of_columns (r : Fin 1140000 → HN)
    (hinj : Function.Injective (fun i => matrixHom (r i) *ᵥ indexBaseVector)) :
    1140000 ≤ localSubgroup.index := by
  refine localSubgroup_index_ge_of_action indexBaseVector ?_ ?_ r ?_
  · change matrixHom a *ᵥ indexBaseVector = indexBaseVector
    rw [matrixHom_a]
    exact aMatrix_mulVec_indexBaseVector
  · change matrixHom localB *ᵥ indexBaseVector = indexBaseVector
    exact localB_mulVec_indexBaseVector
  · exact hinj

/-- A column enumeration can certify reachability without supplying a global transversal. -/
public theorem localSubgroup_index_ge_of_reachable_columns
    (point : Fin 1140000 → (Fin 133 → ZMod 5)) (hinj : Function.Injective point)
    (hreach : ∀ i, ∃ g : HN, matrixHom g *ᵥ indexBaseVector = point i) :
    1140000 ≤ localSubgroup.index := by
  classical
  choose r hr using hreach
  apply localSubgroup_index_ge_of_columns r
  simpa only [hr] using hinj

/-- A rooted tree of certified generator steps proves reachability of every column.
The decreasing depth is useful when columns are sorted for a separate injectivity check. -/
public theorem indexColumns_reachable {ι : Type*}
    (point : ι → (Fin 133 → ZMod 5)) (root : ι)
    (hroot : point root = indexBaseVector) (parent : ι → ι)
    (depth : ι → ℕ) (letter : ι → Bool)
    (hdepth : ∀ i, i ≠ root → depth (parent i) < depth i)
    (hstep : ∀ i, i ≠ root →
      matrixHom (indexGenerator (letter i)) *ᵥ point (parent i) = point i) :
    ∀ i, ∃ g : HN, matrixHom g *ᵥ indexBaseVector = point i := by
  intro i
  induction i using (measure depth).wf.induction with
  | h i ih =>
    by_cases hi : i = root
    · subst i
      exact ⟨1, by rw [map_one, Matrix.one_mulVec, hroot]⟩
    · obtain ⟨g, hg⟩ := ih (parent i) (hdepth i hi)
      refine ⟨indexGenerator (letter i) * g, ?_⟩
      rw [map_mul, ← Matrix.mulVec_mulVec, hg]
      exact hstep i hi

end HaradaNorton.OrderCertificate
