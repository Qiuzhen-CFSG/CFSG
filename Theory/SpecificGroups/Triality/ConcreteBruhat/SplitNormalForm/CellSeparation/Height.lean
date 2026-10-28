module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.Inputs

/-!
# Root-height filtration of the literal split D4 matrices

Every positive root curve is identity modulo matrices raising height by at
least one. The ordered positive parametrization extends this bound to the
whole positive subgroup, over every binary parameter field, including n = 1.
The height functional is the sum of the simple-root coefficients; its explicit
formula agrees with the private functional used by positive-coordinate injectivity.

Source: GLS3 2.3.5 and 2.3.8(c), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
namespace Triality.Standard.ConcreteBruhat.SplitNormalForm.CellSeparation
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Parabolics PositiveCoordinates PositiveCoordinates.Injectivity
open Parabolics.RankOneMatrices
local instance matrixLatticeDecidableEq : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

def height : typeDRootSpan 4 →+ ℝ where
  toFun x := 3 * x.val 0 + 2 * x.val 1 + x.val 2
  map_zero' := by simp
  map_add' x y := by simp only [Submodule.coe_add, Pi.add_apply]; ring

lemma height_rootIndex (i : Fin 12) :
    height ((typeDRootPairing 2).root (rootIndex i)) =
      ![1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 5] i := by
  fin_cases i <;>
    norm_num [height, rootIndex, difference, sumRoot,
      typeDRootPairing_root_val, typeDRootEmbedding, typeDRootVector,
      basisVector, Pi.single_apply, Fin.ext_iff]

lemma height_rootIndex_ge_one (i : Fin 12) :
    1 ≤ height ((typeDRootPairing 2).root (rootIndex i)) := by
  rw [height_rootIndex]
  fin_cases i <;> norm_num

def degree : LatticeIndex → ℝ :=
  fun j => height (rootWeight (b := typeDRootPairing_base 2) j)

def matrix (P : Parameters) :
    SplitGroup P →* Matrix LatticeIndex LatticeIndex (ExtensionField P) :=
  (Units.coeHom _).comp (RootPairing.SimpleGeckGroup.subgroup
    (typeDRootPairing_base 2) (ExtensionField P)).subtype

lemma curve_raises (P : Parameters) (i : Fin 12) (t : ExtensionField P) :
    Raises degree 1 (matrix P (curve P i t) - 1) :=
  (rootMatrix_raises height (rootIndex i) (rootIndex_positive i)
    (by linarith [height_rootIndex_ge_one i]) t).mono degree (height_rootIndex_ge_one i)

lemma orderedProduct_raises (P : Parameters) (a : PositiveCoordinates.Coordinates P) :
    Raises degree 1 (matrix P (orderedProduct P a) - 1) := by
  rw [orderedProduct, map_list_prod, List.map_ofFn]
  apply raises_prod_sub_one degree 1 (by norm_num)
  intro A hA
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
  exact curve_raises P i (a i)

lemma positive_raises (n : ℕ) (hn : 0 < n)
    {g : SplitGroup (binaryParameters n hn)} (hg : g ∈ positiveSubgroup _) :
    Raises degree 1 (matrix _ g - 1) := by
  change g ∈ (positiveSubgroup (binaryParameters n hn) : Set (SplitGroup _)) at hg
  rw [← range_orderedProduct_binary n hn] at hg
  obtain ⟨a, rfl⟩ := hg
  exact orderedProduct_raises _ a

end
end Triality.Standard.ConcreteBruhat.SplitNormalForm.CellSeparation
