module
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Curves
public import Theory.SpecificGroups.Triality.Model.QTKEParameters
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Injectivity.Layers

/-!
# Injectivity of the actual twelve-root Geck product

The displayed D4 roots have heights 1,1,1,1,2,2,2,3,3,3,4,5. Apply the
matrix-filtration uniqueness theorem to their canonical integral Geck curves:
the first parameter is recovered from its Cartan/opposite-root column, its
unit is canceled, and the argument repeats on the remaining roots. The chosen
Tits routes and their integral signs are retained throughout.

This proves injectivity over every standard coefficient field, in particular
for all binary parameters, including exponent one. It supplies the untwisted
positive-product uniqueness input to the fixed-point construction in GLS3,
2.3.6–7 and §§2.4–2.6 (`refs/KGroup/GLS3/chapter2.tex`). Collection and
compatibility with the graph-field automorphism are separate results.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace Triality.Standard.PositiveCoordinates
open Injectivity

/-- Sum of the simple-root coefficients, in the ambient four coordinates. -/
private def rootHeight : typeDRootSpan 4 →+ ℝ where
  toFun x := 3 * x.val 0 + 2 * x.val 1 + x.val 2
  map_zero' := by simp
  map_add' x y := by simp only [Submodule.coe_add, Pi.add_apply]; ring

private lemma rootHeight_rootIndex (i : Fin 12) :
    rootHeight ((typeDRootPairing 2).root (rootIndex i)) =
      ![1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 5] i := by
  fin_cases i <;>
    norm_num [rootHeight, rootIndex, difference, sumRoot,
      typeDRootPairing_root_val, typeDRootEmbedding, typeDRootVector,
      basisVector, Pi.single_apply, Fin.ext_iff]

private lemma rootHeight_pos (i : Fin 12) :
    0 < rootHeight ((typeDRootPairing 2).root (rootIndex i)) := by
  rw [rootHeight_rootIndex]
  fin_cases i <;> norm_num

private lemma rootHeight_monotone :
    Monotone (fun i => rootHeight ((typeDRootPairing 2).root (rootIndex i))) := by
  intro i j hij
  change i.val ≤ j.val at hij
  simp only [rootHeight_rootIndex]
  fin_cases i <;> fin_cases j
  all_goals try norm_num at hij
  all_goals norm_num

/-- Uniqueness for the actual twelve canonical Geck root curves. -/
theorem orderedProduct_injective (P : Parameters) : Function.Injective (orderedProduct P) := by
  classical
  intro a a' heq
  let l := List.ofFn rootIndex
  let A := Function.extend rootIndex a (fun _ => 0)
  let A' := Function.extend rootIndex a' (fun _ => 0)
  have hl : ∀ r ∈ l, (typeDRootPairing_base 2).IsPos r := by
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact rootIndex_positive i
  have hpos : ∀ r ∈ l, 0 < rootHeight ((typeDRootPairing 2).root r) := by
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact rootHeight_pos i
  have hnd : l.Nodup := List.nodup_ofFn.mpr rootIndex_injective
  have hsort : l.Pairwise (fun r s =>
      rootHeight ((typeDRootPairing 2).root r) ≤ rootHeight ((typeDRootPairing 2).root s)) :=
    List.pairwise_ofFn.mpr (fun _ _ hij => rootHeight_monotone hij.le)
  have hu : (l.map (fun r => rootCurveUnit
      (integralChevalleyRootOperators (b := typeDRootPairing_base 2)) r (A r))).prod =
      (l.map (fun r => rootCurveUnit
      (integralChevalleyRootOperators (b := typeDRootPairing_base 2)) r (A' r))).prod := by
    have h := congrArg
      (RootPairing.SimpleGeckGroup.subgroup (typeDRootPairing_base 2)
        (ExtensionField P)).subtype heq
    simpa only [orderedProduct, map_list_prod, List.map_ofFn, Function.comp_def,
      Subgroup.subtype_apply, curve, l, A, A', rootIndex_injective.extend_apply] using h
  have hcoords := rootCurve_prod_parameters_eq rootHeight l hl hpos hnd hsort A A' hu
  funext i
  have hi := hcoords (rootIndex i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  simpa only [A, A', rootIndex_injective.extend_apply] using hi

/-- In particular, the binary family includes exponent one. -/
theorem orderedProduct_injective_binary (n : ℕ) (hn : 0 < n) :
    Function.Injective (orderedProduct (binaryParameters n hn)) :=
  orderedProduct_injective (binaryParameters n hn)

end Triality.Standard.PositiveCoordinates
