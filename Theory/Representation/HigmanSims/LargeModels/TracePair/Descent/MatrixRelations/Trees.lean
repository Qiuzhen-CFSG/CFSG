module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Trees.Data

/-!
# Interpretation and interval checks for the balanced generator trees

Reflexivity identifies the flattened trees with the shared literal rows. A
local recursion-depth allowance is needed only to compare lists of length 896;
no arithmetic or heartbeat budget is raised. Cached interval proofs compose
from bounded 28-row checks, avoiding repeated flattening of the whole matrix.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
open Certificates

private theorem treeABlock00_spec : (Balanced.rows treeABlock00).length = 28 ∧
    Balanced.valid treeABlock00 = true := by decide +kernel

private theorem treeABlock01_spec : (Balanced.rows treeABlock01).length = 28 ∧
    Balanced.valid treeABlock01 = true := by decide +kernel

private theorem treeABlock02_spec : (Balanced.rows treeABlock02).length = 28 ∧
    Balanced.valid treeABlock02 = true := by decide +kernel

private theorem treeABlock03_spec : (Balanced.rows treeABlock03).length = 28 ∧
    Balanced.valid treeABlock03 = true := by decide +kernel

private theorem treeABlock04_spec : (Balanced.rows treeABlock04).length = 28 ∧
    Balanced.valid treeABlock04 = true := by decide +kernel

private theorem treeABlock05_spec : (Balanced.rows treeABlock05).length = 28 ∧
    Balanced.valid treeABlock05 = true := by decide +kernel

private theorem treeABlock06_spec : (Balanced.rows treeABlock06).length = 28 ∧
    Balanced.valid treeABlock06 = true := by decide +kernel

private theorem treeABlock07_spec : (Balanced.rows treeABlock07).length = 28 ∧
    Balanced.valid treeABlock07 = true := by decide +kernel

private theorem treeABlock08_spec : (Balanced.rows treeABlock08).length = 28 ∧
    Balanced.valid treeABlock08 = true := by decide +kernel

private theorem treeABlock09_spec : (Balanced.rows treeABlock09).length = 28 ∧
    Balanced.valid treeABlock09 = true := by decide +kernel

private theorem treeABlock10_spec : (Balanced.rows treeABlock10).length = 28 ∧
    Balanced.valid treeABlock10 = true := by decide +kernel

private theorem treeABlock11_spec : (Balanced.rows treeABlock11).length = 28 ∧
    Balanced.valid treeABlock11 = true := by decide +kernel

private theorem treeABlock12_spec : (Balanced.rows treeABlock12).length = 28 ∧
    Balanced.valid treeABlock12 = true := by decide +kernel

private theorem treeABlock13_spec : (Balanced.rows treeABlock13).length = 28 ∧
    Balanced.valid treeABlock13 = true := by decide +kernel

private theorem treeABlock14_spec : (Balanced.rows treeABlock14).length = 28 ∧
    Balanced.valid treeABlock14 = true := by decide +kernel

private theorem treeABlock15_spec : (Balanced.rows treeABlock15).length = 28 ∧
    Balanced.valid treeABlock15 = true := by decide +kernel

private theorem treeABlock16_spec : (Balanced.rows treeABlock16).length = 28 ∧
    Balanced.valid treeABlock16 = true := by decide +kernel

private theorem treeABlock17_spec : (Balanced.rows treeABlock17).length = 28 ∧
    Balanced.valid treeABlock17 = true := by decide +kernel

private theorem treeABlock18_spec : (Balanced.rows treeABlock18).length = 28 ∧
    Balanced.valid treeABlock18 = true := by decide +kernel

private theorem treeABlock19_spec : (Balanced.rows treeABlock19).length = 28 ∧
    Balanced.valid treeABlock19 = true := by decide +kernel

private theorem treeABlock20_spec : (Balanced.rows treeABlock20).length = 28 ∧
    Balanced.valid treeABlock20 = true := by decide +kernel

private theorem treeABlock21_spec : (Balanced.rows treeABlock21).length = 28 ∧
    Balanced.valid treeABlock21 = true := by decide +kernel

private theorem treeABlock22_spec : (Balanced.rows treeABlock22).length = 28 ∧
    Balanced.valid treeABlock22 = true := by decide +kernel

private theorem treeABlock23_spec : (Balanced.rows treeABlock23).length = 28 ∧
    Balanced.valid treeABlock23 = true := by decide +kernel

private theorem treeABlock24_spec : (Balanced.rows treeABlock24).length = 28 ∧
    Balanced.valid treeABlock24 = true := by decide +kernel

private theorem treeABlock25_spec : (Balanced.rows treeABlock25).length = 28 ∧
    Balanced.valid treeABlock25 = true := by decide +kernel

private theorem treeABlock26_spec : (Balanced.rows treeABlock26).length = 28 ∧
    Balanced.valid treeABlock26 = true := by decide +kernel

private theorem treeABlock27_spec : (Balanced.rows treeABlock27).length = 28 ∧
    Balanced.valid treeABlock27 = true := by decide +kernel

private theorem treeABlock28_spec : (Balanced.rows treeABlock28).length = 28 ∧
    Balanced.valid treeABlock28 = true := by decide +kernel

private theorem treeABlock29_spec : (Balanced.rows treeABlock29).length = 28 ∧
    Balanced.valid treeABlock29 = true := by decide +kernel

private theorem treeABlock30_spec : (Balanced.rows treeABlock30).length = 28 ∧
    Balanced.valid treeABlock30 = true := by decide +kernel

private theorem treeABlock31_spec : (Balanced.rows treeABlock31).length = 28 ∧
    Balanced.valid treeABlock31 = true := by decide +kernel

private theorem treeA_spec : (Balanced.rows treeA).length = 896 ∧
    Balanced.valid treeA = true :=
  Balanced.node_spec 448 448 _ _ (Balanced.node_spec 224 224 _ _ (Balanced.node_spec 112 112 _ _ (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeABlock00_spec) (treeABlock01_spec)) (Balanced.node_spec 28 28 _ _ (treeABlock02_spec) (treeABlock03_spec))) (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeABlock04_spec) (treeABlock05_spec)) (Balanced.node_spec 28 28 _ _ (treeABlock06_spec) (treeABlock07_spec)))) (Balanced.node_spec 112 112 _ _ (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeABlock08_spec) (treeABlock09_spec)) (Balanced.node_spec 28 28 _ _ (treeABlock10_spec) (treeABlock11_spec))) (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeABlock12_spec) (treeABlock13_spec)) (Balanced.node_spec 28 28 _ _ (treeABlock14_spec) (treeABlock15_spec))))) (Balanced.node_spec 224 224 _ _ (Balanced.node_spec 112 112 _ _ (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeABlock16_spec) (treeABlock17_spec)) (Balanced.node_spec 28 28 _ _ (treeABlock18_spec) (treeABlock19_spec))) (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeABlock20_spec) (treeABlock21_spec)) (Balanced.node_spec 28 28 _ _ (treeABlock22_spec) (treeABlock23_spec)))) (Balanced.node_spec 112 112 _ _ (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeABlock24_spec) (treeABlock25_spec)) (Balanced.node_spec 28 28 _ _ (treeABlock26_spec) (treeABlock27_spec))) (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeABlock28_spec) (treeABlock29_spec)) (Balanced.node_spec 28 28 _ _ (treeABlock30_spec) (treeABlock31_spec)))))

set_option maxRecDepth 4096 in
theorem treeA_rows : Balanced.rows treeA = generatorRowsA := by rfl

theorem treeA_valid : Balanced.valid treeA = true := treeA_spec.2

theorem treeA_length : (Balanced.rows treeA).length = 896 := treeA_spec.1

private theorem treeBBlock00_spec : (Balanced.rows treeBBlock00).length = 28 ∧
    Balanced.valid treeBBlock00 = true := by decide +kernel

private theorem treeBBlock01_spec : (Balanced.rows treeBBlock01).length = 28 ∧
    Balanced.valid treeBBlock01 = true := by decide +kernel

private theorem treeBBlock02_spec : (Balanced.rows treeBBlock02).length = 28 ∧
    Balanced.valid treeBBlock02 = true := by decide +kernel

private theorem treeBBlock03_spec : (Balanced.rows treeBBlock03).length = 28 ∧
    Balanced.valid treeBBlock03 = true := by decide +kernel

private theorem treeBBlock04_spec : (Balanced.rows treeBBlock04).length = 28 ∧
    Balanced.valid treeBBlock04 = true := by decide +kernel

private theorem treeBBlock05_spec : (Balanced.rows treeBBlock05).length = 28 ∧
    Balanced.valid treeBBlock05 = true := by decide +kernel

private theorem treeBBlock06_spec : (Balanced.rows treeBBlock06).length = 28 ∧
    Balanced.valid treeBBlock06 = true := by decide +kernel

private theorem treeBBlock07_spec : (Balanced.rows treeBBlock07).length = 28 ∧
    Balanced.valid treeBBlock07 = true := by decide +kernel

private theorem treeBBlock08_spec : (Balanced.rows treeBBlock08).length = 28 ∧
    Balanced.valid treeBBlock08 = true := by decide +kernel

private theorem treeBBlock09_spec : (Balanced.rows treeBBlock09).length = 28 ∧
    Balanced.valid treeBBlock09 = true := by decide +kernel

private theorem treeBBlock10_spec : (Balanced.rows treeBBlock10).length = 28 ∧
    Balanced.valid treeBBlock10 = true := by decide +kernel

private theorem treeBBlock11_spec : (Balanced.rows treeBBlock11).length = 28 ∧
    Balanced.valid treeBBlock11 = true := by decide +kernel

private theorem treeBBlock12_spec : (Balanced.rows treeBBlock12).length = 28 ∧
    Balanced.valid treeBBlock12 = true := by decide +kernel

private theorem treeBBlock13_spec : (Balanced.rows treeBBlock13).length = 28 ∧
    Balanced.valid treeBBlock13 = true := by decide +kernel

private theorem treeBBlock14_spec : (Balanced.rows treeBBlock14).length = 28 ∧
    Balanced.valid treeBBlock14 = true := by decide +kernel

private theorem treeBBlock15_spec : (Balanced.rows treeBBlock15).length = 28 ∧
    Balanced.valid treeBBlock15 = true := by decide +kernel

private theorem treeBBlock16_spec : (Balanced.rows treeBBlock16).length = 28 ∧
    Balanced.valid treeBBlock16 = true := by decide +kernel

private theorem treeBBlock17_spec : (Balanced.rows treeBBlock17).length = 28 ∧
    Balanced.valid treeBBlock17 = true := by decide +kernel

private theorem treeBBlock18_spec : (Balanced.rows treeBBlock18).length = 28 ∧
    Balanced.valid treeBBlock18 = true := by decide +kernel

private theorem treeBBlock19_spec : (Balanced.rows treeBBlock19).length = 28 ∧
    Balanced.valid treeBBlock19 = true := by decide +kernel

private theorem treeBBlock20_spec : (Balanced.rows treeBBlock20).length = 28 ∧
    Balanced.valid treeBBlock20 = true := by decide +kernel

private theorem treeBBlock21_spec : (Balanced.rows treeBBlock21).length = 28 ∧
    Balanced.valid treeBBlock21 = true := by decide +kernel

private theorem treeBBlock22_spec : (Balanced.rows treeBBlock22).length = 28 ∧
    Balanced.valid treeBBlock22 = true := by decide +kernel

private theorem treeBBlock23_spec : (Balanced.rows treeBBlock23).length = 28 ∧
    Balanced.valid treeBBlock23 = true := by decide +kernel

private theorem treeBBlock24_spec : (Balanced.rows treeBBlock24).length = 28 ∧
    Balanced.valid treeBBlock24 = true := by decide +kernel

private theorem treeBBlock25_spec : (Balanced.rows treeBBlock25).length = 28 ∧
    Balanced.valid treeBBlock25 = true := by decide +kernel

private theorem treeBBlock26_spec : (Balanced.rows treeBBlock26).length = 28 ∧
    Balanced.valid treeBBlock26 = true := by decide +kernel

private theorem treeBBlock27_spec : (Balanced.rows treeBBlock27).length = 28 ∧
    Balanced.valid treeBBlock27 = true := by decide +kernel

private theorem treeBBlock28_spec : (Balanced.rows treeBBlock28).length = 28 ∧
    Balanced.valid treeBBlock28 = true := by decide +kernel

private theorem treeBBlock29_spec : (Balanced.rows treeBBlock29).length = 28 ∧
    Balanced.valid treeBBlock29 = true := by decide +kernel

private theorem treeBBlock30_spec : (Balanced.rows treeBBlock30).length = 28 ∧
    Balanced.valid treeBBlock30 = true := by decide +kernel

private theorem treeBBlock31_spec : (Balanced.rows treeBBlock31).length = 28 ∧
    Balanced.valid treeBBlock31 = true := by decide +kernel

private theorem treeB_spec : (Balanced.rows treeB).length = 896 ∧
    Balanced.valid treeB = true :=
  Balanced.node_spec 448 448 _ _ (Balanced.node_spec 224 224 _ _ (Balanced.node_spec 112 112 _ _ (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeBBlock00_spec) (treeBBlock01_spec)) (Balanced.node_spec 28 28 _ _ (treeBBlock02_spec) (treeBBlock03_spec))) (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeBBlock04_spec) (treeBBlock05_spec)) (Balanced.node_spec 28 28 _ _ (treeBBlock06_spec) (treeBBlock07_spec)))) (Balanced.node_spec 112 112 _ _ (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeBBlock08_spec) (treeBBlock09_spec)) (Balanced.node_spec 28 28 _ _ (treeBBlock10_spec) (treeBBlock11_spec))) (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeBBlock12_spec) (treeBBlock13_spec)) (Balanced.node_spec 28 28 _ _ (treeBBlock14_spec) (treeBBlock15_spec))))) (Balanced.node_spec 224 224 _ _ (Balanced.node_spec 112 112 _ _ (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeBBlock16_spec) (treeBBlock17_spec)) (Balanced.node_spec 28 28 _ _ (treeBBlock18_spec) (treeBBlock19_spec))) (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeBBlock20_spec) (treeBBlock21_spec)) (Balanced.node_spec 28 28 _ _ (treeBBlock22_spec) (treeBBlock23_spec)))) (Balanced.node_spec 112 112 _ _ (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeBBlock24_spec) (treeBBlock25_spec)) (Balanced.node_spec 28 28 _ _ (treeBBlock26_spec) (treeBBlock27_spec))) (Balanced.node_spec 56 56 _ _ (Balanced.node_spec 28 28 _ _ (treeBBlock28_spec) (treeBBlock29_spec)) (Balanced.node_spec 28 28 _ _ (treeBBlock30_spec) (treeBBlock31_spec)))))

set_option maxRecDepth 4096 in
theorem treeB_rows : Balanced.rows treeB = generatorRowsB := by rfl

theorem treeB_valid : Balanced.valid treeB = true := treeB_spec.2

theorem treeB_length : (Balanced.rows treeB).length = 896 := treeB_spec.1

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
