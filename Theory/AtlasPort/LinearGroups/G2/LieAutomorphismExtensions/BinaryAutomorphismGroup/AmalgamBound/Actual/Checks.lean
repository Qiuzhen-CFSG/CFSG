module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.Actual.Coordinates
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.Data

/-!
# Checked actions of the binary amalgam generators

The literal root words act on the packed matrix columns exactly as specified
by the published tables. Word multiplication is checked as a table computation;
`ActionTable` then proves multiplication in the actual octonion group. Checks
are divided into sixteen-row blocks to bound kernel reduction memory. Labels
are distinct 64-bit integers, so column equality separates the actual rows.

Coordinates: Gerald Höhn and the ATLAS contributors, ATLAS Research and
Attribution License 1.0 (`LICENSES/ATLAS.txt`), as in `Data` and its diagnostic
`source/generate.py`. All identities here are independently kernel checked.
Source application: Aschbacher--Smith F.1.12 and Definition F.4.3.
-/

@[expose] public section
open Atlas.G2 Atlas.SplitOctonion
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.Actual
set_option maxRecDepth 4096

def commonGenerator : Model (ZMod 2) := rootC 1 * rootE 1 * rootF 1

def leftGenerator : Model (ZMod 2) := rootF 1 * weylS

def rightGenerator : Model (ZMod 2) := rootE 1 * weylR

private theorem left_step_0 : ∀ (i : Fin 16) (b : Bool) (c r : Fin 8),
    (if b then leftGenerator else commonGenerator).val
      (column leftTable (block 0 i) c) r =
    column leftTable (leftTable.mul (if b then 2 else 1) (block 0 i)) c r := by
  decide +kernel

private theorem left_product_0 : ∀ (i : Fin 16) (j : Fin 96),
    leftTable.mul (block 0 i) j =
      evalFrom leftTable j (leftTable.word (block 0 i)) := by
  decide +kernel

private theorem left_step_1 : ∀ (i : Fin 16) (b : Bool) (c r : Fin 8),
    (if b then leftGenerator else commonGenerator).val
      (column leftTable (block 1 i) c) r =
    column leftTable (leftTable.mul (if b then 2 else 1) (block 1 i)) c r := by
  decide +kernel

private theorem left_product_1 : ∀ (i : Fin 16) (j : Fin 96),
    leftTable.mul (block 1 i) j =
      evalFrom leftTable j (leftTable.word (block 1 i)) := by
  decide +kernel

private theorem left_step_2 : ∀ (i : Fin 16) (b : Bool) (c r : Fin 8),
    (if b then leftGenerator else commonGenerator).val
      (column leftTable (block 2 i) c) r =
    column leftTable (leftTable.mul (if b then 2 else 1) (block 2 i)) c r := by
  decide +kernel

private theorem left_product_2 : ∀ (i : Fin 16) (j : Fin 96),
    leftTable.mul (block 2 i) j =
      evalFrom leftTable j (leftTable.word (block 2 i)) := by
  decide +kernel

private theorem left_step_3 : ∀ (i : Fin 16) (b : Bool) (c r : Fin 8),
    (if b then leftGenerator else commonGenerator).val
      (column leftTable (block 3 i) c) r =
    column leftTable (leftTable.mul (if b then 2 else 1) (block 3 i)) c r := by
  decide +kernel

private theorem left_product_3 : ∀ (i : Fin 16) (j : Fin 96),
    leftTable.mul (block 3 i) j =
      evalFrom leftTable j (leftTable.word (block 3 i)) := by
  decide +kernel

private theorem left_step_4 : ∀ (i : Fin 16) (b : Bool) (c r : Fin 8),
    (if b then leftGenerator else commonGenerator).val
      (column leftTable (block 4 i) c) r =
    column leftTable (leftTable.mul (if b then 2 else 1) (block 4 i)) c r := by
  decide +kernel

private theorem left_product_4 : ∀ (i : Fin 16) (j : Fin 96),
    leftTable.mul (block 4 i) j =
      evalFrom leftTable j (leftTable.word (block 4 i)) := by
  decide +kernel

private theorem left_step_5 : ∀ (i : Fin 16) (b : Bool) (c r : Fin 8),
    (if b then leftGenerator else commonGenerator).val
      (column leftTable (block 5 i) c) r =
    column leftTable (leftTable.mul (if b then 2 else 1) (block 5 i)) c r := by
  decide +kernel

private theorem left_product_5 : ∀ (i : Fin 16) (j : Fin 96),
    leftTable.mul (block 5 i) j =
      evalFrom leftTable j (leftTable.word (block 5 i)) := by
  decide +kernel

theorem left_label_bound : ∀ i, leftTable.label i < 2^64 := by decide +kernel

private theorem left_label_injective : Function.Injective leftTable.label := by
  decide +kernel

theorem left_action : ActionTable leftTable commonGenerator leftGenerator where
  zero := by
    have h : ∀ c r : Fin 8, column leftTable 0 c r = basisVector c r := by decide +kernel
    exact fun c => funext (h c)
  step := by
    have h : ∀ (i : Fin 96) (b : Bool) (c r : Fin 8),
        (if b then leftGenerator else commonGenerator).val (column leftTable i c) r =
        column leftTable (leftTable.mul (if b then 2 else 1) i) c r := by
      apply forall_blocks
      intro k
      fin_cases k
      · exact left_step_0
      · exact left_step_1
      · exact left_step_2
      · exact left_step_3
      · exact left_step_4
      · exact left_step_5
    exact fun b i c => funext (h i b c)
  word_zero := rfl
  product := by
    apply forall_blocks
    intro k
    fin_cases k
    · exact left_product_0
    · exact left_product_1
    · exact left_product_2
    · exact left_product_3
    · exact left_product_4
    · exact left_product_5
  separate i j h := left_label_injective
    (labels_eq (left_label_bound i) (left_label_bound j) h)

private theorem right_step_0 : ∀ (i : Fin 16) (b : Bool) (c r : Fin 8),
    (if b then rightGenerator else commonGenerator).val
      (column rightTable (block 0 i) c) r =
    column rightTable (rightTable.mul (if b then 2 else 1) (block 0 i)) c r := by
  decide +kernel

private theorem right_product_0 : ∀ (i : Fin 16) (j : Fin 96),
    rightTable.mul (block 0 i) j =
      evalFrom rightTable j (rightTable.word (block 0 i)) := by
  decide +kernel

private theorem right_step_1 : ∀ (i : Fin 16) (b : Bool) (c r : Fin 8),
    (if b then rightGenerator else commonGenerator).val
      (column rightTable (block 1 i) c) r =
    column rightTable (rightTable.mul (if b then 2 else 1) (block 1 i)) c r := by
  decide +kernel

private theorem right_product_1 : ∀ (i : Fin 16) (j : Fin 96),
    rightTable.mul (block 1 i) j =
      evalFrom rightTable j (rightTable.word (block 1 i)) := by
  decide +kernel

private theorem right_step_2 : ∀ (i : Fin 16) (b : Bool) (c r : Fin 8),
    (if b then rightGenerator else commonGenerator).val
      (column rightTable (block 2 i) c) r =
    column rightTable (rightTable.mul (if b then 2 else 1) (block 2 i)) c r := by
  decide +kernel

private theorem right_product_2 : ∀ (i : Fin 16) (j : Fin 96),
    rightTable.mul (block 2 i) j =
      evalFrom rightTable j (rightTable.word (block 2 i)) := by
  decide +kernel

private theorem right_step_3 : ∀ (i : Fin 16) (b : Bool) (c r : Fin 8),
    (if b then rightGenerator else commonGenerator).val
      (column rightTable (block 3 i) c) r =
    column rightTable (rightTable.mul (if b then 2 else 1) (block 3 i)) c r := by
  decide +kernel

private theorem right_product_3 : ∀ (i : Fin 16) (j : Fin 96),
    rightTable.mul (block 3 i) j =
      evalFrom rightTable j (rightTable.word (block 3 i)) := by
  decide +kernel

private theorem right_step_4 : ∀ (i : Fin 16) (b : Bool) (c r : Fin 8),
    (if b then rightGenerator else commonGenerator).val
      (column rightTable (block 4 i) c) r =
    column rightTable (rightTable.mul (if b then 2 else 1) (block 4 i)) c r := by
  decide +kernel

private theorem right_product_4 : ∀ (i : Fin 16) (j : Fin 96),
    rightTable.mul (block 4 i) j =
      evalFrom rightTable j (rightTable.word (block 4 i)) := by
  decide +kernel

private theorem right_step_5 : ∀ (i : Fin 16) (b : Bool) (c r : Fin 8),
    (if b then rightGenerator else commonGenerator).val
      (column rightTable (block 5 i) c) r =
    column rightTable (rightTable.mul (if b then 2 else 1) (block 5 i)) c r := by
  decide +kernel

private theorem right_product_5 : ∀ (i : Fin 16) (j : Fin 96),
    rightTable.mul (block 5 i) j =
      evalFrom rightTable j (rightTable.word (block 5 i)) := by
  decide +kernel

theorem right_label_bound : ∀ i, rightTable.label i < 2^64 := by decide +kernel

private theorem right_label_injective : Function.Injective rightTable.label := by
  decide +kernel

theorem right_action : ActionTable rightTable commonGenerator rightGenerator where
  zero := by
    have h : ∀ c r : Fin 8, column rightTable 0 c r = basisVector c r := by decide +kernel
    exact fun c => funext (h c)
  step := by
    have h : ∀ (i : Fin 96) (b : Bool) (c r : Fin 8),
        (if b then rightGenerator else commonGenerator).val (column rightTable i c) r =
        column rightTable (rightTable.mul (if b then 2 else 1) i) c r := by
      apply forall_blocks
      intro k
      fin_cases k
      · exact right_step_0
      · exact right_step_1
      · exact right_step_2
      · exact right_step_3
      · exact right_step_4
      · exact right_step_5
    exact fun b i c => funext (h i b c)
  word_zero := rfl
  product := by
    apply forall_blocks
    intro k
    fin_cases k
    · exact right_product_0
    · exact right_product_1
    · exact right_product_2
    · exact right_product_3
    · exact right_product_4
    · exact right_product_5
  separate i j h := right_label_injective
    (labels_eq (right_label_bound i) (right_label_bound j) h)

theorem overlap_labels : ∀ i,
    leftTable.label (leftTable.overlap i) = rightTable.label (rightTable.overlap i) := by
  decide +kernel

theorem left_overlap_injective : Function.Injective leftTable.overlap := by
  decide +kernel

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.Actual
