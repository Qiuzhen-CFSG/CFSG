module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarData
import Mathlib.Tactic.FinCases
/-!
# The fixed masks of the actual right action of xy

Only masks zero and one are fixed by the composite of the certified x and y
right-conjugation tables. Checking 32 blocks of 64 masks avoids a large
endomorphism-space computation. `Commutant` connects the finite computation
to actual equivariant kernel endomorphisms using normal generation by mask one.
The input tables come from literal ATLAS `J4G1-max1W1` through
`KernelCount.Tables`; every finite test is kernel checked.
-/
@[expose] public section
namespace Janko4.Max1RelativeRigidity.CommutantData
open Cardinality.KernelCount Cardinality.QuotientCount.Image
private def Valid (m : Fin 2048) : Prop :=
    maskImage yMasks (maskImage xMasks m.val) < 2048 ∧
    (maskImage yMasks (maskImage xMasks m.val) = m.val → m = 0 ∨ m = 1)
private instance (m : Fin 2048) : Decidable (Valid m) := inferInstanceAs (Decidable (_ ∧ _))
set_option maxRecDepth 10000 in
private theorem block0 : ∀ i : Fin 64, Valid ⟨0 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block1 : ∀ i : Fin 64, Valid ⟨64 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block2 : ∀ i : Fin 64, Valid ⟨128 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block3 : ∀ i : Fin 64, Valid ⟨192 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block4 : ∀ i : Fin 64, Valid ⟨256 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block5 : ∀ i : Fin 64, Valid ⟨320 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block6 : ∀ i : Fin 64, Valid ⟨384 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block7 : ∀ i : Fin 64, Valid ⟨448 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block8 : ∀ i : Fin 64, Valid ⟨512 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block9 : ∀ i : Fin 64, Valid ⟨576 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block10 : ∀ i : Fin 64, Valid ⟨640 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block11 : ∀ i : Fin 64, Valid ⟨704 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block12 : ∀ i : Fin 64, Valid ⟨768 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block13 : ∀ i : Fin 64, Valid ⟨832 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block14 : ∀ i : Fin 64, Valid ⟨896 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block15 : ∀ i : Fin 64, Valid ⟨960 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block16 : ∀ i : Fin 64, Valid ⟨1024 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block17 : ∀ i : Fin 64, Valid ⟨1088 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block18 : ∀ i : Fin 64, Valid ⟨1152 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block19 : ∀ i : Fin 64, Valid ⟨1216 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block20 : ∀ i : Fin 64, Valid ⟨1280 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block21 : ∀ i : Fin 64, Valid ⟨1344 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block22 : ∀ i : Fin 64, Valid ⟨1408 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block23 : ∀ i : Fin 64, Valid ⟨1472 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block24 : ∀ i : Fin 64, Valid ⟨1536 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block25 : ∀ i : Fin 64, Valid ⟨1600 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block26 : ∀ i : Fin 64, Valid ⟨1664 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block27 : ∀ i : Fin 64, Valid ⟨1728 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block28 : ∀ i : Fin 64, Valid ⟨1792 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block29 : ∀ i : Fin 64, Valid ⟨1856 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block30 : ∀ i : Fin 64, Valid ⟨1920 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block31 : ∀ i : Fin 64, Valid ⟨1984 + i.val, by omega⟩ := by
  decide +kernel

theorem xy_fixed_masks (m : Fin 2048) :
    maskImage yMasks (maskImage xMasks m.val) < 2048 ∧
    (maskImage yMasks (maskImage xMasks m.val) = m.val → m = 0 ∨ m = 1) := by
  have h : ∀ b : Fin 32, ∀ i : Fin 64, Valid ⟨64 * b.val + i.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact block0
    · exact block1
    · exact block2
    · exact block3
    · exact block4
    · exact block5
    · exact block6
    · exact block7
    · exact block8
    · exact block9
    · exact block10
    · exact block11
    · exact block12
    · exact block13
    · exact block14
    · exact block15
    · exact block16
    · exact block17
    · exact block18
    · exact block19
    · exact block20
    · exact block21
    · exact block22
    · exact block23
    · exact block24
    · exact block25
    · exact block26
    · exact block27
    · exact block28
    · exact block29
    · exact block30
    · exact block31
  change Valid m
  convert h ⟨m.val / 64, by omega⟩ ⟨m.val % 64, Nat.mod_lt _ (by decide)⟩ using 1
  apply Fin.ext
  exact (Nat.div_add_mod m.val 64).symm
end Janko4.Max1RelativeRigidity.CommutantData
