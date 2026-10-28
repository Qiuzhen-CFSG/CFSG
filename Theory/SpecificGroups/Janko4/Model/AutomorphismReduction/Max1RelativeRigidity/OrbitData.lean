module
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Data
import Mathlib.Tactic.FinCases
/-!
# A checked membership predicate for the orbit of mask three

The bit set is untrusted discovery data. Kernel-checked bounded certificates
show that both actual generator mask maps preserve membership, that parent
edges in the existing orbit tree preserve it, and that exactly 1771 masks
belong. `PairOrbit` transfers these statements to the actual subgroup action.
No search program is part of the trust boundary.

Input tables and parent tree: the ATLAS `J4G1-max1W1` certificates in
`KernelCount.Tables` and `Max1Fusion.KernelOrbits.Data`.
-/

@[expose] public section
namespace Janko4.Max1RelativeRigidity.OrbitData
open Cardinality.KernelCount Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.KernelOrbits
def orbitBits : Nat := 26257567233543845581735372697882066349717471941159671691124225773230737812420743461912914181787551123733098508271031792109037890754647881949970436161859322498136379900376499239168688747303054962605809403665273935870042181034766751028395018727306643438980268900629510745955606133273409825779485283550929437030124453657225627863521260509285993983202061254828251553011522440119926064931081531265024974815248430959423037126567073000042425311545953024512730480640895755825056056439645434192656432407840198598055479489562475389256115379703314959303805930931136484468706464604793734287320903458311453282460887008868625743592
def inPairOrbit (m : Nat) : Bool := orbitBits.testBit m
def Valid (m : Fin 2048) : Prop :=
  maskImage xMasks m.val < 2048 ∧ maskImage yMasks m.val < 2048 ∧
  inPairOrbit (maskImage xMasks m.val) = inPairOrbit m.val ∧
  inPairOrbit (maskImage yMasks m.val) = inPairOrbit m.val ∧
  inPairOrbit (parent m).val = inPairOrbit m.val
instance (m : Fin 2048) : Decidable (Valid m) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))
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

theorem certificate (m : Fin 2048) : Valid m := by
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
  convert h ⟨m.val / 64, by omega⟩ ⟨m.val % 64, Nat.mod_lt _ (by decide)⟩ using 1
  apply Fin.ext
  exact (Nat.div_add_mod m.val 64).symm

/-- The masks marked as lying in the orbit of the kernel pair. -/
abbrev PairMask := {m : Fin 2048 // inPairOrbit m.val = true}

theorem zero_not_mem : inPairOrbit 0 = false := by decide +kernel
theorem one_not_mem : inPairOrbit 1 = false := by decide +kernel
theorem three_mem : inPairOrbit 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
theorem pairMask_card : Nat.card PairMask = 1771 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
end Janko4.Max1RelativeRigidity.OrbitData
