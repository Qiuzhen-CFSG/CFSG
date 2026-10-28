module

public import Theory.SpecificGroups.Suzuki.SchurEightUpper.LocalSetup
public import Theory.SpecificGroups.Suzuki.SchurEightUpper.KernelGeneration
public import Theory.SpecificGroups.Suzuki.SchurEightUpper.MixedPairing

/-!
# The exceptional Suzuki upper bound from local commutators

The constructed mixed commutator pairing and the field calculation bound the
actual third commutator subgroup by four. The kernel-generation theorem
identifies the covering kernel with that subgroup, giving the unconditional
exceptional upper bound. The full root preimage supplies the precise
local-lift witness used by the chapter assembly.

This proves the upper-bound part of Aschbacher--Smith I.1.3(5), printed
p.407/PDF p.418, and GLS3 §6.1 for the actual matrix group Sz(8). The
fourfold-cover construction and the exact E₄ identification are separate
parts of the chapter assembly. The conditional interfaces are retained.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace BenderSuzuki.MatrixGroups.SchurCover.EightLocal

/-- Apply the field calculation to the actual local third commutator. -/
theorem third_card_le_four_of_pairing (d : PairingData) : Nat.card ThirdCommutator ≤ 4 := by
  change Nat.card (Additive ThirdCommutator) ≤ 4
  exact EightPairing.card_le_four_of_generated
    (by simpa [Field, PFAppendixIII.BinaryGaloisField] using GaloisField.card 2 3 (by decide))
    d.pairing d.invariant d.jacobi d.generates

/-- The local pairing and kernel generation together give the required bound. -/
theorem kernel_card_le_four_of_pairing (d : PairingData) (hk : Kernel 1 ≤ ThirdCommutator) :
    Nat.card (Kernel 1) ≤ 4 := by
  rw [le_antisymm hk third_le_kernel]
  exact third_card_le_four_of_pairing d

/-- The full root preimage gives the literal witness consumed by
`exceptional_conclusions_of_rootLift`, under the two local construction inputs. -/
theorem exists_rootLift_of_pairing (d : PairingData) (hk : Kernel 1 ≤ ThirdCommutator) :
    ∃ H : Subgroup (CoverGroup 1), H.map projection = SuzukiRootSubgroup 1 ∧
      Nat.card (H ⊓ Kernel 1 : Subgroup (CoverGroup 1)) ≤ 4 := by
  refine ⟨RootPreimage, rootPreimage_map, ?_⟩
  rw [inf_eq_right.mpr ((SuzukiRootSubgroup 1).ker_le_comap projection)]
  exact kernel_card_le_four_of_pairing d hk

/-- The actual third commutator has at most four elements, by its constructed
mixed commutator pairing and the GF(8) torus and Jacobi calculation. -/
theorem third_card_le_four : Nat.card ThirdCommutator ≤ 4 :=
  third_card_le_four_of_pairing mixedPairingData

/-- The exceptional Suzuki multiplier upper bound for the kernel of the
literal universal projection onto `SuzukiMatrixGroup 1`. -/
theorem kernel_card_le_four : Nat.card (Kernel 1) ≤ 4 :=
  kernel_card_le_four_of_pairing mixedPairingData kernel_le_third

/-- The full root preimage is the local lift required by
`exceptional_conclusions_of_rootLift`, with both local premises discharged. -/
theorem exists_rootLift :
    ∃ H : Subgroup (CoverGroup 1),
      H.map (PerfectCentralCovering.universalProjection (SuzukiMatrixGroup 1)) =
        SuzukiRootSubgroup 1 ∧
      Nat.card (H ⊓ Kernel 1 : Subgroup (CoverGroup 1)) ≤ 4 :=
  exists_rootLift_of_pairing mixedPairingData kernel_le_third

end BenderSuzuki.MatrixGroups.SchurCover.EightLocal

end
