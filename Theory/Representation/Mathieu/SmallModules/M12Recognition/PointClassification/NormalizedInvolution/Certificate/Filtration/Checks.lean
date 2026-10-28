module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.Filtration.Witness

/-!
# Kernel checks for the 300 adapted columns

Each bounded batch checks ten inverse columns, both intertwining columns,
and the corresponding diagonal slices and lower-block vanishing. Natural
number XOR, shift and remainder are evaluated by the Lean kernel.
The one-column prototype was benchmarked before generating these batches.
Source witnesses: `../source/filtration.json`; see `source/export.py`.
-/

-- Keep the large closed reductions sequential within this compilation unit.
set_option Elab.async false

@[expose] public section
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.CertificateFiltration
open Packed

def columnCertificate (j : ℕ) : Prop :=
  combineList inverseColumns basisColumns[j]! = 2 ^ j ∧
  (∀ s : Fin 2, combineList (originalColumns s) basisColumns[j]! =
    combineList basisColumns (transformedColumns s)[j]!) ∧
  (∀ s : Fin 2, (transformedColumns s)[j]! >>> (100 * (j / 100 + 1)) = 0) ∧
  (∀ s : Fin 2, ((transformedColumns s)[j]! >>> (100 * (j / 100))) % 2 ^ 100 =
    pointColumns s ⟨j % 10, Nat.mod_lt _ (by decide)⟩ <<< (10 * ((j % 100) / 10)))

private theorem batch0 : ∀ k : Fin 10, columnCertificate (0 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch1 : ∀ k : Fin 10, columnCertificate (10 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch2 : ∀ k : Fin 10, columnCertificate (20 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch3 : ∀ k : Fin 10, columnCertificate (30 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch4 : ∀ k : Fin 10, columnCertificate (40 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch5 : ∀ k : Fin 10, columnCertificate (50 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch6 : ∀ k : Fin 10, columnCertificate (60 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch7 : ∀ k : Fin 10, columnCertificate (70 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch8 : ∀ k : Fin 10, columnCertificate (80 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch9 : ∀ k : Fin 10, columnCertificate (90 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch10 : ∀ k : Fin 10, columnCertificate (100 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch11 : ∀ k : Fin 10, columnCertificate (110 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch12 : ∀ k : Fin 10, columnCertificate (120 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch13 : ∀ k : Fin 10, columnCertificate (130 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch14 : ∀ k : Fin 10, columnCertificate (140 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch15 : ∀ k : Fin 10, columnCertificate (150 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch16 : ∀ k : Fin 10, columnCertificate (160 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch17 : ∀ k : Fin 10, columnCertificate (170 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch18 : ∀ k : Fin 10, columnCertificate (180 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch19 : ∀ k : Fin 10, columnCertificate (190 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch20 : ∀ k : Fin 10, columnCertificate (200 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch21 : ∀ k : Fin 10, columnCertificate (210 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch22 : ∀ k : Fin 10, columnCertificate (220 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch23 : ∀ k : Fin 10, columnCertificate (230 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch24 : ∀ k : Fin 10, columnCertificate (240 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch25 : ∀ k : Fin 10, columnCertificate (250 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch26 : ∀ k : Fin 10, columnCertificate (260 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch27 : ∀ k : Fin 10, columnCertificate (270 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch28 : ∀ k : Fin 10, columnCertificate (280 + k.val) := by
  unfold columnCertificate
  decide +kernel
private theorem batch29 : ∀ k : Fin 10, columnCertificate (290 + k.val) := by
  unfold columnCertificate
  decide +kernel

/-- All 300 inverse, intertwining, and block identities, with no quotient premise. -/
theorem all_columns (j : Fin 300) : columnCertificate j.val := by
  have all (b : Fin 30) (k : Fin 10) : columnCertificate (10 * b.val + k.val) := by
    fin_cases b
    · exact batch0 k
    · exact batch1 k
    · exact batch2 k
    · exact batch3 k
    · exact batch4 k
    · exact batch5 k
    · exact batch6 k
    · exact batch7 k
    · exact batch8 k
    · exact batch9 k
    · exact batch10 k
    · exact batch11 k
    · exact batch12 k
    · exact batch13 k
    · exact batch14 k
    · exact batch15 k
    · exact batch16 k
    · exact batch17 k
    · exact batch18 k
    · exact batch19 k
    · exact batch20 k
    · exact batch21 k
    · exact batch22 k
    · exact batch23 k
    · exact batch24 k
    · exact batch25 k
    · exact batch26 k
    · exact batch27 k
    · exact batch28 k
    · exact batch29 k
  have h := all ⟨j.val / 10, by omega⟩ ⟨j.val % 10, Nat.mod_lt _ (by decide)⟩
  change columnCertificate (10 * (j.val / 10) + j.val % 10) at h
  rwa [show 10 * (j.val / 10) + j.val % 10 = j.val by omega] at h
end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.CertificateFiltration
