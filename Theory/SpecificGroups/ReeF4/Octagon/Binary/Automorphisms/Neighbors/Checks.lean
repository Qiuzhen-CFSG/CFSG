module

public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.Refinement.Common

/-!
# Checked neighbor rows of the finite binary octagon

Every recorded neighbor has the opposite type, lies in the finite carrier,
and records the reverse adjacency; each row has no duplicates. Bounded
kernel checks establish these facts on all 4680 rows. They identify the raw
lists used by the color certificate with the graph's actual neighbor sets.

Source: the building automorphism calculation used in Aschbacher--Smith
J.5.6, printed p.447, in the existing Parrott coset numbering.
-/

@[expose] public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteGraph

def RowValid (i : ℕ) : Prop :=
  (adjacency i).Nodup ∧ ∀ j ∈ adjacency i,
    j < 4680 ∧ ((i < 1755 ∧ 1755 ≤ j) ∨ (j < 1755 ∧ 1755 ≤ i)) ∧
      i ∈ adjacency j

private instance (i : ℕ) : Decidable (RowValid i) :=
  inferInstanceAs (Decidable ((adjacency i).Nodup ∧ ∀ j ∈ adjacency i,
    j < 4680 ∧ ((i < 1755 ∧ 1755 ≤ j) ∨ (j < 1755 ∧ 1755 ≤ i)) ∧
      i ∈ adjacency j))

set_option Elab.async false in
private theorem checked0 : ∀ i, 0 ≤ i → i < 128 → RowValid i :=
  Refinement.of_block RowValid 0 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked1 : ∀ i, 128 ≤ i → i < 256 → RowValid i :=
  Refinement.of_block RowValid 128 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked2 : ∀ i, 256 ≤ i → i < 384 → RowValid i :=
  Refinement.of_block RowValid 256 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked3 : ∀ i, 384 ≤ i → i < 512 → RowValid i :=
  Refinement.of_block RowValid 384 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked4 : ∀ i, 512 ≤ i → i < 640 → RowValid i :=
  Refinement.of_block RowValid 512 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked5 : ∀ i, 640 ≤ i → i < 768 → RowValid i :=
  Refinement.of_block RowValid 640 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked6 : ∀ i, 768 ≤ i → i < 896 → RowValid i :=
  Refinement.of_block RowValid 768 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked7 : ∀ i, 896 ≤ i → i < 1024 → RowValid i :=
  Refinement.of_block RowValid 896 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked8 : ∀ i, 1024 ≤ i → i < 1152 → RowValid i :=
  Refinement.of_block RowValid 1024 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked9 : ∀ i, 1152 ≤ i → i < 1280 → RowValid i :=
  Refinement.of_block RowValid 1152 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked10 : ∀ i, 1280 ≤ i → i < 1408 → RowValid i :=
  Refinement.of_block RowValid 1280 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked11 : ∀ i, 1408 ≤ i → i < 1536 → RowValid i :=
  Refinement.of_block RowValid 1408 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked12 : ∀ i, 1536 ≤ i → i < 1664 → RowValid i :=
  Refinement.of_block RowValid 1536 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked13 : ∀ i, 1664 ≤ i → i < 1792 → RowValid i :=
  Refinement.of_block RowValid 1664 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked14 : ∀ i, 1792 ≤ i → i < 1920 → RowValid i :=
  Refinement.of_block RowValid 1792 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked15 : ∀ i, 1920 ≤ i → i < 2048 → RowValid i :=
  Refinement.of_block RowValid 1920 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked16 : ∀ i, 2048 ≤ i → i < 2176 → RowValid i :=
  Refinement.of_block RowValid 2048 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked17 : ∀ i, 2176 ≤ i → i < 2304 → RowValid i :=
  Refinement.of_block RowValid 2176 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked18 : ∀ i, 2304 ≤ i → i < 2432 → RowValid i :=
  Refinement.of_block RowValid 2304 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked19 : ∀ i, 2432 ≤ i → i < 2560 → RowValid i :=
  Refinement.of_block RowValid 2432 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked20 : ∀ i, 2560 ≤ i → i < 2688 → RowValid i :=
  Refinement.of_block RowValid 2560 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked21 : ∀ i, 2688 ≤ i → i < 2816 → RowValid i :=
  Refinement.of_block RowValid 2688 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked22 : ∀ i, 2816 ≤ i → i < 2944 → RowValid i :=
  Refinement.of_block RowValid 2816 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked23 : ∀ i, 2944 ≤ i → i < 3072 → RowValid i :=
  Refinement.of_block RowValid 2944 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked24 : ∀ i, 3072 ≤ i → i < 3200 → RowValid i :=
  Refinement.of_block RowValid 3072 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked25 : ∀ i, 3200 ≤ i → i < 3328 → RowValid i :=
  Refinement.of_block RowValid 3200 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked26 : ∀ i, 3328 ≤ i → i < 3456 → RowValid i :=
  Refinement.of_block RowValid 3328 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked27 : ∀ i, 3456 ≤ i → i < 3584 → RowValid i :=
  Refinement.of_block RowValid 3456 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked28 : ∀ i, 3584 ≤ i → i < 3712 → RowValid i :=
  Refinement.of_block RowValid 3584 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked29 : ∀ i, 3712 ≤ i → i < 3840 → RowValid i :=
  Refinement.of_block RowValid 3712 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked30 : ∀ i, 3840 ≤ i → i < 3968 → RowValid i :=
  Refinement.of_block RowValid 3840 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked31 : ∀ i, 3968 ≤ i → i < 4096 → RowValid i :=
  Refinement.of_block RowValid 3968 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked32 : ∀ i, 4096 ≤ i → i < 4224 → RowValid i :=
  Refinement.of_block RowValid 4096 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked33 : ∀ i, 4224 ≤ i → i < 4352 → RowValid i :=
  Refinement.of_block RowValid 4224 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked34 : ∀ i, 4352 ≤ i → i < 4480 → RowValid i :=
  Refinement.of_block RowValid 4352 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked35 : ∀ i, 4480 ≤ i → i < 4608 → RowValid i :=
  Refinement.of_block RowValid 4480 128 (by decide +kernel)

set_option Elab.async false in
private theorem checked36 : ∀ i, 4608 ≤ i → i < 4680 → RowValid i :=
  Refinement.of_block RowValid 4608 72 (by decide +kernel)

/-- Every vertex has its checked finite, simple, symmetric neighbor row. -/
theorem row_valid (i : Vertex) : RowValid i.val :=
  (Refinement.join (mid := 2304) (Refinement.join (mid := 1152) (Refinement.join (mid := 512) (Refinement.join (mid := 256) (Refinement.join (mid := 128) checked0 checked1) (Refinement.join (mid := 384) checked2 checked3)) (Refinement.join (mid := 768) (Refinement.join (mid := 640) checked4 checked5) (Refinement.join (mid := 896) checked6 (Refinement.join (mid := 1024) checked7 checked8)))) (Refinement.join (mid := 1664) (Refinement.join (mid := 1408) (Refinement.join (mid := 1280) checked9 checked10) (Refinement.join (mid := 1536) checked11 checked12)) (Refinement.join (mid := 1920) (Refinement.join (mid := 1792) checked13 checked14) (Refinement.join (mid := 2048) checked15 (Refinement.join (mid := 2176) checked16 checked17))))) (Refinement.join (mid := 3456) (Refinement.join (mid := 2816) (Refinement.join (mid := 2560) (Refinement.join (mid := 2432) checked18 checked19) (Refinement.join (mid := 2688) checked20 checked21)) (Refinement.join (mid := 3072) (Refinement.join (mid := 2944) checked22 checked23) (Refinement.join (mid := 3200) checked24 (Refinement.join (mid := 3328) checked25 checked26)))) (Refinement.join (mid := 4096) (Refinement.join (mid := 3712) (Refinement.join (mid := 3584) checked27 checked28) (Refinement.join (mid := 3840) checked29 (Refinement.join (mid := 3968) checked30 checked31))) (Refinement.join (mid := 4352) (Refinement.join (mid := 4224) checked32 checked33) (Refinement.join (mid := 4480) checked34 (Refinement.join (mid := 4608) checked35 checked36)))))) i.val (Nat.zero_le _) i.isLt

end ReeF4.Octagon.Binary.Automorphisms.FiniteGraph
