module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.SpanningCriterion
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Arithmetic

/-!
# Efficient checking of coordinate reconstruction blocks

The generic `PackedBinaryRows.fastProduct` consumes coefficient bits by division
instead of repeatedly shifting from the original coefficient. Its existing
comparison theorem identifies it with the exact `ColumnCertificate.select`.
Checked consecutive blocks therefore provide the reconstruction premise of
`column_span_of_reconstruction` for the fixed published columns.

The second import contains only generic packed-row arithmetic; no Higman–Sims
matrix or representation is used. Source and bit conventions are recorded in
`../source/README.md`; certificate reproduction is in `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnSpanning

private theorem fastProduct_eq_select (a k : Nat) (xs : List Nat) :
    PackedBinaryRows.fastProduct (a / 2 ^ k) xs = ColumnCertificate.select a xs k := by
  rw [PackedBinaryRows.fastProduct_eq_listProduct]
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => simp only [PackedBinaryRows.listProduct, ColumnCertificate.select, ih]

/-- Check a consecutive block of coefficient rows against the fixed columns. -/
def check (xs : List Nat) : Nat → List Nat → Bool
  | _, [] => true
  | c, a :: as => (PackedBinaryRows.fastProduct a xs == 2 ^ c) && check xs (c+1) as

private theorem check_eq (xs as : List Nat) (c : Nat) :
    check xs c as = ColumnCertificate.checkReconstructions xs c as := by
  induction as generalizing c with
  | nil => rfl
  | cons a as ih =>
    have ha : PackedBinaryRows.fastProduct a xs = ColumnCertificate.select a xs 0 := by
      simpa only [Nat.pow_zero, Nat.div_one] using fastProduct_eq_select a 0 xs
    simp only [check, ColumnCertificate.checkReconstructions, ha, ih]

/-- Every coordinate in an interval has a reconstruction from the literal columns. -/
def Covers (start count : Nat) : Prop :=
  ∀ i, start ≤ i → i < start + count →
    ∃ a, ColumnCertificate.select a ColumnData.columns 0 = 2 ^ i

/-- A kernel-checked block supplies the actual coordinate reconstructions. -/
theorem covers_of_check (as : List Nat) (start count : Nat)
    (hlen : as.length = count) (h : check ColumnData.columns start as = true) :
    Covers start count := by
  intro i hlo hhi
  refine ⟨as[i-start]!, ?_⟩
  have hc := ColumnCertificate.checkReconstructions_sound ColumnData.columns as start
    ((check_eq ColumnData.columns as start) ▸ h) (i-start) (by omega)
  simpa only [Nat.add_sub_of_le hlo] using hc

/-- Join adjacent coordinate intervals without recomputing their certificates. -/
theorem covers_join (start m n : Nat) (hm : Covers start m)
    (hn : Covers (start+m) n) : Covers start (m+n) := by
  intro i hlo hhi
  by_cases h : i < start+m
  · exact hm i hlo h
  · exact hn i (by omega) (by omega)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnSpanning
