module

public import Theory.SpecificGroups.Held.TwoRank.Coloring.Data

/-!
# Checking the Held outside-action table

The 2058 letters are checked in overlapping blocks of 64. This bounds peak
kernel-checking memory while proving the same pointwise equality with the
sixteen-letter correction times the existing outer involution.
Source: ATLAS HeG1-p2058B0 and HeG1-a2W1; `Source/generate.py`.
-/

public section
namespace Held.TwoRank.Coloring

set_option maxRecDepth 8192 in
private theorem cache00 : ∀ j : Fin 64,
    outsideAction ⟨(0 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(0 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache01 : ∀ j : Fin 64,
    outsideAction ⟨(1 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(1 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache02 : ∀ j : Fin 64,
    outsideAction ⟨(2 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(2 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache03 : ∀ j : Fin 64,
    outsideAction ⟨(3 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(3 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache04 : ∀ j : Fin 64,
    outsideAction ⟨(4 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(4 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache05 : ∀ j : Fin 64,
    outsideAction ⟨(5 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(5 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache06 : ∀ j : Fin 64,
    outsideAction ⟨(6 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(6 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache07 : ∀ j : Fin 64,
    outsideAction ⟨(7 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(7 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache08 : ∀ j : Fin 64,
    outsideAction ⟨(8 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(8 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache09 : ∀ j : Fin 64,
    outsideAction ⟨(9 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(9 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache10 : ∀ j : Fin 64,
    outsideAction ⟨(10 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(10 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache11 : ∀ j : Fin 64,
    outsideAction ⟨(11 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(11 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache12 : ∀ j : Fin 64,
    outsideAction ⟨(12 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(12 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache13 : ∀ j : Fin 64,
    outsideAction ⟨(13 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(13 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache14 : ∀ j : Fin 64,
    outsideAction ⟨(14 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(14 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache15 : ∀ j : Fin 64,
    outsideAction ⟨(15 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(15 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache16 : ∀ j : Fin 64,
    outsideAction ⟨(16 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(16 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache17 : ∀ j : Fin 64,
    outsideAction ⟨(17 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(17 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache18 : ∀ j : Fin 64,
    outsideAction ⟨(18 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(18 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache19 : ∀ j : Fin 64,
    outsideAction ⟨(19 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(19 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache20 : ∀ j : Fin 64,
    outsideAction ⟨(20 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(20 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache21 : ∀ j : Fin 64,
    outsideAction ⟨(21 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(21 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache22 : ∀ j : Fin 64,
    outsideAction ⟨(22 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(22 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache23 : ∀ j : Fin 64,
    outsideAction ⟨(23 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(23 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache24 : ∀ j : Fin 64,
    outsideAction ⟨(24 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(24 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache25 : ∀ j : Fin 64,
    outsideAction ⟨(25 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(25 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache26 : ∀ j : Fin 64,
    outsideAction ⟨(26 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(26 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache27 : ∀ j : Fin 64,
    outsideAction ⟨(27 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(27 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache28 : ∀ j : Fin 64,
    outsideAction ⟨(28 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(28 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache29 : ∀ j : Fin 64,
    outsideAction ⟨(29 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(29 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache30 : ∀ j : Fin 64,
    outsideAction ⟨(30 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(30 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache31 : ∀ j : Fin 64,
    outsideAction ⟨(31 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(31 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem cache32 : ∀ j : Fin 64,
    outsideAction ⟨(32 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(32 * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

private theorem cache (i : Fin 33) : ∀ j : Fin 64,
    outsideAction ⟨(i.val * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ =
      outside.val ⟨(i.val * 64 + j.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  fin_cases i
  · exact cache00
  · exact cache01
  · exact cache02
  · exact cache03
  · exact cache04
  · exact cache05
  · exact cache06
  · exact cache07
  · exact cache08
  · exact cache09
  · exact cache10
  · exact cache11
  · exact cache12
  · exact cache13
  · exact cache14
  · exact cache15
  · exact cache16
  · exact cache17
  · exact cache18
  · exact cache19
  · exact cache20
  · exact cache21
  · exact cache22
  · exact cache23
  · exact cache24
  · exact cache25
  · exact cache26
  · exact cache27
  · exact cache28
  · exact cache29
  · exact cache30
  · exact cache31
  · exact cache32

/-- The finite lookup function is the actual outside element's action. -/
theorem outsideAction_eq (x : Fin 2058) : outsideAction x = outside.val x := by
  have h := cache ⟨x.val / 64, by omega⟩ ⟨x.val % 64, Nat.mod_lt _ (by decide)⟩
  have hi : (x.val / 64 * 64 + x.val % 64) % 2058 = x.val := by omega
  simpa only [hi] using h

end Held.TwoRank.Coloring
