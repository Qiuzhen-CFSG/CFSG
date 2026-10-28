module

public import Theory.Representation.BinaryCubicPairs.Data

/-!
# Exhaustive verification of cubic-pair word certificates

All 65,536 binary four-by-four matrices are checked in 64 bounded blocks.
The cubic, rank-two, full-support and noncommuting predicates select exactly
the cases needed by the representation argument. The table is never assumed
complete: every selected matrix must supply a checked involution word.

The blocks are deliberately elaborated sequentially. A representative largest
block uses 2.31 GiB peak RSS including Lake and imports, with 15 seconds of
kernel checking. Source application: Aschbacher--Smith E.6.24, p.255.
-/

set_option Elab.async false
public section
namespace BinaryCubicPairs.Packed

set_option maxRecDepth 4000 in
private theorem check0 : block 0 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check1 : block 1 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check2 : block 2 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check3 : block 3 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check4 : block 4 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check5 : block 5 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check6 : block 6 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check7 : block 7 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check8 : block 8 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check9 : block 9 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check10 : block 10 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check11 : block 11 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check12 : block 12 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check13 : block 13 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check14 : block 14 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check15 : block 15 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check16 : block 16 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check17 : block 17 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check18 : block 18 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check19 : block 19 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check20 : block 20 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check21 : block 21 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check22 : block 22 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check23 : block 23 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check24 : block 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check25 : block 25 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check26 : block 26 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check27 : block 27 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check28 : block 28 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check29 : block 29 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check30 : block 30 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check31 : block 31 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check32 : block 32 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check33 : block 33 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check34 : block 34 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check35 : block 35 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check36 : block 36 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check37 : block 37 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check38 : block 38 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check39 : block 39 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check40 : block 40 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check41 : block 41 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check42 : block 42 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check43 : block 43 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check44 : block 44 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check45 : block 45 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check46 : block 46 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check47 : block 47 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check48 : block 48 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check49 : block 49 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check50 : block 50 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check51 : block 51 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check52 : block 52 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check53 : block 53 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check54 : block 54 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check55 : block 55 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check56 : block 56 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check57 : block 57 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check58 : block 58 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check59 : block 59 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check60 : block 60 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check61 : block 61 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check62 : block 62 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check63 : block 63 = true := by decide +kernel

private theorem all_blocks (i : Fin 64) : block i.val = true := by
  fin_cases i
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
  · exact check21
  · exact check22
  · exact check23
  · exact check24
  · exact check25
  · exact check26
  · exact check27
  · exact check28
  · exact check29
  · exact check30
  · exact check31
  · exact check32
  · exact check33
  · exact check34
  · exact check35
  · exact check36
  · exact check37
  · exact check38
  · exact check39
  · exact check40
  · exact check41
  · exact check42
  · exact check43
  · exact check44
  · exact check45
  · exact check46
  · exact check47
  · exact check48
  · exact check49
  · exact check50
  · exact check51
  · exact check52
  · exact check53
  · exact check54
  · exact check55
  · exact check56
  · exact check57
  · exact check58
  · exact check59
  · exact check60
  · exact check61
  · exact check62
  · exact check63

/-- Every matrix satisfying the original finite predicate has a checked
word certificate, including both orientations of every cyclic actor. -/
theorem exists_certificate (d : BitVec 16) (hd : readyB d = true) :
    ∃ k : Certificate, Valid d k := by
  let i : Fin 64 := ⟨d.toNat / 1024, by have := d.isLt; omega⟩
  have hj : d.toNat % 1024 < 1024 := Nat.mod_lt _ (by decide)
  have hh := List.all_eq_true.mp (all_blocks i) (d.toNat % 1024)
    (List.mem_range.mpr hj)
  have he : 1024 * i.val + d.toNat % 1024 = d.toNat := by
    dsimp only [i]
    omega
  change checkB (1024 * i.val + d.toNat % 1024) = true at hh
  rw [he] at hh
  simp only [checkB, BitVec.ofNat_toNat, BitVec.setWidth_eq, hd, Bool.not_true,
    Bool.false_or] at hh
  exact ⟨lookup d, valid_of_check hh⟩

end BinaryCubicPairs.Packed
