module

public import Theory.Representation.BinaryCubicPairs.NormalizationData

/-!
# Verified coordinates for all binary rank-two cubics

Every one of the 65,536 binary four-by-four matrices is checked. Cubic
matrices with four fixed vectors receive a verified invertible coordinate
change to the standard rank-two cubic. The witnesses in the data module
are checked, not assumed. The bounded blocks are elaborated sequentially.

Source application: Aschbacher--Smith E.6.24, printed p.255.
-/

set_option Elab.async false
public section
namespace BinaryCubicPairs.Packed

set_option maxRecDepth 4000 in
private theorem check0 : normalizationBlock 0 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check1 : normalizationBlock 1 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check2 : normalizationBlock 2 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check3 : normalizationBlock 3 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check4 : normalizationBlock 4 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check5 : normalizationBlock 5 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check6 : normalizationBlock 6 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check7 : normalizationBlock 7 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check8 : normalizationBlock 8 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check9 : normalizationBlock 9 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check10 : normalizationBlock 10 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check11 : normalizationBlock 11 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check12 : normalizationBlock 12 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check13 : normalizationBlock 13 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check14 : normalizationBlock 14 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check15 : normalizationBlock 15 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check16 : normalizationBlock 16 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check17 : normalizationBlock 17 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check18 : normalizationBlock 18 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check19 : normalizationBlock 19 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check20 : normalizationBlock 20 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check21 : normalizationBlock 21 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check22 : normalizationBlock 22 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check23 : normalizationBlock 23 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check24 : normalizationBlock 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check25 : normalizationBlock 25 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check26 : normalizationBlock 26 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check27 : normalizationBlock 27 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check28 : normalizationBlock 28 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check29 : normalizationBlock 29 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check30 : normalizationBlock 30 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check31 : normalizationBlock 31 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check32 : normalizationBlock 32 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check33 : normalizationBlock 33 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check34 : normalizationBlock 34 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check35 : normalizationBlock 35 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check36 : normalizationBlock 36 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check37 : normalizationBlock 37 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check38 : normalizationBlock 38 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check39 : normalizationBlock 39 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check40 : normalizationBlock 40 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check41 : normalizationBlock 41 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check42 : normalizationBlock 42 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check43 : normalizationBlock 43 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check44 : normalizationBlock 44 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check45 : normalizationBlock 45 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check46 : normalizationBlock 46 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check47 : normalizationBlock 47 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check48 : normalizationBlock 48 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check49 : normalizationBlock 49 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check50 : normalizationBlock 50 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check51 : normalizationBlock 51 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check52 : normalizationBlock 52 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check53 : normalizationBlock 53 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check54 : normalizationBlock 54 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check55 : normalizationBlock 55 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check56 : normalizationBlock 56 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check57 : normalizationBlock 57 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check58 : normalizationBlock 58 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check59 : normalizationBlock 59 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check60 : normalizationBlock 60 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check61 : normalizationBlock 61 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check62 : normalizationBlock 62 = true := by decide +kernel

set_option maxRecDepth 4000 in
private theorem check63 : normalizationBlock 63 = true := by decide +kernel

private theorem all_blocks (i : Fin 64) : normalizationBlock i.val = true := by
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

/-- The original matrix is put in standard cubic coordinates by a
verified pair of inverse matrices. -/
theorem exists_normalization (a : BitVec 16) (ha : cubicB a = true) :
    ∃ g h : BitVec 16, mm g h = ident ∧ mm h g = ident ∧
      mm (mm g a) h = cubic := by
  let i : Fin 64 := ⟨a.toNat / 1024, by have := a.isLt; omega⟩
  have hj : a.toNat % 1024 < 1024 := Nat.mod_lt _ (by decide)
  have hh := List.all_eq_true.mp (all_blocks i) (a.toNat % 1024)
    (List.mem_range.mpr hj)
  have he : 1024 * i.val + a.toNat % 1024 = a.toNat := by
    dsimp only [i]
    omega
  change normalizationCheck (1024 * i.val + a.toNat % 1024) = true at hh
  rw [he] at hh
  simp only [normalizationCheck, BitVec.ofNat_toNat, BitVec.setWidth_eq, ha,
    Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hh
  exact ⟨(normalization a).1, (normalization a).2, hh.1.1, hh.1.2, hh.2⟩

end BinaryCubicPairs.Packed
