module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality.Cover.Computation

/-!
# Certifying the fixed alignment tables

All 2,058 forward images agree with the literal conjugator word. The inverse
table is a left inverse on every point and therefore is the inverse of that
same permutation. This avoids re-evaluating the conjugator in all 4,831 rows.
Source: the two alignment words in ConcreteMaximality.Setup, preserving the
inverted ATLAS convention described in Held/Model/Source/README.md.
-/

namespace Held.RankOneLocalPair.ConcreteMaximality.CoverCertificate
open Held.TwoLocalCandidates
open Held.LocalPairs.PairCoverage.SylowOvergroups
open Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification

set_option Elab.async false

@[expose] public def conjugatorPermutation : Equiv.Perm (Fin 2058) :=
  wordEval fastA Cores.Tables0.p1 firstConjugatorWord *
    wordEval fastA fastB secondConjugatorWord

private theorem conjugatorAction_eq (p : Fin 2058) :
    conjugatorAction p = conjugatorPermutation p := by
  simp only [conjugatorAction, wordAction_eq]
  rfl

private def conjugatorCheck (start count : ℕ) : Bool :=
  (List.range count).all fun n =>
    let p : Fin 2058 := ⟨(start+n) % 2058, Nat.mod_lt _ (by decide)⟩
    conjugatorTable p == conjugatorAction p

private theorem conjugatorCheck_sound (start count : ℕ)
    (h : conjugatorCheck start count = true) (p : Fin 2058)
    (hlo : start ≤ p.val) (hhi : p.val < start + count) :
    conjugatorTable p = conjugatorAction p := by
  have he := List.all_eq_true.mp h (p.val-start)
    (List.mem_range.mpr (show p.val-start < count by omega))
  have hp : (⟨(start+(p.val-start)) % 2058, Nat.mod_lt _ (by decide)⟩ : Fin 2058) = p := by
    apply Fin.ext
    change (start+(p.val-start)) % 2058 = p.val
    omega
  simpa only [hp, beq_iff_eq] using he

set_option maxRecDepth 10000 in
private theorem conjugatorChecked0 : conjugatorCheck 0 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked64 : conjugatorCheck 64 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked128 : conjugatorCheck 128 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked192 : conjugatorCheck 192 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked256 : conjugatorCheck 256 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked320 : conjugatorCheck 320 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked384 : conjugatorCheck 384 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked448 : conjugatorCheck 448 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked512 : conjugatorCheck 512 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked576 : conjugatorCheck 576 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked640 : conjugatorCheck 640 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked704 : conjugatorCheck 704 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked768 : conjugatorCheck 768 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked832 : conjugatorCheck 832 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked896 : conjugatorCheck 896 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked960 : conjugatorCheck 960 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1024 : conjugatorCheck 1024 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1088 : conjugatorCheck 1088 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1152 : conjugatorCheck 1152 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1216 : conjugatorCheck 1216 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1280 : conjugatorCheck 1280 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1344 : conjugatorCheck 1344 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1408 : conjugatorCheck 1408 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1472 : conjugatorCheck 1472 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1536 : conjugatorCheck 1536 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1600 : conjugatorCheck 1600 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1664 : conjugatorCheck 1664 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1728 : conjugatorCheck 1728 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1792 : conjugatorCheck 1792 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1856 : conjugatorCheck 1856 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1920 : conjugatorCheck 1920 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked1984 : conjugatorCheck 1984 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem conjugatorChecked2048 : conjugatorCheck 2048 10 = true := by decide +kernel

public theorem conjugatorTable_eq (p : Fin 2058) :
    conjugatorTable p = conjugatorPermutation p := by
  rw [← conjugatorAction_eq]
  by_cases h0 : p.val < 64
  · exact conjugatorCheck_sound 0 64 conjugatorChecked0 p (by omega) h0
  by_cases h64 : p.val < 128
  · exact conjugatorCheck_sound 64 64 conjugatorChecked64 p (by omega) h64
  by_cases h128 : p.val < 192
  · exact conjugatorCheck_sound 128 64 conjugatorChecked128 p (by omega) h128
  by_cases h192 : p.val < 256
  · exact conjugatorCheck_sound 192 64 conjugatorChecked192 p (by omega) h192
  by_cases h256 : p.val < 320
  · exact conjugatorCheck_sound 256 64 conjugatorChecked256 p (by omega) h256
  by_cases h320 : p.val < 384
  · exact conjugatorCheck_sound 320 64 conjugatorChecked320 p (by omega) h320
  by_cases h384 : p.val < 448
  · exact conjugatorCheck_sound 384 64 conjugatorChecked384 p (by omega) h384
  by_cases h448 : p.val < 512
  · exact conjugatorCheck_sound 448 64 conjugatorChecked448 p (by omega) h448
  by_cases h512 : p.val < 576
  · exact conjugatorCheck_sound 512 64 conjugatorChecked512 p (by omega) h512
  by_cases h576 : p.val < 640
  · exact conjugatorCheck_sound 576 64 conjugatorChecked576 p (by omega) h576
  by_cases h640 : p.val < 704
  · exact conjugatorCheck_sound 640 64 conjugatorChecked640 p (by omega) h640
  by_cases h704 : p.val < 768
  · exact conjugatorCheck_sound 704 64 conjugatorChecked704 p (by omega) h704
  by_cases h768 : p.val < 832
  · exact conjugatorCheck_sound 768 64 conjugatorChecked768 p (by omega) h768
  by_cases h832 : p.val < 896
  · exact conjugatorCheck_sound 832 64 conjugatorChecked832 p (by omega) h832
  by_cases h896 : p.val < 960
  · exact conjugatorCheck_sound 896 64 conjugatorChecked896 p (by omega) h896
  by_cases h960 : p.val < 1024
  · exact conjugatorCheck_sound 960 64 conjugatorChecked960 p (by omega) h960
  by_cases h1024 : p.val < 1088
  · exact conjugatorCheck_sound 1024 64 conjugatorChecked1024 p (by omega) h1024
  by_cases h1088 : p.val < 1152
  · exact conjugatorCheck_sound 1088 64 conjugatorChecked1088 p (by omega) h1088
  by_cases h1152 : p.val < 1216
  · exact conjugatorCheck_sound 1152 64 conjugatorChecked1152 p (by omega) h1152
  by_cases h1216 : p.val < 1280
  · exact conjugatorCheck_sound 1216 64 conjugatorChecked1216 p (by omega) h1216
  by_cases h1280 : p.val < 1344
  · exact conjugatorCheck_sound 1280 64 conjugatorChecked1280 p (by omega) h1280
  by_cases h1344 : p.val < 1408
  · exact conjugatorCheck_sound 1344 64 conjugatorChecked1344 p (by omega) h1344
  by_cases h1408 : p.val < 1472
  · exact conjugatorCheck_sound 1408 64 conjugatorChecked1408 p (by omega) h1408
  by_cases h1472 : p.val < 1536
  · exact conjugatorCheck_sound 1472 64 conjugatorChecked1472 p (by omega) h1472
  by_cases h1536 : p.val < 1600
  · exact conjugatorCheck_sound 1536 64 conjugatorChecked1536 p (by omega) h1536
  by_cases h1600 : p.val < 1664
  · exact conjugatorCheck_sound 1600 64 conjugatorChecked1600 p (by omega) h1600
  by_cases h1664 : p.val < 1728
  · exact conjugatorCheck_sound 1664 64 conjugatorChecked1664 p (by omega) h1664
  by_cases h1728 : p.val < 1792
  · exact conjugatorCheck_sound 1728 64 conjugatorChecked1728 p (by omega) h1728
  by_cases h1792 : p.val < 1856
  · exact conjugatorCheck_sound 1792 64 conjugatorChecked1792 p (by omega) h1792
  by_cases h1856 : p.val < 1920
  · exact conjugatorCheck_sound 1856 64 conjugatorChecked1856 p (by omega) h1856
  by_cases h1920 : p.val < 1984
  · exact conjugatorCheck_sound 1920 64 conjugatorChecked1920 p (by omega) h1920
  by_cases h1984 : p.val < 2048
  · exact conjugatorCheck_sound 1984 64 conjugatorChecked1984 p (by omega) h1984
  exact conjugatorCheck_sound 2048 10 conjugatorChecked2048 p (by omega) p.isLt

set_option maxRecDepth 10000 in
private theorem inverse_checked : ∀ p : Fin 2058,
    conjugatorInverseTable (conjugatorTable p) = p := by
  apply Cores.allLetters
  decide +kernel

public theorem conjugatorInverseTable_eq (p : Fin 2058) :
    conjugatorInverseTable p = (conjugatorPermutation⁻¹ : Equiv.Perm _) p := by
  have h := inverse_checked ((conjugatorPermutation⁻¹ : Equiv.Perm _) p)
  rw [conjugatorTable_eq] at h
  rw [show conjugatorPermutation ((conjugatorPermutation⁻¹ : Equiv.Perm _) p) = p
    from conjugatorPermutation.apply_symm_apply p] at h
  exact h

end Held.RankOneLocalPair.ConcreteMaximality.CoverCertificate
