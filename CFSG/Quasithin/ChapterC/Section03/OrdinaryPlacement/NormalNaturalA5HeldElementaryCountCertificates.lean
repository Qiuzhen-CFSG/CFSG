module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryCoreCountSixteenZero
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryCoreCountSixteenOne
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryCoreCountThirtyTwoZero
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryCoreCountThirtyTwoOne
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryFastCounts

/-!
# Kernel-checked native elementary class-count certificates

The finite tree checks the original subgroup closure constraints and counts
the exact conjugacy label. Proposal trees were found by an untrusted search;
only the kernel computation and the sound checker establish these counts.
Source: Aschbacher--Smith 12.7.5, printed p.840.
-/

@[expose] public section
namespace Held.OrdinaryElementary.NativeCoverage

def candidateSet (k : Fin 34) : Finset (Fin 192) :=
  Finset.univ.filter (fun v => (candidateMask k).testBit v.val = true)

set_option maxRecDepth 10000 in
private def countTree16_28 : CountTree := (.branch 1 (.branch 2 (.branch 4 (.branch 6 (.branch 17 (.branch 18 (.branch 23 (.branch 24 (.branch 25 (.branch 26 (.branch 27 (.branch 29 (.branch 31 (.branch 34 (.branch 36 (.branch 37 .bounds .impossible) .impossible) .impossible) .impossible) .impossible) (.branch 29 .impossible .impossible)) (.branch 27 (.branch 29 .impossible (.branch 31 .impossible .impossible)) .impossible)) (.branch 26 (.branch 27 .bounds .impossible) .bounds)) (.branch 25 .bounds .impossible)) (.branch 24 (.branch 26 .bounds .impossible) .impossible)) (.branch 23 (.branch 24 (.branch 25 .bounds .impossible) .bounds) .impossible)) (.branch 18 (.branch 23 (.branch 24 (.branch 26 .bounds .impossible) .impossible) (.branch 24 .bounds .impossible)) .bounds)) (.branch 17 (.branch 18 (.branch 23 (.branch 24 (.branch 25 (.branch 26 .impossible .impossible) .impossible) .impossible) .bounds) (.branch 23 .impossible .impossible)) (.branch 18 (.branch 24 .impossible .impossible) .impossible))) (.branch 6 (.branch 17 (.branch 18 (.branch 23 (.branch 24 (.branch 25 (.branch 27 .impossible .impossible) .impossible) .impossible) .bounds) (.branch 23 .impossible .impossible)) (.branch 18 (.branch 24 .impossible .impossible) .impossible)) (.branch 17 (.branch 18 (.branch 24 .bounds .bounds) .bounds) (.branch 18 .bounds .bounds)))) (.branch 4 (.branch 6 (.branch 17 (.branch 18 (.branch 23 (.branch 24 (.branch 26 (.branch 31 .impossible .impossible) .impossible) .impossible) .bounds) (.branch 23 .impossible .impossible)) (.branch 18 (.branch 24 .impossible .impossible) .impossible)) (.branch 17 (.branch 18 (.branch 23 .bounds .bounds) .bounds) (.branch 18 .bounds .bounds))) (.branch 17 (.branch 18 (.branch 23 (.branch 24 .impossible .impossible) .bounds) .bounds) (.branch 18 .bounds .bounds)))) (.branch 2 (.branch 4 (.branch 6 (.branch 17 (.branch 18 (.branch 23 (.branch 24 (.branch 29 (.branch 34 .impossible .impossible) .impossible) .impossible) .bounds) (.branch 23 .impossible .impossible)) (.branch 18 (.branch 24 .impossible .impossible) .impossible)) (.branch 17 (.branch 18 (.branch 23 (.branch 24 .impossible .impossible) .bounds) .bounds) (.branch 18 .bounds .bounds))) (.branch 17 (.branch 18 (.branch 23 .bounds .bounds) .bounds) (.branch 18 .bounds .bounds))) (.branch 4 (.branch 17 (.branch 18 (.branch 24 .bounds .bounds) .bounds) (.branch 18 .bounds .bounds)) (.branch 17 (.branch 18 .bounds .bounds) .bounds))))

set_option maxRecDepth 10000 in
private theorem count_checked16_28 :
    fastCountCheck 16 countTree16_28 {0} (candidateSet 28) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private def countTree16_29 : CountTree := (.branch 3 (.branch 5 (.branch 7 (.branch 8 (.branch 19 (.branch 20 (.branch 21 (.branch 22 (.branch 28 (.branch 30 (.branch 32 (.branch 33 (.branch 35 (.branch 38 (.branch 39 (.branch 40 .bounds .impossible) .impossible) .impossible) .impossible) .impossible) (.branch 33 .impossible .impossible)) (.branch 32 (.branch 33 .impossible .impossible) .impossible)) (.branch 30 (.branch 32 .bounds .impossible) .bounds)) (.branch 30 .bounds .impossible)) (.branch 22 (.branch 28 .bounds .impossible) .impossible)) (.branch 21 (.branch 22 (.branch 28 .bounds .impossible) .impossible) (.branch 22 .bounds .impossible))) (.branch 20 (.branch 21 (.branch 22 (.branch 30 .bounds .impossible) .bounds) .impossible) .bounds)) (.branch 19 (.branch 20 (.branch 21 (.branch 22 (.branch 28 (.branch 30 .impossible .impossible) .impossible) .impossible) .bounds) (.branch 22 .impossible .impossible)) (.branch 20 (.branch 21 .impossible .impossible) .impossible))) (.branch 8 (.branch 19 (.branch 20 (.branch 21 (.branch 22 (.branch 28 (.branch 32 .impossible .impossible) .impossible) .impossible) .bounds) (.branch 22 .impossible .impossible)) (.branch 20 (.branch 21 .impossible .impossible) .impossible)) (.branch 19 (.branch 20 (.branch 21 .bounds .bounds) .bounds) (.branch 20 .bounds .bounds)))) (.branch 7 (.branch 8 (.branch 19 (.branch 20 (.branch 21 (.branch 22 (.branch 30 (.branch 33 .impossible .impossible) .impossible) .impossible) .bounds) (.branch 22 .impossible .impossible)) (.branch 20 (.branch 21 .impossible .impossible) .impossible)) (.branch 19 (.branch 20 (.branch 22 .bounds .bounds) .bounds) (.branch 20 .bounds .bounds))) (.branch 19 (.branch 20 (.branch 21 (.branch 22 .impossible .impossible) .bounds) .bounds) (.branch 20 .bounds .bounds)))) (.branch 5 (.branch 7 (.branch 8 (.branch 19 (.branch 20 (.branch 21 (.branch 22 (.branch 35 (.branch 38 .impossible .impossible) .impossible) .impossible) .bounds) (.branch 22 .impossible .impossible)) (.branch 20 (.branch 21 .impossible .impossible) .impossible)) (.branch 19 (.branch 20 (.branch 21 (.branch 22 .impossible .impossible) .bounds) .bounds) (.branch 20 .bounds .bounds))) (.branch 19 (.branch 20 (.branch 22 .bounds .bounds) .bounds) (.branch 20 .bounds .bounds))) (.branch 7 (.branch 19 (.branch 20 (.branch 21 .bounds .bounds) .bounds) (.branch 20 .bounds .bounds)) (.branch 19 (.branch 20 .bounds .bounds) .bounds))))

set_option maxRecDepth 10000 in
private theorem count_checked16_29 :
    fastCountCheck 16 countTree16_29 {0} (candidateSet 29) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private def countTree16_30 : CountTree := (.branch 9 (.branch 10 (.branch 15 (.branch 16 (.branch 63 (.branch 65 (.branch 67 (.branch 68 (.branch 99 (.branch 102 (.branch 104 (.branch 105 (.branch 107 (.branch 109 (.branch 110 (.branch 112 .bounds .impossible) .impossible) .impossible) .impossible) .impossible) (.branch 105 .impossible .impossible)) (.branch 104 .bounds .impossible)) (.branch 102 (.branch 104 (.branch 105 .impossible .impossible) .impossible) .bounds)) (.branch 99 (.branch 102 .impossible .impossible) .impossible)) (.branch 68 (.branch 105 (.branch 107 .impossible .impossible) .impossible) .impossible)) (.branch 67 (.branch 68 (.branch 102 (.branch 104 .impossible .impossible) .impossible) .bounds) .bounds)) (.branch 65 (.branch 67 (.branch 68 (.branch 99 (.branch 105 .impossible .impossible) .impossible) .bounds) .bounds) .bounds)) (.branch 63 (.branch 65 (.branch 67 (.branch 68 (.branch 99 .bounds .impossible) .impossible) .bounds) .bounds) (.branch 65 .bounds .impossible))) (.branch 16 (.branch 63 (.branch 65 (.branch 67 (.branch 68 (.branch 102 .bounds .impossible) .impossible) .bounds) .bounds) (.branch 65 .bounds .impossible)) (.branch 63 (.branch 65 .bounds .impossible) .bounds))) (.branch 15 (.branch 16 (.branch 63 (.branch 65 (.branch 67 (.branch 68 (.branch 102 .bounds .impossible) .impossible) .bounds) .bounds) (.branch 65 .bounds .impossible)) (.branch 63 (.branch 65 .bounds .impossible) .bounds)) (.branch 16 (.branch 63 (.branch 65 .bounds .impossible) .bounds) (.branch 63 .bounds .bounds)))) (.branch 10 (.branch 15 (.branch 16 (.branch 63 (.branch 65 (.branch 67 (.branch 68 (.branch 99 .bounds .impossible) .impossible) .bounds) .bounds) (.branch 65 .bounds .impossible)) (.branch 63 (.branch 65 .bounds .impossible) .bounds)) (.branch 16 (.branch 63 (.branch 65 .bounds .impossible) .bounds) (.branch 63 .bounds .bounds))) (.branch 15 (.branch 16 (.branch 63 (.branch 65 .bounds .impossible) .bounds) (.branch 63 .bounds .bounds)) (.branch 16 (.branch 63 .bounds .bounds) .bounds))))

set_option maxRecDepth 10000 in
private theorem count_checked16_30 :
    fastCountCheck 16 countTree16_30 {0} (candidateSet 30) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private def countTree16_31 : CountTree := (.branch 11 (.branch 12 (.branch 13 (.branch 14 (.branch 61 (.branch 62 (.branch 64 (.branch 66 (.branch 97 (.branch 98 (.branch 100 (.branch 101 (.branch 103 (.branch 106 (.branch 108 (.branch 111 .bounds .impossible) .impossible) .impossible) .impossible) .impossible) (.branch 101 .impossible .impossible)) (.branch 100 .bounds (.branch 101 .impossible .impossible))) (.branch 98 (.branch 100 (.branch 101 .impossible .impossible) .impossible) .bounds)) (.branch 97 (.branch 98 .impossible .impossible) .impossible)) (.branch 66 (.branch 100 (.branch 101 .impossible .impossible) .impossible) .impossible)) (.branch 64 (.branch 66 (.branch 98 (.branch 103 .impossible .impossible) .impossible) .bounds) .bounds)) (.branch 62 (.branch 64 (.branch 66 (.branch 97 (.branch 100 .impossible .impossible) .impossible) .bounds) .bounds) .bounds)) (.branch 61 (.branch 62 (.branch 64 (.branch 66 (.branch 97 .bounds .impossible) .impossible) .bounds) .bounds) (.branch 62 .bounds .impossible))) (.branch 14 (.branch 61 (.branch 62 (.branch 64 (.branch 66 (.branch 98 .bounds .impossible) .impossible) .bounds) .bounds) (.branch 62 .bounds .impossible)) (.branch 61 (.branch 62 .bounds .impossible) .bounds))) (.branch 13 (.branch 14 (.branch 61 (.branch 62 (.branch 64 (.branch 66 (.branch 98 .bounds .impossible) .impossible) .bounds) .bounds) (.branch 62 .bounds .impossible)) (.branch 61 (.branch 62 .bounds .impossible) .bounds)) (.branch 14 (.branch 61 (.branch 62 .bounds .impossible) .bounds) (.branch 61 .bounds .bounds)))) (.branch 12 (.branch 13 (.branch 14 (.branch 61 (.branch 62 (.branch 64 (.branch 66 (.branch 97 .bounds .impossible) .impossible) .bounds) .bounds) (.branch 62 .bounds .impossible)) (.branch 61 (.branch 62 .bounds .impossible) .bounds)) (.branch 14 (.branch 61 (.branch 62 .bounds .impossible) .bounds) (.branch 61 .bounds .bounds))) (.branch 13 (.branch 14 (.branch 61 (.branch 62 .bounds .impossible) .bounds) (.branch 61 .bounds .bounds)) (.branch 14 (.branch 61 .bounds .bounds) .bounds))))

set_option maxRecDepth 10000 in
private theorem count_checked16_31 :
    fastCountCheck 16 countTree16_31 {0} (candidateSet 31) = true := by
  decide +kernel



set_option maxRecDepth 10000 in
private def countTree32_28 : CountTree := .bounds

set_option maxRecDepth 10000 in
private theorem count_checked32_28 :
    fastCountCheck 32 countTree32_28 {0} (candidateSet 28) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private def countTree32_29 : CountTree := .bounds

set_option maxRecDepth 10000 in
private theorem count_checked32_29 :
    fastCountCheck 32 countTree32_29 {0} (candidateSet 29) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private def countTree32_30 : CountTree := .bounds

set_option maxRecDepth 10000 in
private theorem count_checked32_30 :
    fastCountCheck 32 countTree32_30 {0} (candidateSet 30) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private def countTree32_31 : CountTree := .bounds

set_option maxRecDepth 10000 in
private theorem count_checked32_31 :
    fastCountCheck 32 countTree32_31 {0} (candidateSet 31) = true := by
  decide +kernel



private theorem small_counts : ∀k:Fin 28,
    fastCountCheck 16 .bounds {0} (candidateSet (⟨k.val,Nat.lt_trans k.isLt (by decide)⟩ : Fin 34)) = true := by
  decide +kernel

theorem candidate_count16 (k:Fin 34) (s : Finset (Fin 192))
    (hs : s.card=16) (h0 : 0∈s) (hsub : s⊆candidateSet k)
    (hcomm : ∀ v∈s,∀w∈s,compatible v w=true)
    (hcoset : ∀v w,w∈s → compatible v w=true → (productVertex v w∈s ↔ v∈s)) :
    allowedCount 16 (markedCount s) := by
  by_cases hk : k.val<28
  · exact fastCountCheck_sound 16 .bounds {0} (candidateSet k) s
      (small_counts ⟨k.val,hk⟩) (Finset.singleton_subset_iff.mpr h0) hsub hs hcomm hcoset
  · have hk' : k=28 ∨ k=29 ∨ k=30 ∨ k=31 ∨ k=32 ∨ k=33 := by
      have hlt:=k.isLt
      omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fastCountCheck_sound 16 countTree16_28 {0} (candidateSet 28) s
        count_checked16_28 (Finset.singleton_subset_iff.mpr h0) hsub hs hcomm hcoset
    · exact fastCountCheck_sound 16 countTree16_29 {0} (candidateSet 29) s
        count_checked16_29 (Finset.singleton_subset_iff.mpr h0) hsub hs hcomm hcoset
    · exact fastCountCheck_sound 16 countTree16_30 {0} (candidateSet 30) s
        count_checked16_30 (Finset.singleton_subset_iff.mpr h0) hsub hs hcomm hcoset
    · exact fastCountCheck_sound 16 countTree16_31 {0} (candidateSet 31) s
        count_checked16_31 (Finset.singleton_subset_iff.mpr h0) hsub hs hcomm hcoset
    · exact core_count16_0 s hs h0 hsub hcomm hcoset
    · exact core_count16_1 s hs h0 hsub hcomm hcoset

theorem candidate_count32 (k:Fin 34) (s : Finset (Fin 192))
    (hs : s.card=32) (h0 : 0∈s) (hsub : s⊆candidateSet k)
    (hcomm : ∀ v∈s,∀w∈s,compatible v w=true)
    (hcoset : ∀v w,w∈s → compatible v w=true → (productVertex v w∈s ↔ v∈s)) :
    allowedCount 32 (markedCount s) := by
  by_cases hk : k.val<28
  · have hh : ∀k:Fin 28,(candidateSet (⟨k.val,Nat.lt_trans k.isLt (by decide)⟩ : Fin 34)).card<32 := by decide +kernel
    have hb : (candidateSet k).card<32 := hh ⟨k.val,hk⟩
    have hc := Finset.card_le_card hsub
    omega
  · have hk' : k=28 ∨ k=29 ∨ k=30 ∨ k=31 ∨ k=32 ∨ k=33 := by
      have hlt:=k.isLt
      omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fastCountCheck_sound 32 countTree32_28 {0} (candidateSet 28) s
        count_checked32_28 (Finset.singleton_subset_iff.mpr h0) hsub hs hcomm hcoset
    · exact fastCountCheck_sound 32 countTree32_29 {0} (candidateSet 29) s
        count_checked32_29 (Finset.singleton_subset_iff.mpr h0) hsub hs hcomm hcoset
    · exact fastCountCheck_sound 32 countTree32_30 {0} (candidateSet 30) s
        count_checked32_30 (Finset.singleton_subset_iff.mpr h0) hsub hs hcomm hcoset
    · exact fastCountCheck_sound 32 countTree32_31 {0} (candidateSet 31) s
        count_checked32_31 (Finset.singleton_subset_iff.mpr h0) hsub hs hcomm hcoset
    · exact core_count32_0 s hs h0 hsub hcomm hcoset
    · exact core_count32_1 s hs h0 hsub hcomm hcoset

end Held.OrdinaryElementary.NativeCoverage
