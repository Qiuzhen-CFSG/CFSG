module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Parameters
public import Theory.Quasithin.Rank
public import Theory.SpecificGroups.OddThreeRank
public import Theory.SpecificGroups.OddThreeSylowOrder

/-!
# Odd degree-three exclusions for the faithful full Sylow action

A binary PSL₂ subgroup in an odd degree-three classical group has parameter
at most two by elementary two-rank. In the noncubic range its parameter is
therefore exactly two. A full ambient Sylow subgroup acting faithfully on
this PSL₂(4) then has order dividing eight, whereas the containing classical
group forces its order to be divisible by sixteen.

Both projective groups and their special covers are treated. The hypotheses
refer to the full original Sylow action, as in Aschbacher–Smith C.5.13,
printed pp.162–163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02.LocalModels
open Theory.SpecificGroups.OddThreeRank Theory.SpecificGroups.OddThreeSylowOrder
variable {G : Type*} [Group G] [Finite G]

private theorem odd_three_order_contradiction
    (T : Sylow 2 G) (B D : Subgroup G) (hBD : B ≤ D) {n : ℕ}
    (hn : 1 < n) (hB : ClassicalGroup.IsPSL B 2 (2^n))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (T : Subgroup G) ⊓ centralizer (B : Set G) = ⊥)
    (hr : primeRank 2 D ≤ 2) (hd : 16 ∣ Nat.card D) : False := by
  have hn2 : n = 2 := by
    have := (binary_rank_lower hB).trans ((primeRank_mono 2 hBD).trans hr)
    omega
  have hs := binary_normalizer_card_dvd T B (by omega) hB hTB hfaith
  have hl : 16 ∣ Nat.card T := T.pow_dvd_card_of_pow_dvd_card (n := 4)
    (hd.trans (card_subgroup_dvd_card D))
  rw [hn2] at hs
  have := hl.trans hs
  norm_num at this

/-- No odd-prime projective linear or unitary degree-three containing model
admits the actual faithful full-Sylow action on the binary subgroup. -/
theorem not_odd_three_projective_containing
    (T : Sylow 2 G) (B D : Subgroup G) (hBD : B ≤ D) {n : ℕ}
    (hn : 1 < n) (hB : ClassicalGroup.IsPSL B 2 (2^n))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (T : Subgroup G) ⊓ centralizer (B : Set G) = ⊥)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool) :
    ¬ IsPSLSign D unitary 3 p := by
  intro hm
  apply odd_three_order_contradiction T B D hBD hn hB hTB hfaith
  · cases unitary with
    | false =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      rw [primeRank_equiv 2 e]
      exact psl3_primeRank_two_le hp ho hF
    | true =>
      obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hm
      let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_equiv D e.toEquiv
      rw [primeRank_equiv 2 e]
      exact psu3_primeRank_two_le J hp ho hF hc
  · cases unitary with
    | false =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      rw [Nat.card_congr e.toEquiv]
      exact projective_sixteen_dvd_card (hF.symm ▸ ho)
    | true =>
      obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hm
      rw [Nat.card_congr e.toEquiv]
      exact unitary_projective_sixteen_dvd_card J hp ho hF hc

/-- The same contradiction excludes the special linear and special unitary
covers in the full A.3.6 containing-model catalogue. -/
theorem not_odd_three_special_containing
    (T : Sylow 2 G) (B D : Subgroup G) (hBD : B ≤ D) {n : ℕ}
    (hn : 1 < n) (hB : ClassicalGroup.IsPSL B 2 (2^n))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (T : Subgroup G) ⊓ centralizer (B : Set G) = ⊥)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool) :
    ¬ IsSLSign D unitary 3 p := by
  intro hm
  apply odd_three_order_contradiction T B D hBD hn hB hTB hfaith
  · cases unitary with
    | false =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      exact special_primeRank_two_le e
        (two_ne_zero_of_odd_card ho (k := 1) (by simpa using hF))
    | true =>
      obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hm
      rw [primeRank_equiv 2 e]
      exact hermitian_special_primeRank_two_le J (two_ne_zero_of_odd_card ho hF)
  · cases unitary with
    | false =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      rw [Nat.card_congr e.toEquiv]
      exact special_sixteen_dvd_card (hF.symm ▸ ho)
    | true =>
      obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hm
      rw [Nat.card_congr e.toEquiv]
      exact unitary_special_sixteen_dvd_card J hp ho hF hc

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
