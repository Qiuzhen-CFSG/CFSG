module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Obstructions
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.RootElements
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupAction.SimpleCosets
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# Separating genuine binary triality from the seven-component models

The faithful cubic short-root subgroup rules out order 2520 when the field
exponent is at least two. At exponent one the actual arm Levi is PSL₂(8),
of order 504. A hypothetical simple ambient group of order 2520 would then
act faithfully on its five cosets, contradicting divisibility by 5!.
Simplicity makes every ordinary component the whole carrier, and also
excludes the central three-cover. No order formula or independent simplicity
certification for the triality carrier is used.

Source: the Theorem C inspection in Aschbacher–Smith E.6.18, printed p.252,
and Remark A.2.4, printed p.33, `refs/quasithin.pdf`. The actual descended
arm Levi and short-root constructions are the pinned D4 constructions in
`Theory.SpecificGroups.Triality.LeviIdentification` and `RootElements`.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.TrialityCase

/-- The source simplicity hypothesis and the actual arm Levi exclude order 2520. -/
theorem card_ne_seven (n : ℕ) (hn : 0 < n) [IsSimpleGroup (BinaryCarrier n hn)] :
    Nat.card (BinaryCarrier n hn) ≠ 2520 := by
  intro hc
  by_cases h : n = 1
  · subst n
    let P := binaryParameters 1 hn
    let U := levi P .arms
    have hU : Nat.card U = 504 := by
      rw [Nat.card_congr (leviArmsEquivPSL2 P rfl).toEquiv]
      have he := Atlas.ExceptionalSupport.card_psl_mul (F := ExtensionField P) 2
      have hF : Nat.card (ExtensionField P) = 8 := card_extensionField P
      norm_num [hF, Fin.prod_univ_succ] at he
      omega
    have hu : U ≠ ⊤ := by
      intro htop
      have he := hU
      rw [htop, card_top, hc] at he
      omega
    have hi : U.index = 5 := by
      have he := U.card_mul_index
      rw [hU, hc] at he
      omega
    have hd := U.card_dvd_factorial_index_of_simple hu
    change Nat.card (BinaryCarrier 1 hn) ∣ U.index.factorial at hd
    norm_num [hc, hi] at hd
  · have hle : 6 ≤ 3 * n := by omega
    have hd : 2 ^ (3 * n) ∣ Nat.card (BinaryCarrier n hn) := by
      rw [← EvenInvolutionGeometry.shortRootSubgroup_card n hn]
      exact (EvenInvolutionGeometry.shortRootSubgroup n hn).card_subgroup_dvd_card
    have h64 : 64 ∣ 2520 := (pow_dvd_pow 2 hle).trans (hc ▸ hd)
    norm_num at h64

/-- A simple genuine binary triality carrier has no ordinary seven component. -/
theorem no_seven_components (n : ℕ) (hn : 0 < n) [IsSimpleGroup (BinaryCarrier n hn)]
    (L : Subgroup (BinaryCarrier n hn)) (hL : IsComponent (BinaryCarrier n hn) L) :
    ¬ IsSeven L := by
  intro hs
  have ht : L = ⊤ := by
    rcases hL.1.eq_bot_or_top_of_isSimpleGroup inferInstance with hb | ht
    · have hd := seven_card_dvd hs
      simp only [hb, card_bot] at hd
      norm_num at hd
    · exact ht
  let e : L ≃* BinaryCarrier n hn := (MulEquiv.subgroupCongr ht).trans topEquiv
  let : IsSimpleGroup L := e.isSimpleGroup
  let := hL.2
  rcases hs with ha | hc
  · obtain ⟨a⟩ := ha
    have hc : Nat.card (BinaryCarrier n hn) = 2520 := by
      rw [← Nat.card_congr e.toEquiv, Nat.card_congr a.toEquiv,
        nat_card_alternatingGroup]
      norm_num
    exact card_ne_seven n hn hc
  · obtain ⟨_, ⟨c⟩, _⟩ := hc
    have hz : center L = ⊥ := by
      rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with hb | ht
      · exact hb
      · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp ht)).elim
    have hc := Nat.card_congr c.toEquiv
    simp [hz] at hc

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.TrialityCase
