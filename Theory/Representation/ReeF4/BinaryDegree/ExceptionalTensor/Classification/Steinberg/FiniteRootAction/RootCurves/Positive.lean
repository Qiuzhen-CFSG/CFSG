module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.RootCurves.Degrees
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootSubgroups

/-!
# Actual positive Ree curves with a marked short-root factor

Reparameterize each native main or central curve by the inverse field map
on its long root. This puts an arbitrary prescribed parameter on its short
root factor. The complete native partition and the degree inequalities then
show that every other factor has strictly higher degree. Factor order is
retained, including the essential B2 correction factor.

Source: GLS3 Table 2.4 and 2.4.5(d); Steinberg (1963), Section 12.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.RootCurves

open Theory.AlgebraicGroup StandardRootSystem
open Parabolics RadicalCoordinates RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open NormalizedRootCentralizers.CenterExponent ElementaryTwoBound

local instance rootNegPositive : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- A root word records literal native root indices and field parameters. -/
abbrev RootWord (m : ℕ) := List (F4Chevalley.Root × CoefficientField m)

/-- Evaluate the word in the native split matrix group, in its given order. -/
@[expose] def splitWord {m : ℕ} (w : RootWord m) : SplitGroup m :=
  (w.map fun p => rootGeneratorInGroup m p.1 p.2).prod

/-- Degree measured towards the specified positive or negative chamber. -/
@[expose] def signedDegree (positive : Bool) (r : F4Chevalley.Root) : ℝ :=
  if positive then rootDegree r else -rootDegree r

/-- All factors lie in the specified chamber and have higher degree than the
marked root. -/
@[expose] def HigherSupport {m : ℕ} (positive : Bool) (r : F4Chevalley.Root)
    (w : RootWord m) : Prop :=
  ∀ p ∈ w, (if positive then typeF4RootPairing_base.IsPos p.1
      else typeF4RootPairing_base.IsPos (-p.1)) ∧
    signedDegree positive r < signedDegree positive p.1


private theorem long_pos (i : Fin 8) : typeF4RootPairing_base.IsPos (longRoot i) := by
  rcases positiveRootWordLayout.positive_covers i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [← positiveRootWordLayout.pair_long j]
    exact (positiveRootWordLayout.blocks.roots (.inl (j, 0))).property
  · rw [← positiveRootWordLayout.quartet_long j]
    exact (positiveRootWordLayout.blocks.roots (.inr (j, 0))).property

private theorem mixed_pos (i : Fin 8) : typeF4RootPairing_base.IsPos (mixedRoot i) := by
  rcases positiveRootWordLayout.positive_covers i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [positiveRootWordLayout.pair_mixed j, ← positiveRootWordLayout.pair_short j]
    exact (positiveRootWordLayout.blocks.roots (.inl (j, 1))).property
  · rw [← positiveRootWordLayout.quartet_mixed j]
    exact (positiveRootWordLayout.blocks.roots (.inr (j, 2))).property

private theorem high_pos (i : Fin 8) : typeF4RootPairing_base.IsPos (highRoot i) := by
  rcases positiveRootWordLayout.positive_covers i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [positiveRootWordLayout.pair_high j, ← positiveRootWordLayout.pair_long j]
    exact (positiveRootWordLayout.blocks.roots (.inl (j, 0))).property
  · rw [← positiveRootWordLayout.quartet_high j]
    exact (positiveRootWordLayout.blocks.roots (.inr (j, 3))).property

private theorem inverse_parameter (m : ℕ) (i : Fin 8) (t : CoefficientField m) :
    rootFieldEnd m (longRoot i) (rootFieldEnd m (shortRoot i) t) = t := by
  have h := rootFieldEnd_twice m (shortRoot i) t
  change rootFieldEnd m (exceptionalRootPermutation (exceptionalRootPermutation (longRoot i)))
    (rootFieldEnd m (shortRoot i) t) = t at h
  rw [exceptionalRootPermutation_involutive] at h
  exact h

/-- Every native positive short root occurs with any prescribed field
parameter inside an actual Ree element, with only higher-degree side factors. -/
theorem exists_positive_root_curve (m : ℕ) {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) (hs : IsShortRoot r)
    (t : CoefficientField m) :
    ∃ (g : Model m) (left right : RootWord m),
      HigherSupport true r (left ++ right) ∧
      toSplitGroup m g = splitWord left * rootGeneratorInGroup m r t * splitWord right := by
  rcases positive_short_cases hr hs with ⟨i, rfl, hl, hm⟩ | ⟨i, _, rfl, hh⟩
  · let s := rootFieldEnd m (shortRoot i) t
    refine ⟨mainElement m i s, [(longRoot i, s)],
      if i.val % 2 = 0 then [(mixedRoot i, s * t)] else [], ?_, ?_⟩
    · intro p hp
      by_cases hi : i.val % 2 = 0
      · simp only [if_pos hi, List.mem_append, List.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact ⟨long_pos i, hl⟩
        · exact ⟨mixed_pos i, hm hi⟩
      · simp only [if_neg hi, List.append_nil, List.mem_singleton] at hp
        subst p
        exact ⟨long_pos i, hl⟩
    · rw [mainElement_coe]
      simp only [rootWord, s, inverse_parameter]
      by_cases hi : i.val % 2 = 0 <;>
        simp [splitWord, hi]
  · let s := rootFieldEnd m (shortRoot i) t
    refine ⟨centralElement m i s, [(highRoot i, s)], [], ?_, ?_⟩
    · intro p hp
      simp only [List.append_nil, List.mem_singleton] at hp
      subst p
      exact ⟨high_pos i, hh⟩
    · rw [centralElement_coe]
      simp [centralWord, splitWord, s, inverse_parameter]

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.RootCurves
