module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.Geometry

/-!
# Short-root detectors for all F4 roots

Every root `r` admits short roots `s` and `k = s + r` with root-string
coefficient one. For a signed pair we cancel one coordinate by a unit root;
for a unit root we choose a half-sign vector; for a half-sign vector we flip
one coordinate by a unit root. The parallelogram identity then gives squared
length three or five for `r - s`, so it is not a root.

This is the coordinate geometry of the standard F4 root system underlying
Geck's integral construction; see Steinberg, *Lectures on Chevalley Groups*,
the root-string formulas for the integral admissible lattice.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open scoped Matrix

namespace ReeF4.WordRelations.ShortOperators

private lemma short_of_norm (r : typeF4Roots) (h : dot r.val r.val = 1) :
    IsShortRoot r := by
  intro hr
  have := isLongRoot_norm r hr
  linarith

private noncomputable def unitRoot (i : Fin 4) : typeF4Roots :=
  ⟨basisVector i, Or.inl (Or.inr ⟨i, Or.inl rfl⟩)⟩

private lemma unitRoot_short (i : Fin 4) : IsShortRoot (unitRoot i) := by
  apply short_of_norm
  simp [unitRoot, dot, basisVector, Pi.single_apply]

private noncomputable def halfRoot (ε : Fin 4 → Bool) : typeF4Roots :=
  ⟨halfSignVector ε, halfSignVector_mem_typeF4Roots ε⟩

private lemma halfRoot_short (ε : Fin 4 → Bool) : IsShortRoot (halfRoot ε) := by
  apply short_of_norm
  change (∑ i : Fin 4, halfSignVector ε i * halfSignVector ε i) = 1
  have hh (i : Fin 4) : halfSignVector ε i * halfSignVector ε i = (1 / 4 : ℝ) := by
    cases h : ε i <;> norm_num [halfSignVector, h]
  simp_rw [hh]
  norm_num

private def HasDetector (x : Vec 4) : Prop :=
  ∃ s k : typeF4Roots, IsShortRoot s ∧ IsShortRoot k ∧ k.val = s.val + x

private lemma hasDetector_neg {x : Vec 4} (h : HasDetector x) : HasDetector (-x) := by
  let := typeF4RootPairing.indexNeg
  obtain ⟨s, k, hs, hk, he⟩ := h
  refine ⟨-s, -k, (isShortRoot_neg_iff s).mpr hs,
    (isShortRoot_neg_iff k).mpr hk, ?_⟩
  have hneg (r : typeF4Roots) : (-r).val = -r.val := by
    change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  rw [hneg, hneg, he]
  abel

private lemma hasDetector_unit (i : Fin 4) : HasDetector (basisVector i) := by
  classical
  refine ⟨halfRoot (fun j => if j = i then false else true), halfRoot (fun _ => true),
    halfRoot_short _, halfRoot_short _, ?_⟩
  ext j
  by_cases h : j = i <;> norm_num [halfRoot, halfSignVector, basisVector, h]

private lemma hasDetector_half (ε : Fin 4 → Bool) : HasDetector (halfSignVector ε) := by
  classical
  let := typeF4RootPairing.indexNeg
  let δ : Fin 4 → Bool := fun j => if j = 0 then !(ε j) else ε j
  have hneg : (-(unitRoot 0)).val = -basisVector 0 := by
    change typeF4RootPairing.root (-(unitRoot 0)) = -typeF4RootPairing.root (unitRoot 0)
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  cases h : ε 0
  · refine ⟨unitRoot 0, halfRoot δ, unitRoot_short _, halfRoot_short _, ?_⟩
    ext j
    by_cases hj : j = 0
    · subst j; norm_num [halfRoot, unitRoot, halfSignVector, basisVector, δ, h]
    · simp [halfRoot, unitRoot, halfSignVector, basisVector, δ, hj]
  · refine ⟨-(unitRoot 0), halfRoot δ, (isShortRoot_neg_iff _).mpr (unitRoot_short _),
      halfRoot_short _, ?_⟩
    rw [hneg]
    ext j
    by_cases hj : j = 0
    · subst j; norm_num [halfRoot, halfSignVector, basisVector, δ, h]
    · simp [halfRoot, halfSignVector, basisVector, δ, hj]

private lemma hasDetector_pair (i j : Fin 4) (a c : ℝ)
    (ha : a ∈ ({-1, 1} : Set ℝ)) (hc : c ∈ ({-1, 1} : Set ℝ)) :
    HasDetector (a • basisVector i + c • basisVector j) := by
  let := typeF4RootPairing.indexNeg
  have hneg (l : Fin 4) : (-(unitRoot l)).val = -basisVector l := by
    change typeF4RootPairing.root (-(unitRoot l)) = -typeF4RootPairing.root (unitRoot l)
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  rcases ha with rfl | ha <;> rcases hc with rfl | hc
  · refine ⟨unitRoot i, -(unitRoot j), unitRoot_short _,
      (isShortRoot_neg_iff _).mpr (unitRoot_short _), ?_⟩
    rw [hneg]
    simp only [unitRoot, neg_one_smul]
    abel
  · rcases hc with rfl
    refine ⟨unitRoot i, unitRoot j, unitRoot_short _, unitRoot_short _, ?_⟩
    simp [unitRoot]
  · rcases ha with rfl
    refine ⟨-(unitRoot i), -(unitRoot j),
      (isShortRoot_neg_iff _).mpr (unitRoot_short _),
      (isShortRoot_neg_iff _).mpr (unitRoot_short _), ?_⟩
    simp only [hneg, one_smul, neg_one_smul]
    abel
  · rcases ha with rfl
    rcases hc with rfl
    refine ⟨-(unitRoot i), unitRoot j,
      (isShortRoot_neg_iff _).mpr (unitRoot_short _), unitRoot_short _, ?_⟩
    rw [hneg]
    simp [unitRoot]

private lemma hasDetector_root (r : typeF4Roots) : HasDetector r.val := by
  rcases r.property with (hp | hu) | hh
  · obtain ⟨i, j, -, a, c, ha, hc, he⟩ := hp
    rw [he]
    exact hasDetector_pair i j a c ha hc
  · obtain ⟨i, he | he⟩ := hu
    · rw [he]; exact hasDetector_unit i
    · rw [he]; exact hasDetector_neg (hasDetector_unit i)
  · obtain ⟨ε, he⟩ := hh
    rw [← he]
    exact hasDetector_half ε

private lemma norm_parallelogram (x y : Vec 4) :
    dot (x - y) (x - y) + dot (x + y) (x + y) =
      2 * dot x x + 2 * dot y y := by
  change (x - y) ⬝ᵥ (x - y) + (x + y) ⬝ᵥ (x + y) =
      2 * (x ⬝ᵥ x) + 2 * (y ⬝ᵥ y)
  simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add]
  ring

theorem exists_short_detector (r : typeF4Roots) :
    ∃ s k : typeF4Roots, IsShortRoot s ∧ IsShortRoot k ∧
      typeF4RootPairing.root k = typeF4RootPairing.root s + typeF4RootPairing.root r ∧
      typeF4RootPairing.chainBotCoeff s r = 0 := by
  obtain ⟨s, k, hs, hk, he⟩ := hasDetector_root r
  refine ⟨s, k, hs, hk, he, ?_⟩
  apply typeF4RootPairing.chainBotCoeff_eq_zero_iff.mpr
  right
  rintro ⟨t, ht⟩
  change t.val = r.val - s.val at ht
  have hn := norm_parallelogram r.val s.val
  rw [← ht, add_comm r.val s.val, ← he, isShortRoot_norm s hs,
    isShortRoot_norm k hk] at hn
  by_cases hr : IsLongRoot r <;> by_cases ht : IsLongRoot t
  · rw [isLongRoot_norm r hr, isLongRoot_norm t ht] at hn; norm_num at hn
  · rw [isLongRoot_norm r hr, isShortRoot_norm t ht] at hn; norm_num at hn
  · rw [isShortRoot_norm r hr, isLongRoot_norm t ht] at hn; norm_num at hn
  · rw [isShortRoot_norm r hr, isShortRoot_norm t ht] at hn; norm_num at hn

end ReeF4.WordRelations.ShortOperators
