module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.Elementary

/-!
# The actual action quotient in 15.3.11

For `U_I = ⟨Z^I⟩`, the quotient is `I/C_I(U_I)`. Its denominator is normal
inside `I` because `I` normalizes the span and hence its centralizer; no
ambient normality is assumed. The normalizer result uses clauses (2), (4),
and (6) to recover `Y₊` from the inverse image of its quotient image.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 15.3.11(9), printed pp.1123–1124.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03

open Subgroup

variable {G : Type*} [Group G]

/-- The action kernel `C_I(⟨Z^I⟩)`, formed inside `I`. -/
def localActionKernel (Z I : Subgroup G) : Subgroup I :=
  (centralizer (localSpan Z I : Set G)).subgroupOf I

/-- Normality is relative to `I`, as required to form the source quotient. -/
instance localActionKernel_normal (Z I : Subgroup G) : (localActionKernel Z I).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact (le_normalizer_conjugateSpanBy Z I).trans (normalizer_le_normalizer_centralizer _)

abbrev LocalActionQuotient (Z I : Subgroup G) := I ⧸ localActionKernel Z I

/-- The natural quotient map, with the actual centralizer denominator. -/
def localActionMap (Z I : Subgroup G) : I →* LocalActionQuotient Z I :=
  QuotientGroup.mk' (localActionKernel Z I)

/-- The image of `X ∩ I` in the source action quotient `I*`. -/
def localActionImage (Z I X : Subgroup G) : Subgroup (LocalActionQuotient Z I) :=
  (X.subgroupOf I).map (localActionMap Z I)

/-- All three conclusions of 15.3.11(9), derived from the preceding local
clauses and the nontrivial action. The assembly owner supplies these inputs
from the natural orthogonal setup and Hypothesis 15.3.10. -/
theorem lemma_15_3_11_9_of_local_facts
    (Z Yplus S M I : Subgroup G) (hI : I ∈ outsideFamily Yplus S M)
    (hC : I ⊓ centralizer (localSpan Z I : Set G) ≤ M ⊓ I)
    (hN : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hθ : theta (M ⊓ I) = Yplus)
    (hact : ¬ Yplus ≤ centralizer (localSpan Z I : Set G)) :
    normalizer (localActionImage Z I Yplus : Set (LocalActionQuotient Z I)) =
        localActionImage Z I M ∧
      localActionImage Z I M < ⊤ ∧ localActionImage Z I Yplus ≠ ⊥ := by
  have hYI : Yplus ≤ I := le_sup_left.trans hI.1.2
  let f := localActionMap Z I
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hker : f.ker ≤ M.subgroupOf I := by
    rw [show f.ker = localActionKernel Z I from QuotientGroup.ker_mk' _]
    exact fun x hx => (hC ⟨x.property, hx⟩).1
  have hθI : theta (M.subgroupOf I) = Yplus.subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [theta_map_of_injective I.subtype I.subtype_injective,
      subgroupOf_map_subtype, hθ, map_subgroupOf_eq_of_le hYI]
  have hYM : Yplus.subgroupOf I ≤ M.subgroupOf I := by
    rw [← hθI]
    exact theta_le _
  have hNI : normalizer (Yplus.subgroupOf I : Set I) = M.subgroupOf I := by
    rw [← subgroupOf_normalizer_eq hYI]
    ext x
    exact ⟨fun hx => (hN.le ⟨x.property, hx⟩).1,
      fun hx => (hN.ge ⟨hx, x.property⟩).2⟩
  refine ⟨image_normalizer_of_theta f hf _ _ hYM hker hθI hNI, ?_, ?_⟩
  · apply image_lt_top_of_kernel_le f hf _ hker
    apply lt_top_iff_ne_top.mpr
    intro h
    exact hI.2 (subgroupOf_eq_top.mp h)
  · intro h
    have hYker := (map_eq_bot_iff (Yplus.subgroupOf I)).mp h
    rw [show f.ker = localActionKernel Z I from QuotientGroup.ker_mk' _] at hYker
    apply hact
    intro y hy
    exact hYker (show (⟨y, hYI hy⟩ : I) ∈ Yplus.subgroupOf I from hy)

end CFSG.Quasithin.Chapter15.Section03

end
