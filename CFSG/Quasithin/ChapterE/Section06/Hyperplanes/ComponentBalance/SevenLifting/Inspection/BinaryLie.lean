module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.RankAndOrder
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Four

/-!
# Characteristic-two assembly of the E.6.18 inspection

Binary PSL₂, Suzuki, Sp₄(2)′, G₂(2)′ and the actual Tits presentation are
discharged by rank and order obstructions. PSL₄(2) is handled using the actual
isomorphism to A₈ and the proved alternating inspection. The assembly retains all
eight rank-two constructors, including the genuine pinned triality model and
the actual Ree `LocalBlockInput` fixed group.

The remaining premises are explicit outstanding model inspections: PSU₃,
PSL₃, Sp₄, G₂, triality and Ree, together with PSL₅(2).
Consequently these conditional assembly lemmas do not yet prove
the full characteristic-two inspection in E.6.18. Their owner must supply the
model-specific fixed-component restrictions for arbitrary two-subgroups.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18,
printed p.252; Theorem C and Remark A.2.4, printed p.33.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
open Chapter1.Section02.LocalModels
variable {S : Type*} [Group S] [Finite S]

/-- Only the unitary model inspection remains in the Bender family. -/
theorem bender_of_unitary
    (hunitary : ∀ f : ℕ, 2 ≤ f → ClassicalGroup.IsPSU S 3 (2 ^ f) →
      SevenActionInspection S)
    (h : ClassificationModels.IsBenderModel S) : SevenActionInspection S := by
  cases h with
  | linear f hf iso => exact linear_rank_one hf iso
  | unitary f hf iso => exact hunitary f hf iso
  | suzuki m hm iso => exact suzuki hm iso

omit [Finite S] in
/-- All three small endpoints are proved; each remaining infinite family is
an explicit premise to be discharged by its concrete model proof. -/
theorem rank_two_of_family_inspections [IsSimpleGroup S]
    (hlinear : ∀ f : ℕ, 1 ≤ f → ClassicalGroup.IsPSL S 3 (2 ^ f) →
      SevenActionInspection S)
    (hsymplectic : ∀ f : ℕ, 2 ≤ f → ClassicalGroup.IsPSp S 2 (2 ^ f) →
      SevenActionInspection S)
    (hg2 : ∀ f : ℕ, 2 ≤ f → ClassificationModels.IsG2At S (2 ^ f) →
      SevenActionInspection S)
    (htriality : ∀ f : ℕ, 1 ≤ f → Triality.Standard.IsTrialityGroupAt (2 ^ f) S →
      SevenActionInspection S)
    (hree : ∀ m : ℕ, 1 ≤ m → IsReeF4At S m → SevenActionInspection S)
    (h : RankTwoTheoremC S) : SevenActionInspection S := by
  cases h with
  | linear f hf iso => exact hlinear f hf iso
  | symplectic f hf iso => exact hsymplectic f hf iso
  | g2 f hf iso => exact hg2 f hf iso
  | triality f hf iso => exact htriality f hf iso
  | ree m hm iso => exact hree m hm iso
  | symplectic_derived iso => exact symplectic_derived iso
  | g2_derived iso => exact g2_derived iso
  | tits iso => exact tits iso

/-- The binary-linear branch only needs the dimension-five inspection. -/
theorem binary_linear_of_five
    (hfive : ClassicalGroup.IsPSL S 5 2 → SevenActionInspection S)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (h : ClassicalGroup.IsPSL S n 2) :
    SevenActionInspection S := by
  rcases hn with rfl | rfl
  · exact binary_four h
  · exact hfive h

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
