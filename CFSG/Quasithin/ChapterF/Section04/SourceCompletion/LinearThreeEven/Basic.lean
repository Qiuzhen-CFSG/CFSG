module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Generated
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.RankTwoGeneration

/-!
# The full-extension and source quotient inputs for linear-three completion

Use the existing faithful type-preserving extension contract with the actual
PSL₃ point and line parabolics. All outer factors and the whole middle are
retained. The source Hall-quotient relation gives cube membership in that
middle by the kernel of its literal quotient map.

Source: Aschbacher–Smith F.4.3 and F.4.49(3), printed pp.274,298–299 of
`refs/quasithin.pdf`. This adapter does not identify the Hall odd subgroup
with the native Borel and does not assert that the source product has order three.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven
variable (F : Type*) [Field F]

/-- All type-preserving extensions, with their whole marked endpoint intersection. -/
abbrev SourceExtension := UnitaryNonbinary.SourceExtension (pointParabolic F) (lineParabolic F)

variable {F}

abbrev Completion (E : SourceExtension F) (M : Type*) [Group M] :=
  RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M)

variable {M : Type*} [Group M]

/-- The actual F.4.49 quotient relation supplies cube membership in the whole
middle. The Hall subgroup here is not the native Borel or its Sylow two-subgroup. -/
theorem cube_mem_middle_of_hall_quotient (E : SourceExtension F) (c : Completion E M)
    (B : Subgroup M) (hB : B ≤ c.middle.range)
    (s t : normalizer (B : Set M))
    (horder : orderOf ((QuotientGroup.mk' (B.subgroupOf (normalizer (B : Set M)))) (s*t)) = 3) :
    (s.val*t.val)^3 ∈ c.middle.range := by
  apply hB
  have hp : ((QuotientGroup.mk' (B.subgroupOf (normalizer (B : Set M)))) (s*t))^3 = 1 :=
    horder ▸ pow_orderOf_eq_one _
  rw [←map_pow] at hp
  have hm : (s*t)^3 ∈ B.subgroupOf (normalizer (B : Set M)) :=
    (QuotientGroup.eq_one_iff ((s*t)^3)).mp hp
  exact hm
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven
