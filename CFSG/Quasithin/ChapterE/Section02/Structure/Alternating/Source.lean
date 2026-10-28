module
public import CFSG.Quasithin.ChapterE.Section02.Structure.Alternating.Models
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSourceCases

/-!
# Removing the alternating disjunct from the original E.2.2 source cases

Apply the proved alternating sieve to the literal normal simple image of
K in H/J. The original prescribed quotient Sylow and its minimal-parabolic
property are retained. Every alternating case now enters the actual Bender
or derived binary symplectic row; no alternating case remains unresolved.
The independent odd-characteristic and sporadic rows remain explicit.

Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- The original normal star-component cases with the alternating family discharged. -/
theorem source_normal_component_cases_no_alternating
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (D : Type u) [Group D] [Finite D], ChapterA.Section02.TheoremC κ D)
    (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    let D := K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))
    ChapterA.Section02.IsTheoremCOddModel D ∨
    ClassificationModels.IsBenderModel D ∨
    (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL D 3 (2^f)) ∨
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp D 2 (2^f)) ∨
    Nonempty (D ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) ∨
    ChapterA.Section02.IsTheoremCSporadicModel D := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let D := K.map q
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  rcases source_normal_component_cases hA hC hH T hP hs K hK hgen with ha | h
  · have hd := source_normal_simple_image T hP hs K hK hgen
    let : IsSimpleGroup D := hd.1
    let : D.Normal := hd.2.2.1
    have hmin : ChapterB.IsMinimalParabolicOver S ⊤ :=
      ChapterB.minimalParabolic_surjective_core T hP q (QuotientGroup.mk'_surjective J)
        (by rw [QuotientGroup.ker_mk'])
    have hds : D ⊔ (S : Subgroup (H ⧸ J)) = ⊤ := hd.2.2.2
    rcases Alternating.source_rows S D hd.2.1 hds hmin ha with hb | hb
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb))))
  · exact h

end CFSG.Quasithin.ChapterE.Structure
