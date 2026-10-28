module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.BinaryDegree
public import Theory.Representation.BinaryOffender.ElementaryConjugateBudget
public import Theory.SpecificGroups.PSL2.ElevenConjugateBudget

/-!
# The PSL₂(11) exclusion from elementary conjugate generation

The actual quotient forces binary degree at least ten. A generation budget
of four for its elementary automorphism actors instead forces degree at most
eight at cubic ratio at most two. The lifting theorem retains arbitrary
compatible central covers, diagonal outer actors, and the original binary
representation; every conjugating operator comes from G.

The concrete generation theorem covers every nontrivial elementary
two-subgroup of the actual quotient's automorphism group, including mixed
four-groups. It discharges the generation premise below and proves the
unconditional source exclusion `two_lt_cubicRatio`.

This gives an alternative to the small-module and common
fixed-space calculation in GM02, *Classification of 2F-modules I*,
Proposition 4.1, manuscript pp.8--9, cited by Aschbacher--Smith K.2,
printed p.453. No classification of the small irreducible modules is needed.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Eleven
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- Once the concrete generation calculation is supplied, its source
application excludes PSL₂(11) with no additional module or covering premise. -/
theorem two_lt_cubicRatio_of_elementary_generation
    (hgen : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 11 →
      ElementaryInnerConjugateBudget
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) 4)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 11) :
    2 < cubicRatio ρ := by
  by_contra hn
  have hratio : cubicRatio ρ ≤ 2 := le_of_not_gt hn
  have hlo := ten_le_degree_eleven ρ h.faithful hm
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) :=
    h.quasisimple.simple
  let : Nontrivial (generalizedFitting G) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting G))).nontrivial
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hhi := finrank_le_of_cubicRatio_and_elementary_budget (a := 2) ρ
    (generalizedFitting G) h.faithful h.irreducible
    (fixedSpace_eq_bot_of_faithful_irreducible_restriction ρ _ h.faithful)
    e (hgen F hF) hratio
  omega

/-- The PSL₂(11) case of K.2: the original faithful binary action, irreducible
on its quasisimple generalized Fitting subgroup, has cubic ratio above two.
The actual quotient generation theorem discharges every extra premise of
the conditional bound, including for diagonal outer actors and central covers. -/
theorem two_lt_cubicRatio
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 11) :
    2 < cubicRatio ρ :=
  two_lt_cubicRatio_of_elementary_generation ρ h
    (fun F _ _ hF => Theory.PSL2.ElevenConjugateBudget.budget F hF) hm

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Eleven
