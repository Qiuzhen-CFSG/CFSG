module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.OddResidual
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.SourceTheorems
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Preparation

/-!
# The original ratio-one cyclic actor has a three-group residual

At cubic ratio one, every original rank-one starred actor is a best FF
offender. Starred generation therefore identifies the whole acting group
with its offender subgroup. The proved solvable FF structure embeds that
group into a product of S₃ factors, so its two-residual is a three-group.
No moved-space hypothesis or classification of an arbitrary cover is used.

Source: Aschbacher--Smith D.2.23 and the restriction in 15.1.2, p.1084.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
open Theory.GroupTheory
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- At ratio one the original cyclic starred actors are best FF offenders. -/
theorem CoreHypotheses.ratioOne_offenderSubgroup (h : CoreHypotheses ρ)
    (hq : cubicRatio ρ = 1) : offenderSubgroup ρ = ⊤ := by
  have hnot : ¬ IsStrongFFModule ρ := by
    intro hs
    have hlo : 1 ≤ quadraticRatio ρ := hq ▸ cubicRatio_le_quadraticRatio ρ
    exact not_lt_of_ge hlo ((isStrongFFModule_iff_quadraticRatio_lt_one ρ).mp hs)
  apply top_unique
  rw [←h.generated]
  apply sSup_le
  intro A hA
  apply IsBestOffender.le_offenderSubgroup ρ
  apply (isBestOffender_iff_of_not_strong ρ hnot A).mpr
  refine ⟨hA.1.2.1,?_⟩
  have he := (starred_codimension ρ hA (h.rank_one A hA)).trans hq
  rw [h.rank_one A hA]
  exact_mod_cast he

/-- The full original actor has a normal three-group residual in the ratio-one case. -/
theorem CoreHypotheses.ratioOne_residual_threeGroup (h : CoreHypotheses ρ)
    (hs : Group.IsSolvable G) (hq : cubicRatio ρ = 1) :
    IsPGroup 3 (pResidual 2 G) := by
  have ho := h.ratioOne_offenderSubgroup ρ hq
  have hff : IsFFModule ρ := by
    obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr h.ratio_le
    refine ⟨A,hA.1.2.1,?_⟩
    have he := (starred_codimension ρ hA (h.rank_one A hA)).trans hq
    have he' : fixedCodim ρ A = 1 := by exact_mod_cast he
    rw [he',h.rank_one A hA]
  obtain ⟨d⟩ := ChapterB.solvableFFStructure_nonempty ρ hs h.twoCore h.faithful hff
  let f : G →* offenderSubgroup ρ :=
    { toFun := fun g => ⟨g,ho.symm ▸ Subgroup.mem_top g⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  exact d.toSolvableFFFactors.pResidual_threeGroup_of_embedding f
    (fun _ _ he => congrArg Subtype.val he)
end CFSG.Quasithin.ChapterD.CyclicSource
