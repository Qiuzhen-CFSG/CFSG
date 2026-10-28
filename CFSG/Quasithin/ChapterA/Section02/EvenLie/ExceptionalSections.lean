module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ParabolicSections
public import Theory.SpecificGroups.LieType.A02ParabolicSections
public import Theory.SpecificGroups.LieType.A02ParabolicSections.BinaryTargets

/-!
# The marked exceptional-section obstruction under A.2 induction

A proper two-local normalizer in the actual central quotient lifts to a
proper two-local of the original group. We pull back the stored section map
and apply smaller-section induction to its literal kernel quotient. This
quotient lives in the original group's universe; the concrete target may
live in any universe. Its quasisimplicity makes it a semisimple section.

The three binary applications discharge all intrinsic target hypotheses
using the checked projective models Sp₆(2), Ω₈⁺(2), and Ω₆⁻(2). They retain
the actual local-section construction as an input. In particular this file
does not yet construct exceptional parabolics or assert the full A.2.18
exclusions for F₄, E₆, E₇, E₈, or twisted E₆.

Source: Aschbacher–Smith A.2.15(2) and the first paragraph of A.2.18,
printed pp.37–40 of `refs/quasithin.pdf`; GLS3 §2.6 supplies the separate
parabolic and subsystem geometry.
-/

public section

namespace CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections
open Theory.GroupTheory Theory.SpecificGroups.LieType

universe u v w
variable {G : Type u} {H : Type v} {S : Type w}
  [Group G] [Finite G] [Group H] [Group S] [Finite S]

private theorem semisimple_of_quasisimple (T : Type*) [Group T] [IsQuasisimple T] :
    IsSemisimple T := by
  let : IsQuasisimple (⊤ : Subgroup T) :=
    IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm
  exact top_unique (le_sSup (show IsComponent T ⊤ from ⟨.top, inferInstance⟩))

/-- Apply A.2.15(2) to the actual lifted numerator's quotient. No universe
restriction on the marked model, or quasithinness of G/Z(G), is required. -/
theorem rank_bound_of_marked_section [IsQuasisimple S]
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    (e : (G ⧸ Subgroup.center G) ≃* H) (d : NormalizerSection H S)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) : primeRank p S ≤ 2 := by
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hs : IsSectionOf S (Subgroup.normalizer (d.twoSubgroup : Set H)) :=
    ⟨d.numerator, d.quotient, d.onto⟩
  obtain ⟨M, hM, hl, _, hS⟩ :=
    exists_proper_twoLocal_section_lift π hπ d.proper d.isTwoLocal hs
  obtain ⟨U, f, hf⟩ := hS
  let eS : (U ⧸ f.ker) ≃* S := QuotientGroup.quotientKerEquivOfSurjective f hf
  let : IsQuasisimple (U ⧸ f.ker) := IsQuasisimple.of_mulEquiv eS.symm
  have hlocal : primeRank p M ≤ 2 :=
    Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG M hl p hp ho
  have hA := ih M (IsProperSectionOf.subgroup M hM)
  have hbound := (hA (hG.subgroup M) (hK.subgroup M) (U ⧸ f.ker)
    (.quotient_subgroup U f.ker) (semisimple_of_quasisimple _) p hp ho).2 hlocal
  calc
    primeRank p S = primeRank p (U ⧸ f.ker) := (primeRank_equiv p eS).symm
    _ ≤ 2 := hbound.trans hlocal

/-- The literal projective Sp₆(2) section contradicts the source induction bound. -/
theorem false_of_binary_symplectic_section
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    (e : (G ⧸ Subgroup.center G) ≃* H)
    (d : NormalizerSection H (Theory.SpecificGroups.SymplecticSix.PSp (ZMod 2))) : False := by
  let := BinarySectionTargets.symplectic_quasisimple
  exact (not_le_of_gt BinarySectionTargets.symplectic_rank)
    (rank_bound_of_marked_section ih hG hK e d 3 (by decide) (by decide))

/-- The literal projective Ω₈⁺(2) section contradicts the source induction bound. -/
theorem false_of_binary_splitEight_section
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    (e : (G ⧸ Subgroup.center G) ≃* H)
    (d : NormalizerSection H (ClassicalOrthogonal.POmegaPlus 4 (ZMod 2))) : False := by
  let := BinarySectionTargets.splitEight_quasisimple
  exact (not_le_of_gt BinarySectionTargets.splitEight_rank)
    (rank_bound_of_marked_section ih hG hK e d 3 (by decide) (by decide))

/-- The literal projective Ω₆⁻(2) section also suffices, for a unitary Levi
comparison that constructs this exact carrier rather than an abstract label. -/
theorem false_of_binary_minusSix_section
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    (e : (G ⧸ Subgroup.center G) ≃* H)
    (d : NormalizerSection H (ClassicalGroup.POmegaMinus 3 (ZMod 2))) : False := by
  let := BinarySectionTargets.minusSix_quasisimple
  exact (not_le_of_gt BinarySectionTargets.minusSix_rank)
    (rank_bound_of_marked_section ih hG hK e d 3 (by decide) (by decide))

end CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections
