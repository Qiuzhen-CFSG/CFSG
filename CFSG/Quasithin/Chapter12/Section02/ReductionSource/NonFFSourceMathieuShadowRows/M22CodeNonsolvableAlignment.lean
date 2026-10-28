module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeChiefSieve
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.ChiefImageAlignment
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeChiefSieve
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeParabolicInputs
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# Common quotient actor on the original M22-code chief factors

For any faithful irreducible chief action of a nonsolvable minimal parabolic,
the image is nonsolvable: its kernel embeds in the solvable canonical core.
When two such actions have the same kernel, their first-isomorphism
equivalence intertwines the original homomorphisms and carries every original
subgroup image to the matching subgroup image.

Applied under the temporary inside-core branch for M22 code, this aligns the
literal quotient actors of all original noncentral chief factors. It does not
identify their natural modules; the same-offender module comparison and the
3.1.9(6) Cartan argument remain separate obligations.

Source: Aschbacher--Smith, 3.1.9(5--6), pp.577--578, and B.6.9.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal


namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD ChapterD.UniqueFactor NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- In the nonsolvable original M22-code inside-core branch, every noncentral
chief image is nonsolvable and all such images have one literal quotient
actor, preserving their original subgroup actions. -/
theorem sourceOrbit_m22_code_inside_core_nonsolvable_alignment
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2)
    (hs : ¬ Group.IsSolvable H) :
    let U := (conjugateSpan H D.sourceOrbit).subgroupOf H
    ∃ hU : IsElementaryAbelian 2 U,
      let := hU
      (∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
        ¬ Group.IsSolvable (actionImage (s.factorRepresentation i))) ∧
      (∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
        ∀ (t : SeriesOn U) (j : Fin t.series.length), ¬ t.Central j →
            Nonempty (CFSG.Quasithin.Chapter8.MathieuShadowRows.LiteralChiefActionEquiv
              (s.factorRepresentation i) (t.factorRepresentation j))) := by
  obtain ⟨hU, A, hA, hAR, hquad, hrank, hmin, hchief⟩ :=
    D.sourceOrbit_m22_code_inside_core_large_chief_actor
      h hmany hV hnon d hH hcore
  let : IsElementaryAbelian 2 ((conjugateSpan H D.sourceOrbit).subgroupOf H) := hU
  have hp := D.original_minimal_parabolic h hmany hV hnon d hH hcore
  let S := T.subtype hH.1.1.2
  have hSQTK := Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1
  refine ⟨hU, ?_⟩
  constructor
  · intro s i hi
    let := s.factorRepresentation_irreducible i
    have hff : IsFFModule (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) :=
      ⟨actionSubgroup (s.factorRepresentation i) A, (hchief s i hi).1⟩
    intro hsolv
    have hiff := CFSG.Quasithin.Chapter8.MathieuShadowRows.chief_image_solvable_iff
      S hp (s.factorRepresentation i) hff
    exact hs (hiff.mp hsolv)
  · intro s i hi t j hj
    let := s.factorRepresentation_irreducible i
    let := t.factorRepresentation_irreducible j
    have hρ : IsFFModule (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) :=
      ⟨actionSubgroup (s.factorRepresentation i) A, (hchief s i hi).1⟩
    have hσ : IsFFModule (Representation.BinaryOffender.imageRepresentation (t.factorRepresentation j)) :=
      ⟨actionSubgroup (t.factorRepresentation j) A, (hchief t j hj).1⟩
    have hker : (Representation.BinaryOffender.actionHom (s.factorRepresentation i)).ker =
        (Representation.BinaryOffender.actionHom (t.factorRepresentation j)).ker := by
      rw [actionHom_ker_eq, actionHom_ker_eq,
        ChapterB.minimalParabolic_nonsolvable_chief_kernel
          (s.factorRepresentation i) hSQTK S hp hs hρ,
        ChapterB.minimalParabolic_nonsolvable_chief_kernel
          (t.factorRepresentation j) hSQTK S hp hs hσ]
    exact CFSG.Quasithin.Chapter8.MathieuShadowRows.chief_equiv_of_kernel_eq
      (s.factorRepresentation i) (t.factorRepresentation j) hker

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
