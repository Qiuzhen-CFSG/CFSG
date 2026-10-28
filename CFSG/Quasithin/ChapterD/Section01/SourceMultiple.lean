module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.QuotientNumericalSource
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SourceGenerators
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SourceQuadraticActor
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SourceChiefActions

/-!
# The SQTK multiple-chief-factor ratio bound

For each literal chief action on the conjugate span of V, the original SQTK
group supplies B.6.9's faithful quotient cover and hence ratio at least one.
The noncentral factors have the original Sylow kernel A ∩ O₂(G₂). Together
with the quadratic actor and conjugate-generator filtration, these bounds
give q ≤ 2 when the span has at least two noncentral chief factors.

This removes the solvability restriction from the numerical branch used in
the original Chapter 3 and Chapter 15 source applications. The concrete
quotients, Sylow subgroup, and action conventions remain those of D.1.
Source: Aschbacher--Smith D.1.2(5), D.1.3(1), and 3.1.6, printed pp.173--175,
573--575; the SQTK hypothesis is the sufficient case stated on p.173.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterD.MultipleFactors
variable {H : Type*} [Group H] [Finite H]
  (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]

/-- B.6.9 on each original chief factor, with no faithful-action premise. -/
theorem source_sqtk_chief_image_ratio_ge_one
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (s : SeriesOn U) (i : Fin s.series.length) :
    1 ≤ quadraticRatio (imageRepresentation (s.factorRepresentation i)) := by
  let := s.factorRepresentation_irreducible i
  exact ChapterB.minimalParabolic_irreducible_image_quadraticRatio_ge_one
    hH T hP (s.factorRepresentation i)
end CFSG.Quasithin.ChapterD.MultipleFactors

namespace CFSG.Quasithin.ChapterD.UniqueFactor
open NoncentralChiefRefinement
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}
/-- The chief ratios and exact Sylow kernels required by D.1.3. -/
theorem source_sqtk_chief_actions
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn G₂)
    (hnf : letI := d.module_elementary
      ¬ IsFFModule (imageRepresentation G₁ V d.module_normalized))
    (hG₂ : IsSQTK KnownSimple.IsKnownSimple G₂) :
    let U := (conjugateSpan G₂ V).subgroupOf G₂
    letI := source_elementary_span_of_notFF d hV hnf
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le G₂))
    ∀ (S : Sylow 2 G₂), (S : Subgroup G₂).map G₂.subtype = T →
      ∀ (s : SeriesOn U) (i : Fin s.series.length),
        1 ≤ quadraticRatio (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) ∧
          (¬ s.Central i → ∀ A : Subgroup G₂, A ≤ S →
            A ⊓ (s.factorRepresentation i).ker = A ⊓ pCore 2 G₂) := by
  let := d.finite_right
  let U := (conjugateSpan G₂ V).subgroupOf G₂
  let := source_elementary_span_of_notFF d hV hnf
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le G₂))
  dsimp only
  intro S hS s i
  exact ⟨MultipleFactors.source_sqtk_chief_image_ratio_ge_one U hG₂ S
      (source_intrinsic_minimalParabolic_of_notFF d hne hnf S hS) s i,
    fun hi A hA => MultipleFactors.source_chief_sylow_kernel U S
      (source_intrinsic_minimalParabolic_of_notFF d hne hnf S hS) s i hi A hA⟩
end CFSG.Quasithin.ChapterD.UniqueFactor

namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}

/-- D.1.3(1) for the original SQTK second local group. -/
theorem source_sqtk_multiple_ratio
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn G₂)
    (hG₂ : IsSQTK KnownSimple.IsKnownSimple G₂)
    (s : SeriesOn ((conjugateSpan G₂ V).subgroupOf G₂)) (hc : 1 < s.noncentralCount) :
    letI := d.module_elementary
    quadraticRatio (imageRepresentation G₁ V d.module_normalized) ≤ 2 := by
  let := d.finite_left
  let := d.finite_right
  let := d.module_elementary
  let : Finite V := Finite.of_injective (inclusion d.module_le) (inclusion_injective d.module_le)
  let f := actionHom G₁ V d.module_normalized
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let ρ := imageRepresentation G₁ V d.module_normalized
  by_cases hff : IsFFModule ρ
  · exact ((isFFModule_iff_quadraticRatio_le_one ρ).mp hff).trans (by norm_num)
  let := source_elementary_span_of_notFF d hV hff
  let U := (conjugateSpan G₂ V).subgroupOf G₂
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le G₂))
  obtain ⟨S,hS⟩ := d.sylow_right
  obtain ⟨A,hA,hAR,hquad⟩ := source_quadratic_max_actor d hne hV hff S hS
  have hUS : U ≤ S := by
    intro u hu
    have ht : (u : G) ∈ T := (right_core_le_sylow d) ((span_le_right_core d hV) hu)
    rw [← hS] at ht
    obtain ⟨s,hs,he⟩ := ht
    exact G₂.subtype_injective he ▸ hs
  have hk : A ⊓ centralizer (U : Set G₂) ≤ pCore 2 G₂ :=
    (inf_le_inf_right _ hA.1).trans (source_span_centralizer_sylow_le_core d hne hV hff S hS)
  have hf := source_sqtk_chief_actions d hne hV hff hG₂ S hS s
  obtain ⟨n,W,hgen,hgenRatio⟩ := exists_conjugateGenerator_sequence d hV
    (A ⊓ pCore 2 G₂) inf_le_right
  have hq : 1 < quadraticRatio ρ := lt_of_not_ge fun h => hff
    ((isFFModule_iff_quadraticRatio_le_one ρ).mpr h)
  exact MultipleFactors.rank_bound_of_action_images U s S A (pCore 2 G₂)
    hUS hA hAR hc hquad hk (fun i hi => (hf i).2 hi A hA.1)
    (fun i _ => (hf i).1) (quadraticRatio ρ) hq W n hgen hgenRatio

end CFSG.Quasithin.ChapterD.UniqueFactor

