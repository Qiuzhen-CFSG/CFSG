module
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SourceGenerators
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SourceQuadraticActor
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SourceChiefActions

/-!
# The solvable qrc source alternatives

The original non-FF qrc hypotheses construct an elementary conjugate span,
a quadratic maximal elementary actor outside O₂(G₂), the exact chief-action
kernels, and the finite filtration by literal conjugates of V. Solvability
gives the chief-image ratios at least one, and the filtration proves the
original ratio at most two whenever there are multiple noncentral factors.

Splitting an actual chief series now gives all five qrc alternatives used
in the inside-core source route, including every unique-factor structural
clause. No additional actor, generator, rank, or classification input remains.
The outside-core alternative is retained explicitly; its separate module
classification and ratio-hat consequences are not asserted here.

Source: Aschbacher–Smith D.1.2–5, printed pp.172–177.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}

theorem source_solvable_multiple_ratio
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn G₂)
    (hs : Group.IsSolvable G₂)
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
  have hf := source_solvable_chief_actions d hne hV hff hs S hS s
  obtain ⟨n,W,hgen,hgenRatio⟩ := exists_conjugateGenerator_sequence d hV
    (A ⊓ pCore 2 G₂) inf_le_right
  have hq : 1 < quadraticRatio ρ := lt_of_not_ge fun h => hff
    ((isFFModule_iff_quadraticRatio_le_one ρ).mpr h)
  exact MultipleFactors.rank_bound_of_action_images U s S A (pCore 2 G₂)
    hUS hA hAR hc hquad hk (fun i hi => (hf i).2 hi A hA.1)
    (fun i _ => (hf i).1) (quadraticRatio ρ) hq W n hgen hgenRatio

/-- The five actual qrc alternatives when the second local group is solvable. -/
theorem source_solvable_qrc_cases
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥) (hs : Group.IsSolvable G₂) :
    letI := d.module_elementary
    let ρ := imageRepresentation G₁ V d.module_normalized
    (¬ V ≤ twoCoreIn G₂) ∨
    (quadraticRatio ρ ≤ 1 ∧ IsFFModule ρ) ∨
    DualFF d ∨
    (quadraticRatio ρ ≤ 2 ∧ IsElementaryAbelian 2 (conjugateSpan G₂ V) ∧
      ∃ s : SeriesOn ((conjugateSpan G₂ V).subgroupOf G₂), 1 < s.noncentralCount) ∨
    (HasUniqueNoncentralChiefFactor G₂ V ∧ StructuralConclusion G₁ G₂ T V) := by
  let := d.finite_left
  let := d.finite_right
  let := d.module_elementary
  let : Finite V := Finite.of_injective (inclusion d.module_le) (inclusion_injective d.module_le)
  let f := actionHom G₁ V d.module_normalized
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let ρ := imageRepresentation G₁ V d.module_normalized
  by_cases hV : V ≤ twoCoreIn G₂
  · right
    by_cases hff : IsFFModule ρ
    · exact Or.inl ⟨(isFFModule_iff_quadraticRatio_le_one ρ).mp hff,hff⟩
    right
    let := source_elementary_span_of_notFF d hV hff
    let U := (conjugateSpan G₂ V).subgroupOf G₂
    obtain ⟨s⟩ := SeriesOn.exists_series U
    have hn := noncentralCount_ne_zero d hne hV s
    by_cases hc : s.noncentralCount = 1
    · have hu : HasUniqueNoncentralChiefFactor G₂ V := ⟨s,hc⟩
      rcases source_uniqueFactor_cases d hV hu with h | hd | ht
      · exact (hff h.2).elim
      · exact Or.inl hd
      · exact Or.inr (Or.inr ⟨hu,ht⟩)
    · have hm : 1 < s.noncentralCount := by omega
      exact Or.inr (Or.inl ⟨source_solvable_multiple_ratio d hne hV hs s hm,
        inferInstance,s,hm⟩)
  · exact Or.inl hV
end CFSG.Quasithin.ChapterD.UniqueFactor
