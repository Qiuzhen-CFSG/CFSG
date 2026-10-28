module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleFiveAlpha
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleOrbitSpan
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairSourceOrbitSpan
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SolvableOrbitSpan
/-!
# Complete original-source linear conclusions in E.2.3

The full known-simple B.5 theorem supplies the actual natural factors.
Every linear branch, including the complete solvable case, now carries
both Baumann Sylow and the exact moved-alpha and residual orbit identities.
Only the original marked symmetric-five alternatives are retained for
C.1.24, with their source sections and the same prescribed-Sylow exchange.
No earlier classification or linear geometry premise remains.
Source: Aschbacher–Smith E.2.3(2)–(3), printed pp.216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

abbrev SourceLinearConclusions (T : Sylow 2 G) (U : Subgroup G) : Prop :=
  Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
    (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
  thompsonAlpha (T : Subgroup G) =
    ((⁅U,pResidual 2 G⁆ : Subgroup G) ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⊔
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ∧
  conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
    (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G))

abbrev SymmetricFiveSingleSource
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q) (hker : q.ker = centralizer (U : Set G)) : Prop :=
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  IsQuasisimple (generalizedFitting Y) ∧
    ∃ c : ProjectiveLine.QuasisimpleSourceConclusion (α.comp Y.subtype) (generalizedFitting Y),
      Nonempty (MarkedActionEquiv c.sectionData.action (offenderSubgroup c.sectionData.action)
        (generalizedFitting Y) (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))

attribute [local instance] RankOneBaumann.semilinear_moved_elementary

private theorem linear_conclusions_of_sylow_and_span
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : IsPReduced 2 U)
    (hs : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (pResidual 2 G ⊔ baumann (T : Subgroup G)))
    (hspan : conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G))) :
    SourceLinearConclusions T U := by
  exact ⟨hs, RankOneBaumann.thompsonAlpha_decomposition_of_orbit_span T _
    ((commutator_le_left U (pResidual 2 G)).trans
      (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T))) _ hspan, hspan⟩

/-- All original linear cases are complete, and the remaining alternatives retain actual S5 source markers. -/
theorem source_linear_conclusions_or_symmetric_five
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set G)
    SourceLinearConclusions T U ∨
      SymmetricFiveSingleSource U (QuotientGroup.mk' C)
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) ∨
      SymmetricFivePairSource T U (QuotientGroup.mk' C)
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) := by
  classical
  let := hU.normal
  let := hU.elementary
  by_cases hs : Group.IsSolvable G
  · let := hs
    have hr := hG.stronglyQuasithin 3 (by decide) (by decide)
    exact Or.inl (linear_conclusions_of_sylow_and_span T U hU
      (source_solvable_baumann_sylow_and_alpha T hP U hU hJ hr inferInstance).1
      (source_solvable_orbit_span T hP U hU hJ hr inferInstance))
  · let C := centralizer (U : Set G)
    let q := QuotientGroup.mk' C
    have hq : Function.Surjective q := QuotientGroup.mk'_surjective C
    have hk : q.ker = centralizer (U : Set G) := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    rcases source_nonsolvable_natural_factors hG T hP U hU hs hJ with
      ⟨hqs,c,hlin|hfive⟩ | ⟨d,_,_⟩
    · obtain ⟨F,hF⟩ := hlin
      exact Or.inl (linear_conclusions_of_sylow_and_span T U hU
        (quasisimple_linear_baumann_of_section T hP U hU hJ q hq hk hqs c.sectionData F hF).1
        (quasisimple_linear_orbit_span_of_section T hP U hU hJ q hq hk hqs c.sectionData F hF))
    · exact Or.inr (Or.inl ⟨hqs,c,hfive⟩)
    · let := offenderSubgroup_normal α
      have hcore : pCore 2 (G ⧸ C) = ⊥ := hU.quotient_pCore_eq_bot
      have hn : q.ker ≠ ⊤ := by
        intro he
        exact hJ (hk ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
      have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
      have hff : IsFFModule α := by
        obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hk T
        · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
        · exact hff
      obtain ⟨t,ht₁,ht₂,hkind⟩ := source_offender_two_factor_shared_natural α (T.mapSurjective hq) hp hff hcore d
      rcases hkind with ⟨F,⟨c⟩⟩ | hfive
      · exact Or.inl (linear_conclusions_of_sylow_and_span T U hU
          (paired_baumann_of_source_model T hP U hU hJ q hq hk d F c ⟨t,ht₁,ht₂⟩).1
          (paired_orbit_span_of_source_model T hP U hU hJ q hq hk d F c ⟨t,ht₁,ht₂⟩))
      · exact Or.inr (Or.inr ⟨d,t,ht₁,ht₂,hfive⟩)

/-- The single symmetric-five branch includes its exact alpha and actual index-two Sylow span. -/
abbrev SourceSingleFiveConclusions (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) : Prop :=
  thompsonAlpha (T : Subgroup G) =
    ((⁅U,pResidual 2 G⁆ : Subgroup G) ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⊔
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ∧
  ∃ S₁ : Subgroup G,
    IsSylowSubgroupIn S₁ (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
    baumann (T : Subgroup G) ≤ S₁ ∧
    ((baumann (T : Subgroup G)).subgroupOf S₁).index = 2 ∧
    S₁ ≤ conjugateSpanBy (baumann (T : Subgroup G))
      (pResidual 2 G ⊓ minimalParabolicMax T hP)

/-- The original source now needs geometry only for the same marked symmetric-five pair. -/
theorem source_complete_geometry_or_paired_five
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set G)
    SourceLinearConclusions T U ∨ SourceSingleFiveConclusions T hP U ∨
      SymmetricFivePairSource T U (QuotientGroup.mk' C)
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) := by
  let := hU.normal
  let := hU.elementary
  rcases source_linear_conclusions_or_symmetric_five hG T hP U hU hJ with
    h | ⟨hqs,c,⟨e⟩⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl
      ⟨quasisimple_five_source_alpha T hP U hU hJ _
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hqs c.sectionData e,
       quasisimple_five_source_conclusions T hP U hU hJ _
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hqs c.sectionData e⟩)
  · exact Or.inr (Or.inr h)
end CFSG.Quasithin.ChapterE.ThompsonAction
