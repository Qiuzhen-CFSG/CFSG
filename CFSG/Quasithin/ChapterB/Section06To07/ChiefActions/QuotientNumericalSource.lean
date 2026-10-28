module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.NumericalSource
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import Theory.Representation.BinaryOffender.QuasisimpleImage
import all CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.NumericalSource

/-!
# Chief-action ratios from the original SQTK cover

The B.6.9 numerical argument applies to a faithful action with an actual SQTK
cover. Passing an irreducible action to its image gives trivial two-core; a
nontrivial such image inherits the original minimal-parabolic structure. Its
cover is the original group with the literal action kernel. The solvable-image
case follows from B.1.8. Thus every original irreducible chief action has ratio
at least one, without asserting SQTK closure under arbitrary quotients.

The `import all` of `NumericalSource` deliberately shares the private numerical
case proofs with this second source entry point, preserving their public API.
Source: Aschbacher--Smith B.6.9(1) and D.1.2(5), printed pp.115 and 173.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterB
open SourceInduction QuasisimpleSource
universe u
variable {H W : Type u} [Group H] [Finite H] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The faithful numerical bound with its actual SQTK cover. -/
theorem minimalParabolic_covered_faithful_quadraticRatio_ge_one
    (hcover : Nonempty (SQTKQuotient KnownSimple.IsKnownSimple H))
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (ρ : Representation (ZMod 2) H W) [Representation.IsIrreducible ρ]
    (hfaith : Function.Injective ρ) :
    1 ≤ quadraticRatio (imageRepresentation ρ) := by
  have hcore : pCore 2 H = ⊥ := by
    have hk := normal_p_subgroup_le_ker ρ (pCore 2 H) pCore_isPGroup
    exact bot_unique (hk.trans ((MonoidHom.ker_eq_bot_iff _).mpr hfaith).le)
  by_contra hlt
  have hltρ : quadraticRatio ρ < 1 := by
    rw [← QuasisimpleSource.SourceCompletion.image_ratio_of_faithful ρ hfaith]
    exact lt_of_not_ge hlt
  have hstrong : IsStrongFFModule ρ :=
    (isStrongFFModule_iff_quadraticRatio_lt_one ρ).mpr hltρ
  have hff : IsFFModule ρ := by
    obtain ⟨A,hA⟩ := hstrong
    exact ⟨A, ⟨hA.1, hA.2.le⟩⟩
  by_cases hs : Group.IsSolvable H
  · exact (not_lt_of_ge (solvable_irreducible_image_ratio_ge_one ρ hs)) (lt_of_not_ge hlt)
  · have hsrc := nonsolvable_offender_natural_source ρ T hP hs hfaith hff hcore hcover
    rcases hsrc with ⟨hqs,⟨c,_⟩⟩ | ⟨d,hd₁,hd₂⟩
    · exact (section_not_strong ρ T hP hff hcore hqs c) hstrong
    · obtain ⟨_,_,_,hmodel⟩ := source_offender_two_factor_shared_natural
        ρ T hP hff hcore d
      rcases hmodel with ⟨F,⟨c⟩⟩ | ⟨c⟩
      · exact (pair_not_strong ρ _ F c) hstrong
      · obtain ⟨c⟩ := c
        exact (SourceTwoFactorCase.MarkedProduct.symmetric_not_strong ρ _ c) hstrong

/-- The B.6.9 bound for the literal image of any original irreducible action. -/
theorem minimalParabolic_irreducible_image_quadraticRatio_ge_one
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (ρ : Representation (ZMod 2) H W) [Representation.IsIrreducible ρ] :
    1 ≤ quadraticRatio (imageRepresentation ρ) := by
  let q := actionHom ρ
  let σ := imageRepresentation ρ
  let := imageRepresentation_irreducible ρ (inferInstance : IsIrreducible ρ)
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hr : quadraticRatio (imageRepresentation σ) = quadraticRatio σ :=
    SourceCompletion.image_ratio_of_faithful σ (imageRepresentation_injective ρ)
  by_cases hs : Group.IsSolvable (actionImage ρ)
  · rw [← hr]
    exact solvable_irreducible_image_ratio_ge_one σ hs
  · have hn : q.ker ≠ ⊤ := by
      intro he
      have hall (x : actionImage ρ) : x = 1 := by
        obtain ⟨g,rfl⟩ := hq x
        exact (show g ∈ q.ker from he ▸ mem_top g)
      exact hs (Group.isSolvable_of_comm (fun a b => by rw [hall a, hall b]))
    have hp := (minimalParabolic_reduced_image T hP q hq
      (irreducible_image_twoCore_eq_bot ρ) hn).2
    let c : SQTKQuotient KnownSimple.IsKnownSimple (actionImage ρ) := {
      Cover := H
      kernel := q.ker
      sqtk := hH
      equiv := QuotientGroup.quotientKerEquivOfSurjective q hq }
    rw [← hr]
    exact minimalParabolic_covered_faithful_quadraticRatio_ge_one ⟨c⟩
      (T.mapSurjective hq) hp σ (imageRepresentation_injective ρ)

end CFSG.Quasithin.ChapterB
