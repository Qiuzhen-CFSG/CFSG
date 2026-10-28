module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.QuotientNumericalSource
public import Theory.Representation.BinaryOffender.ChiefSectionBudget
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section

/-!
# Chief-section budgets for a reduced minimal parabolic

The kernel of a nontrivial irreducible action lies in the maximal core.
When the two-core vanishes, that core has odd order, so every elementary
two-actor remains faithful on the chief action. B.6.9 and the strict budget
of a faithful non-FF submodule then force every perfect subgroup to act
trivially on its quotient whenever the original cubic ratio is at most two.

Source: Aschbacher--Smith B.6.8(5--6), B.6.9(1), and 9.2.2(1).
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
variable {H W : Type*} [Group H] [Finite H]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem minimalParabolic_irreducible_elementary_faithful
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (hc : pCore 2 H = ⊥)
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ]
    (hn : ∃ h w, ρ h w ≠ w)
    (A : Subgroup H) (hA : IsPGroup 2 A) :
    ∀ a ∈ A, (∀ w, ρ a w = w) → a = 1 := by
  have hk : ρ.ker ≤ minimalParabolicCore T hP :=
    minimalParabolic_source6a T hP ρ (irreducible_residual_not_le_ker ρ hn)
  obtain ⟨S,hS⟩ := minimalParabolic_twoCore_sylow_core T hP
  have hSb : (S : Subgroup (minimalParabolicCore T hP)) = ⊥ := by
    rw [hS,hc,bot_subgroupOf]
  let : (S : Subgroup (minimalParabolicCore T hP)).Normal := by rw [hSb]; infer_instance
  let : Unique (Sylow 2 (minimalParabolicCore T hP)) := Sylow.unique_of_normal S inferInstance
  obtain ⟨P,hP'⟩ := (hA.to_le (show A ⊓ ρ.ker ≤ A from inf_le_left)).comap_subtype.exists_le_sylow
  have hPb : P = S := Subsingleton.elim _ _
  intro a ha hfix
  have haK : a ∈ ρ.ker := by
    change ρ a = 1
    apply LinearMap.ext
    intro w
    exact hfix w
  have hmem : (⟨a,hk haK⟩ : minimalParabolicCore T hP) ∈ P := hP' ⟨ha,haK⟩
  rw [hPb] at hmem
  change (⟨a,hk haK⟩ : minimalParabolicCore T hP) ∈ (S : Subgroup _) at hmem
  rw [hSb,mem_bot] at hmem
  exact congrArg Subtype.val hmem

open SourceInduction
universe u
variable {H W : Type u} [Group H] [Finite H]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- B.6.9 for the literal irreducible image with an original SQTK cover. -/
theorem covered_irreducible_image_quadraticRatio_ge_one
    (hcover : Nonempty (SQTKQuotient KnownSimple.IsKnownSimple H))
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ] :
    1 ≤ quadraticRatio (imageRepresentation ρ) := by
  let q := actionHom ρ
  let σ := imageRepresentation ρ
  let := imageRepresentation_irreducible ρ (inferInstance : IsIrreducible ρ)
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hr : quadraticRatio (imageRepresentation σ) = quadraticRatio σ :=
    QuasisimpleSource.SourceCompletion.image_ratio_of_faithful σ (imageRepresentation_injective ρ)
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
    obtain ⟨c⟩ := hcover
    let f := q.comp (c.equiv.toMonoidHom.comp (QuotientGroup.mk' c.kernel))
    have hf : Function.Surjective f := hq.comp (c.equiv.surjective.comp
      (QuotientGroup.mk'_surjective _))
    let d : SQTKQuotient KnownSimple.IsKnownSimple (actionImage ρ) := {
      Cover := c.Cover
      kernel := f.ker
      sqtk := c.sqtk
      equiv := QuotientGroup.quotientKerEquivOfSurjective f hf }
    rw [← hr]
    exact minimalParabolic_covered_faithful_quadraticRatio_ge_one ⟨d⟩
      (T.mapSurjective hq) hp σ (imageRepresentation_injective ρ)

/-- A cubic bound of two leaves no moved perfect section above a faithful non-FF submodule. -/
theorem perfect_fixes_quotient_of_nonFF_and_cubic_le_two
    (hcover : Nonempty (SQTKQuotient KnownSimple.IsKnownSimple H))
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hc : pCore 2 H = ⊥)
    (ρ : Representation (ZMod 2) H W) (U : Subrepresentation ρ)
    (hf : Function.Injective U.toRepresentation)
    (hnU : ¬ IsFFModule (imageRepresentation U.toRepresentation))
    (hb : cubicRatio ρ ≤ 2) (K : Subgroup H) [Group.IsPerfect K] :
    K ≤ U.quotientRepresentation.ker := by
  by_contra hmove
  obtain ⟨W,N,hi,hn⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect K hmove
  let := hi
  have hn' : ∃ h w, N.quotientRepresentation h w ≠ w := by
    by_contra! he
    exact hn (fun k _ => LinearMap.ext (he k))
  have hw := covered_irreducible_image_quadraticRatio_ge_one hcover T hP
    N.quotientRepresentation
  obtain ⟨A,hA,_,ha⟩ := (cubicRatio_le_nat_iff ρ 2).mp hb
  have hu : ∀ a ∈ A, (∀ v, U.toRepresentation a v = v) → a = 1 := by
    intro a _ hh
    apply hf
    apply LinearMap.ext
    intro v
    simpa only [map_one,Module.End.one_apply] using hh v
  have hfaith := minimalParabolic_irreducible_elementary_faithful T hP hc
    N.quotientRepresentation hn' A hA.2.isPGroup
  exact (not_lt_of_ge ha)
    (twice_rank_lt_fixedCodim_of_nonFF_and_chief_subquotient ρ U W N A hA hu hfaith hnU hw)

end CFSG.Quasithin.ChapterB

