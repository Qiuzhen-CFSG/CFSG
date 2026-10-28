module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.NaturalSource
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairNatural
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.WreathActor
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors.Rank
public import Theory.Representation.NormalComponentConstituents
public import Theory.Representation.BinaryOffender.IrreducibleResidual
public import Theory.Representation.BinaryOffender.QuasisimpleImage

/-!
# The natural alternatives for a literal irreducible FF action

Pass the original irreducible module to its faithful action image. Its
nontrivial reduced quotient inherits minimal parabolicity and the original
SQTK cover, so the proved B.6.9 source classification applies. In the
solvable case A.1.31 bounds the number of natural factors using the original
surjection; their transitivity gives the full S₃ or S₃≀C₂ action. The other
cases retain the actual single or paired SL₂ or S₅ natural coordinates.
Irreducibility makes the offender moved space the entire original module.

This supplies the earlier classification in3.1.9(5); excluding larger fields
uses its additional centralizer hypothesis and is a separate source step.
Source: Aschbacher–Smith B.6.9 and3.1.9, printed pp.115–116 and577–578.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
open SourceInduction QuasisimpleSource

/-- The genuine earlier B.6.9 alternatives on the actual faithful chief action. -/
def ChiefNaturalAlternatives {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W) : Prop :=
  ChapterB.SmallNaturalWreathAction ρ ∨
    (IsQuasisimple (generalizedFitting (offenderSubgroup ρ)) ∧
      ∃ c : ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ)),
        (∃ F : BinaryField, IsLinearNatural
          (c.sectionData.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype) F 2) ∨
        Nonempty (MarkedActionEquiv c.sectionData.action
          (offenderSubgroup c.sectionData.action) (generalizedFitting (offenderSubgroup ρ))
          (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))) ∨
    (∃ c : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype),
      (∃ F : BinaryField, Nonempty (c.MarkedProduct (linearNatural F 2))) ∨
        Nonempty (c.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5))))

universe u
theorem minimalParabolic_chief_natural_alternatives
    {D W : Type u} [Group D] [Finite D] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (hD : IsSQTK KnownSimple.IsKnownSimple D)
    (S : Sylow 2 D) (hS : ChapterB.IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule (Representation.BinaryOffender.imageRepresentation ρ)) :
    ChiefNaturalAlternatives (Representation.BinaryOffender.imageRepresentation ρ) ∧
      subspaceCommutator (Representation.BinaryOffender.imageRepresentation ρ) ⊤
        (offenderSubgroup (Representation.BinaryOffender.imageRepresentation ρ)) = ⊤ := by
  let q := actionHom ρ
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hf := imageRepresentation_injective ρ
  have hc := irreducible_image_twoCore_eq_bot ρ
  let := imageRepresentation_irreducible ρ (inferInstance : IsIrreducible ρ)
  have hn : q.ker ≠ ⊤ := by
    intro he
    obtain ⟨A,hA⟩ := hff
    obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1.1
    obtain ⟨g,hg⟩ := hq (a : actionImage ρ)
    apply ha
    apply Subtype.ext
    change (a : actionImage ρ) = 1
    rw [←hg]
    exact (show g ∈ q.ker from he ▸ mem_top g)
  have hp := (ChapterB.minimalParabolic_reduced_image S hS q hq hc hn).2
  let := offenderSubgroup_normal σ
  refine ⟨?_,subspaceCommutator_top_eq_top_of_normal_faithful_irreducible σ hf
    inferInstance _ (offenderSubgroup_ne_bot_of_ff σ hff)⟩
  by_cases hs : Group.IsSolvable (actionImage ρ)
  · obtain ⟨d,ht,hstable,hr,hgen⟩ :=
      source_solvable_minimalParabolic_factors (S.mapSurjective hq) hp hs hc hf hff
    have hcount := d.toSolvableFFFactors.count_eq_one_or_two_of_surjective_threeRank
      q hq (hD.stronglyQuasithin 3 (by decide) (by decide))
    exact Or.inl ((d.toSolvableFFFactors.small_natural_moved_action hf hc hr hcount
      (fun i j => let ⟨t,ht⟩ := ht i j; ⟨t,ht⟩)).wreath)
  · let c : SQTKQuotient KnownSimple.IsKnownSimple (actionImage ρ) := {
      Cover := D
      kernel := q.ker
      sqtk := hD
      equiv := QuotientGroup.quotientKerEquivOfSurjective q hq }
    rcases nonsolvable_offender_natural_source σ (S.mapSurjective hq) hp hs hf hff hc ⟨c⟩
      with hqs | ⟨d,hd₁,hd₂⟩
    · exact Or.inr (Or.inl hqs)
    · obtain ⟨t,ht₁,ht₂,hmodel⟩ := source_offender_two_factor_shared_natural
        σ (S.mapSurjective hq) hp hff hc d
      exact Or.inr (Or.inr ⟨d,hmodel⟩)


end CFSG.Quasithin.ChapterB
