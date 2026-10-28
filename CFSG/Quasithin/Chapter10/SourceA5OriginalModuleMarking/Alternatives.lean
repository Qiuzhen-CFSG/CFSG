module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.Recognition
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.CentralCover
public import Theory.Representation.BinaryConjugationSection.Relabel
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Projective
public import Theory.Representation.ProjectivityTransport

/-!
# The two original A₅ module markings after the source choice

For a Fundamental Setup whose actual moved central quotient is irreducible,
classify its faithful A₅ action and retain the original component quotient
and subgroup inclusions. The natural SL₂(4) branch marks W/C_W(L); the
projective deleted-permutation branch has C_W(L)=1 and marks W itself.

The irreducibility input is explicit. D.3.21 permits two natural constituents
before the new choice of V in 3.2.6, so this theorem does not assert that
input for an arbitrary fixed Fundamental Setup. The choice producer must
supply it for the particular D passed to the consumer.
Source: Aschbacher–Smith, 3.2.6 and 10.1.1, printed pp.581 and 741;
projectivity is I.1.5–6, printed p.408.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
local instance originalAlternativesMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance originalAlternativesFieldFourAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

/-- Actual natural quotient or whole deleted-permutation marking, preserving
all original actor and subgroup maps for the chosen irreducible setup. -/
theorem source_a5_original_module_alternatives_of_irreducible
    (hi : (originalMovedQuotientAction D e).IsIrreducible) :
    (∃ f : alternatingGroup (Fin 5) ≃*
        SL(2,Representation.OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
        (sourceMovedFixed D)
        (Representation.SL2.BinarySmall.natural.comp
          (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))) ∨
    (sourceMovedFixed D = ⊥ ∧
      ∃ f : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5),
      Nonempty (Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
        (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp
          (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let ρ := originalMovedQuotientAction D e
  let c := originalMovedQuotientSection D e
  rcases (source_a5_original_quotient_alternatives_of_irreducible D e hi).2 with
    ⟨f,⟨E⟩⟩ | ⟨f,⟨E⟩⟩
  · exact Or.inl ⟨f,⟨c.relabel q E⟩⟩
  · let : Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5)))
        Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.asModule :=
      BinaryPermutation.alternatingFive_natural_projective
    let : Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5))) ρ.asModule :=
      Representation.projective_of_group_module_equiv ρ
        Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation
        f E.toLinearEquiv (fun g v =>
          Representation.IntertwiningMap.isIntertwining ρ _ E.toIntertwiningMap g v)
    have hz := source_original_moved_fixed_eq_bot_of_projective D e ρ c
    refine Or.inr ⟨hz,f,?_⟩
    have hh := c.relabel q E
    rw [hz] at hh
    exact ⟨hh⟩
end CFSG.Quasithin.Chapter10
