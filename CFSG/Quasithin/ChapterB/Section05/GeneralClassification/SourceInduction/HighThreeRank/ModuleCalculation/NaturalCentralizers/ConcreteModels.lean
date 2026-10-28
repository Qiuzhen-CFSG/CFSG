module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.MarkedTransport
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.ConcreteModels.CoreNormalizer

/-!
# Concrete commutants and the original moved-space decomposition

The natural A₆ and A₇ actions and the nonsplit A₆ augmentation core all have
scalar endomorphisms. Over the binary field their automorphism commutants are
therefore trivial. These calculations construct `ModelCommutants` without any
ambient classification hypothesis. The application below transports them along
the given marked model to the original [V,L] and proves its disjoint moved-space
decomposition with the actual three-core.

The accompanying normalizer theorem concerns the literal action on the full
five-dimensional augmentation core, retaining its fixed line.

Source: Aschbacher–Smith, B.5.7, final paragraph, printed p.106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.ConcreteModels

/-- All concrete commutants required by the marked B.5.7 module alternatives. -/
theorem modelCommutants : ModelCommutants where
  natural n hn := by
    rcases hn with rfl | rfl
    · intro f hf
      exact equiv_eq_refl_of_scalar f
        (CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.commuting_endomorphism_scalar
          f.toLinearMap hf)
    · intro f hf
      exact equiv_eq_refl_of_scalar f (natural_seven_scalar f.toLinearMap hf)
  coreSix := by
    intro f hf
    exact equiv_eq_refl_of_scalar f (core_six_scalar f.toLinearMap hf)

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}

/-- The source decomposition on the original action, with its model commutants discharged. -/
theorem moved_decomposition {L A : Subgroup G}
    (hL : IsComponent G L) (d : NoncentralContext K G L)
    (m : SymmetricMovedModel ρ L A) :
    moved ρ (L ⊔ pCore 3 G) = moved ρ L ⊔ moved ρ (pCore 3 G) ∧
      Disjoint (moved ρ L) (moved ρ (pCore 3 G)) ∧
      moved ρ (pCore 3 G) ≤ fixedSpace ρ L :=
  model_moved_decomposition ρ modelCommutants hL d m

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.ConcreteModels
