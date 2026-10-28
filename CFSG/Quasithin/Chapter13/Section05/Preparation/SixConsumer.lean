module
public import CFSG.Quasithin.Chapter13.Section05.Preparation.NaturalSix
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySixSeed

/-!
# Applying the natural-six preparation to the original seed closure

Lift the earlier central-quotient marking, select the original invariant
flag, and apply the completed ordinary-A₆ nonabelian-seed exclusion. The
result keeps V and its literal point normalizer. The earlier trivial-fixed-
space and natural-quotient classification inputs remain explicit.
Source: Aschbacher–Smith 13.5.2, 13.5.12 and 13.7.2, pp.915,918,935–936.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.Preparation
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual ordinary-A₆ consumer of the constructed natural setup. -/
theorem exists_six_setup_with_abelian_seed
    (hmax : Maximal (Counterexample T) L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (e : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6))
    (e₂ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : D.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (ha : ∀ (l : L) v, a (D.chosenCentralAction l v) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
        (e (QuotientGroup.mk' (centralCore L) l)) (a v))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    ∃ V₁ V₂ V₃ : Subgroup G,
      Nonempty (NaturalSetup T L V V₁ V₂ V₃
        (normalizer (L : Set G)) (normalizer (V₁ : Set G))) ∧
      IsMulCommutative (conjugateSpanBy V₃ (normalizer (V₁ : Set G))) := by
  obtain ⟨V₁,V₂,V₃,⟨d⟩⟩ := exists_six_setup_of_fixed_quotient hmax.1 D e a ha hTV hfixed
  exact ⟨V₁,V₂,V₃,⟨d⟩,
    Chapter14.Section08.LieTypeBranch.original_six_seed_span_abelian d hmax e₂⟩
end CFSG.Quasithin.Chapter13.Section05.Preparation
