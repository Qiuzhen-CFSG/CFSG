module
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation.Core
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Solvability.SylowProfiles.Rudvalis.InvolutionFibers

/-!
# Applying genuine Theorem C to the source component quotients

Theorem C supplies a listed model only after nonabelian simplicity, strong
quasithinness and the full K-group hypothesis have been established. The
checked model adapter gives outer solvability and even order; the intrinsic
Rudvalis Sylow calculation discharges its remaining model premise. For a
C-component, Theorem A supplies the actual semisimple radical quotient.

Source: Aschbacher--Smith, A.2.3, A.3.9(1) and A.3.12, pp.33,46--48.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents
open Subgroup Theory.GroupTheory
universe u

/-- The genuine universal Theorem C implies the precise simple-SQTK predicate
used by component generation and containment, with all model facts supplied. -/
theorem source_model_inputs_of_theoremC
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremC KnownSimple.IsKnownSimple X) :
    ∀ (S : Type u) [Group S] [Finite S], IsSimpleGroup S → ¬ IsMulCommutative S →
      IsSQTK KnownSimple.IsKnownSimple S →
      Group.IsSolvable (MulAut.Outer S) ∧ Even (Nat.card S) := by
  intro S _ _ hsimple hna hsq
  let : IsSimpleGroup S := hsimple
  let : Group.IsPerfect S := ⟨
    (Subgroup.Normal.eq_bot_or_eq_top (H := commutator S) inferInstance).resolve_left
      (fun hbot => hna ((commutator_eq_bot_iff S).mp hbot))⟩
  exact source_model_outer_isSolvable_even
    (fun hRu => @Chapter1.XiEmbedding.OuterModels.rudvalis_outer_isSolvable_of_involution_fibers hRu)
    hna ((hC S) hsimple hna hsq.stronglyQuasithin hsq.isKGroup)

/-- Apply genuine A and C to the literal solvable-radical quotient of an
original C-component, retaining its section map and full K-group inheritance. -/
theorem source_model_inputs_on_cComponent_of_theoremC
    {G : Type u} [Group G] [Finite G]
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (L : Subgroup G) (hL : L.IsCComponent) :
    Group.IsSolvable (MulAut.Outer (L ⧸ solvableRadical L)) ∧
      Even (Nat.card (L ⧸ solvableRadical L)) :=
  source_model_inputs_of_theoremC hC _ hL.isSimpleGroup_quotient_solvableRadical
    hL.not_isMulCommutative_quotient_solvableRadical
    (GenerationCore.radical_quotient_sqtk hA hG hL)

end CFSG.Quasithin.ChapterA.Section03.SourceComponents
