module

public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Models
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Preparation
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Centralizers
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six.Recognition
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel
public import Theory.GroupTheory.Commutator.Basic

/-!
# The marked degree-six extraspecial model

The degree-six output of G.9.4 is a marked subgroup of the concrete
`3^(1+2).SD16` model.  This file records the transport which is needed by
the source proof: once the actual group and module have been identified with
that model, the marked subgroup and the intertwining map give
`ExtraspecialRealization` literally.  The concrete model application is
proved below for every subgroup containing the marked four-extension.

The GL₆(2) normalizer recognition of an arbitrary source action is a separate
source theorem.  It is therefore kept as the explicit `ExtraspecialRealization`
input to the final CaseFive consumer; no model identification is hidden in a
record or asserted from the dimension alone.

The imported `Six.Recognition` proves the concrete Heisenberg centralizer,
the resulting generalized-Fitting identity, the local cyclic-centralizer
restriction, and the conditional assembly from core coordinates and marked
normalizer placement. The core reduction, module comparison, and placement
theorems remain independent proof obligations.

Source: Aschbacher--Smith, G.9.4(5), printed p.355 (PDF p.366), together
with the marked model in
`Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel`.
-/

@[expose] public section

open Representation Subgroup

namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A : Subgroup G}

namespace Six

open Representation.RankTwo.ExtraspecialModel

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Transport data for the marked extraspecial realization.  The subgroup is
kept as an actual subgroup of the concrete model, as required by the output
predicate in `Models.lean`. -/
theorem extraspecialRealization_of_intertwining
    (H : Subgroup Representation.RankTwo.ExtraspecialModel.Model)
    (hH : Representation.RankTwo.ExtraspecialModel.fourExtension ≤ H)
    (e : G ≃* H)
    (f : V ≃ₗ[ZMod 2] Representation.RankTwo.ExtraspecialModel.BinaryAction.V)
    (he : ∀ g v,
      f (ρ g v) =
        Representation.RankTwo.ExtraspecialModel.BinaryAction.representation
          (e g) (f v)) :
    ExtraspecialRealization ρ := by
  exact ⟨H, hH, ⟨e, f, he⟩⟩

/-- The concrete model and its represented linear image are genuinely
equivalent actions.  This is the model comparison used when the source group
has first been embedded into the binary image. -/
theorem binaryModel_quasiequivalent :
    Quasiequivalent
      Representation.RankTwo.ExtraspecialModel.BinaryAction.representation
      (Representation.RankTwo.ExtraspecialModel.BinaryAction.imageRepresentation
        Representation.RankTwo.ExtraspecialModel.BinaryAction.binaryImage) := by
  refine ⟨Representation.RankTwo.ExtraspecialModel.BinaryAction.modelEquiv,
    LinearEquiv.refl (ZMod 2) _, ?_⟩
  intro g v
  change Representation.RankTwo.ExtraspecialModel.BinaryAction.representation g v =
    (Representation.RankTwo.ExtraspecialModel.BinaryAction.modelEquiv g :
      Representation.RankTwo.ExtraspecialModel.BinaryAction.V ≃ₗ[ZMod 2]
        Representation.RankTwo.ExtraspecialModel.BinaryAction.V) v
  have he :=
    congrArg (fun q :
      (Representation.RankTwo.ExtraspecialModel.BinaryAction.V →ₗ[ZMod 2]
        Representation.RankTwo.ExtraspecialModel.BinaryAction.V) => q v)
      (Representation.RankTwo.ExtraspecialModel.BinaryAction.modelEquiv_representation g)
  exact he.symm

/-- A subgroup containing the marked four-extension is already a CaseFive
model for its concrete six-dimensional binary action.  The marked subgroup,
group equivalence and intertwining linear equivalence are all explicit. -/
theorem binary_caseFive
    (H : Subgroup Representation.RankTwo.ExtraspecialModel.Model)
    (hH : Representation.RankTwo.ExtraspecialModel.fourExtension ≤ H) :
    CaseFive
      (Representation.RankTwo.ExtraspecialModel.BinaryAction.representation.comp H.subtype)
      2 := by
  refine ⟨rfl, Representation.RankTwo.ExtraspecialModel.BinaryAction.finrank_vector, ?_⟩
  refine ⟨H, hH, ?_⟩
  refine ⟨MulEquiv.refl H, LinearEquiv.refl (ZMod 2) _, ?_⟩
  intro g v
  rfl

/-- The CaseFive branch once the source normalizer argument has supplied the
actual marked model comparison.  The numerical hypotheses are retained in
the consumer so that the theorem can be used directly by the G.9.4 assembly;
the model comparison is the only independent recognition premise. -/
theorem caseFive_of_model
    (_h : FittingHypothesis K ρ A 2)
    (_data : ThreeCoreData ρ A 2)
    (_reduce : ThreeSectionReducibilityInput.{u})
    (_hcore : IsPGroup 3
      (⁅(fittingSubgroup G : Subgroup G), (A : Subgroup G)⁆ : Subgroup G))
    (hdim : Module.finrank (ZMod 2) V = 6)
    (hmodel : ExtraspecialRealization ρ) :
    CaseFive ρ 2 := by
  exact ⟨rfl, hdim, hmodel⟩

end Six

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
