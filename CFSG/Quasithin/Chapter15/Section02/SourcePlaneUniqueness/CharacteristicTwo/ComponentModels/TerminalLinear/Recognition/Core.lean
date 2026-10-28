module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Setup
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import Theory.SpecificGroups.PSL4Two.SchurMultiplier
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.GroupTheory.PerfectCentralCoverPGroupKernel

/-!
# The actual core-to-star marking in binary degree four and five

The C.2.7 map from X/O₂(X) onto its star image is a perfect central cover.
The multipliers of PSL₄(2) and PSL₅(2) are two-groups, so its kernel lies
in the trivial two-core. Thus the actual map is an isomorphism, retaining
its formula on original component elements and supplying simplicity for
the action on the original reduced submodule.

Source: Aschbacher--Smith C.2.7(1),(3)(h), pp.145--147.
-/

public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {M I X : Subgroup G} {n : ℕ}

/-- The binary parabolic marking kills the central core-to-star kernel.
The multiplier is a two-group, while X/O₂(X) has trivial two-core. -/
theorem BinaryBranch.coreToStar_injective (b : BinaryBranch M I X n) :
    Function.Injective (coreToStar b.source.normalizes) := by
  obtain ⟨e,_⟩ := b.parabolic
  let Q := X ⧸ pCore 2 X
  let : IsQuasisimple Q := b.source.quasisimple
  let f := coreToStar b.source.normalizes
  let c : Cover Q PSL(n,ZMod 2) := {
    toMonoidHom := e.toMonoidHom.comp f
    surjective := e.surjective.comp (coreToStar_surjective b.source.normalizes)
    isPerfect := inferInstance
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      exact ChapterC.C27Source.coreToStar_ker_central_from_source b.source }
  let : Group.IsPerfect PSL(n,ZMod 2) := Group.IsPerfect.ofSurjective c.surjective
  have hp : IsPGroup 2 (universalProjection PSL(n,ZMod 2)).ker := by
    rcases b.degree with h | h <;> subst n
    · exact (IsPGroup.of_card (show Nat.card (Multiplicative (ZMod 2)) = 2 ^ 1 by simp)).of_equiv
        (Matrix.PSL4Two.schurMultiplierEquivTwo (ZMod 2) (by simp) (MulEquiv.refl _)).symm
    · rw [Theory.SpecificGroups.PSL5Two.UniversalCover.field_universalProjection_ker_eq_bot
        (ZMod 2) (by simp)]
      exact IsPGroup.of_subsingleton 2 _
  have hf := c.injective_of_pCore_eq_bot_of_universal_pGroup
    (universalCover PSL(n,ZMod 2)) universalCover_isUniversal hp
    (pCore_quotient_pCore_eq_bot 2)
  exact fun x y h => hf (congrArg e h)

/-- This equivalence is the actual C.2.7 quotient map. -/
@[expose] def BinaryBranch.coreStarEquiv (b : BinaryBranch M I X n) :
    (X ⧸ pCore 2 X) ≃* starImage X ((M ⊓ I).pCoreIn 2) X :=
  MulEquiv.ofBijective (coreToStar b.source.normalizes)
    ⟨b.coreToStar_injective,coreToStar_surjective b.source.normalizes⟩

@[simp] theorem BinaryBranch.coreStarEquiv_mk (b : BinaryBranch M I X n) (x : X) :
    b.coreStarEquiv (QuotientGroup.mk' (pCore 2 X) x) = toStarImage X ((M ⊓ I).pCoreIn 2) x := rfl

/-- The source core quotient is simple, as required for the original-U marking. -/
theorem BinaryBranch.coreQuotient_simple (b : BinaryBranch M I X n) :
    IsSimpleGroup (X ⧸ pCore 2 X) := by
  obtain ⟨e,_⟩ := b.parabolic
  let : IsSimpleGroup PSL(n,ZMod 2) :=
    Atlas.psl_simple_high_rank n (by rcases b.degree with rfl | rfl <;> decide)
  exact (b.coreStarEquiv.trans e).isSimpleGroup

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
