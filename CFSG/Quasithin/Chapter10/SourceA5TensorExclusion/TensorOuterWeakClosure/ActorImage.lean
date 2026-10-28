module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorActorRank
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorThompsonActor

/-!
# The original tensor actor in the full normalizer

The general-linear equivalence identifies the range of the original
normalizer-valued action with its existing maximal-local linear image.
It preserves cardinality and hence elementary rank, and carries the inner
action image to the determinant group's linear range. The original outer
hypothesis therefore transfers to the exact matrix-normalizer subgroup.

This connects the source rank entrance to the outer geometry in
Aschbacher–Smith 9.4.5, printed pp.736–737.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The actual normalizer actor has the rank of the original linear image. -/
theorem normalizerActor_rank {A : Subgroup G} (hAM : A ≤ D.maximalLocal) :
    rank (m.maximalNormalizerAction.comp (inclusion hAM)).range =
      rank ((A.subgroupOf D.maximalLocal).map m.maximalAction) := by
  let f := m.maximalNormalizerAction.comp (inclusion hAM)
  let eqv := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Binary.V
  let p : linearNormalizer Binary.action →* (Binary.V ≃ₗ[ZMod 2] Binary.V) :=
    eqv.toMonoidHom.comp (linearNormalizer Binary.action).subtype
  have heval (a : A) : p (f a) = m.maximalAction ⟨a,hAM a.property⟩ := by
    apply LinearEquiv.ext
    intro v
    exact m.maximalNormalizerAction_apply ⟨a,hAM a.property⟩ v
  have he : f.range.map p = (A.subgroupOf D.maximalLocal).map m.maximalAction := by
    ext t
    constructor
    · rintro ⟨b,⟨a,rfl⟩,rfl⟩
      exact ⟨⟨a,hAM a.property⟩,a.property,(heval a).symm⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨f ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,heval ⟨a,ha⟩⟩
  change rank f.range = _
  rw [←he]
  unfold rank
  rw [card_map_of_injective (eqv.injective.comp (linearNormalizer Binary.action).subtype_injective)]

/-- An outer original image stays outer under the literal normalizer action. -/
theorem normalizerActor_outer {A : Subgroup G} (hAM : A ≤ D.maximalLocal)
    (houter : ¬ (A.subgroupOf D.maximalLocal).map m.maximalAction ≤ Binary.linearAction.range) :
    ¬ (m.maximalNormalizerAction.comp (inclusion hAM)).range.map
      (linearNormalizer Binary.action).subtype ≤ actionImage Binary.action := by
  intro h
  apply houter
  rintro t ⟨a,ha,rfl⟩
  let b : A := ⟨a,ha⟩
  let f := m.maximalNormalizerAction.comp (inclusion hAM)
  have hb : (f b).val ∈ f.range.map (linearNormalizer Binary.action).subtype :=
    ⟨f b,⟨b,rfl⟩,rfl⟩
  obtain ⟨g,hg⟩ := h hb
  refine ⟨g,?_⟩
  apply LinearEquiv.ext
  intro v
  have hv := congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) Binary.V => u.val v) hg
  change Binary.action g v = normalizerRepresentation Binary.action
    (m.maximalNormalizerAction a) v at hv
  rwa [m.maximalNormalizerAction_apply] at hv

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
