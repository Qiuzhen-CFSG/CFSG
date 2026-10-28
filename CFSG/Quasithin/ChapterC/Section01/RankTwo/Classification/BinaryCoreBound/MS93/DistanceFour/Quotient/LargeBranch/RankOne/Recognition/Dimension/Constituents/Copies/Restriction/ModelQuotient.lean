module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Linear.Group

/-!
# The specified rank-one quotient on the literal matrix parabolic

The source projection maps the supplied second parabolic onto its marked
SL3(2) model, with two-group kernel. That kernel is killed by the prescribed
rank-one quotient, whose kernel is the intrinsic two-core. Descending this
specific quotient therefore produces a surjection from the marked matrix
parabolic with exactly its intrinsic two-core as kernel.

This allows the finite matrix restriction calculation to use the specified
full SL2(2) action without unfolding its hidden definition or changing its
marking. Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12)(5), p.912.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Restriction
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}

/-- The original source projection restricted to the actual second parabolic. -/
noncomputable def modelProjection (f : Seed.Frame source) :
    f.parabolic true →* modelParabolic f.flag (!f.first) :=
  source.projection.subgroupComap _

/-- This projection retains the original matrix value. -/
theorem modelProjection_apply (f : Seed.Frame source) (m : f.parabolic true) :
    (modelProjection f m : SL) = source.projection m := by rfl

/-- Every element of the marked matrix parabolic lifts through the source. -/
theorem modelProjection_surjective (f : Seed.Frame source) :
    Function.Surjective (modelProjection f) :=
  source.projection.subgroupComap_surjective_of_surjective _ source.projection_surjective

private theorem modelProjection_kernel_two (f : Seed.Frame source) :
    IsPGroup 2 (modelProjection f).ker := by
  have hk : (modelProjection f).ker =
      source.projection.ker.comap (f.parabolic true).subtype := by
    ext x
    change (⟨source.projection x, _⟩ : modelParabolic f.flag (!f.first)) = 1 ↔
      source.projection x = 1
    exact Subtype.ext_iff
  rw [hk, source.projection_kernel]
  exact pCore_isPGroup.comap_of_injective _ (f.parabolic true).subtype_injective

private theorem modelProjection_kernel_le [Finite M] (f : Seed.Frame source) :
    (modelProjection f).ker ≤ (parabolicQuotient f true).ker := by
  rw [parabolicQuotient_kernel]
  exact le_sSup ⟨inferInstance, modelProjection_kernel_two f⟩

/-- Descend the already prescribed rank-one quotient to the matrix parabolic. -/
noncomputable def modelQuotient [Finite M] (f : Seed.Frame source) :
    modelParabolic f.flag (!f.first) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  (modelProjection f).liftOfSurjective (modelProjection_surjective f)
    ⟨parabolicQuotient f true, modelProjection_kernel_le f⟩

/-- The new model quotient agrees with the given quotient on every actual lift. -/
theorem modelQuotient_apply [Finite M] (f : Seed.Frame source) (m : f.parabolic true) :
    modelQuotient f (modelProjection f m) = parabolicQuotient f true m :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- The model quotient still covers full SL2(2), including the involutions. -/
theorem modelQuotient_surjective [Finite M] (f : Seed.Frame source) :
    Function.Surjective (modelQuotient f) := by
  intro a
  obtain ⟨m, rfl⟩ := parabolicQuotient_surjective f true a
  exact ⟨modelProjection f m, modelQuotient_apply f m⟩

/-- Descending through the two-group kernel preserves the exact intrinsic
matrix-parabolic two-core kernel. -/
theorem modelQuotient_kernel [Finite M] (f : Seed.Frame source) :
    (modelQuotient f).ker = pCore 2 (modelParabolic f.flag (!f.first)) := by
  apply Subgroup.comap_injective (modelProjection_surjective f)
  rw [MonoidHom.comap_ker]
  have he : (modelQuotient f).comp (modelProjection f) = parabolicQuotient f true :=
    MonoidHom.ext (modelQuotient_apply f)
  rw [he, parabolicQuotient_kernel,
    (modelProjection f).comap_pCore_of_ker_isPGroup
      (modelProjection_surjective f) (modelProjection_kernel_two f)]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Restriction
