module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Candidate
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Parabolics.Model
public import Theory.GroupTheory.PCoreSurjective

/-!
# The full second rank-one quotient and its literal action

For either member of the supplied incident frame, restrict source.projection
to its actual parabolic preimage. Lift the model quotient through its two-group
kernel. The resulting epimorphism to full SL2(2) has kernel exactly the
intrinsic two-core of that parabolic, without replacing it by its residual.

The second starred layer is invariant under this parabolic and fixed by its
two-core. Descending its representation through the units of the endomorphism
ring produces an actual SL2(2) action. Its equation retains the original
source.projection and the original radius quotient. Natural two-copy
coordinates remain a separate representation-theoretic obligation.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation on printed p.905 and (4.6.12)(5), printed pp.911--912.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R}

/-- The full rank-one quotient of either actual parabolic in the supplied frame. -/
noncomputable def parabolicQuotient (f : Seed.Frame source) (i : Bool) :
    f.parabolic i →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  let P := modelParabolic f.flag (if i then !f.first else f.first)
  (Classical.choice ((binaryWeakBN f.flag).rank_one _)).toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 P)).comp (source.projection.subgroupComap P))

/-- Every rank-one matrix has a lift in the actual supplied parabolic. -/
theorem parabolicQuotient_surjective (f : Seed.Frame source) (i : Bool) :
    Function.Surjective (parabolicQuotient f i) :=
  (Classical.choice ((binaryWeakBN f.flag).rank_one _)).surjective.comp
    ((QuotientGroup.mk'_surjective _).comp
      (source.projection.subgroupComap_surjective_of_surjective _ source.projection_surjective))

/-- The quotient kernel is the intrinsic parabolic two-core, with no extra factor. -/
theorem parabolicQuotient_kernel [Finite M] (f : Seed.Frame source) (i : Bool) :
    (parabolicQuotient f i).ker = pCore 2 (f.parabolic i) := by
  let P := modelParabolic f.flag (if i then !f.first else f.first)
  let π := source.projection.subgroupComap P
  have hπ : Function.Surjective π :=
    source.projection.subgroupComap_surjective_of_surjective _ source.projection_surjective
  have hk : π.ker = source.projection.ker.comap (f.parabolic i).subtype := by
    ext x
    change (⟨source.projection x, _⟩ : P) = 1 ↔ source.projection x = 1
    exact Subtype.ext_iff
  have hp : IsPGroup 2 π.ker := by
    rw [hk, source.projection_kernel]
    exact pCore_isPGroup.comap_of_injective _ (f.parabolic i).subtype_injective
  change (((Classical.choice ((binaryWeakBN f.flag).rank_one _)).toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 P)).comp π)).ker) = pCore 2 (P.comap source.projection)
  rw [MonoidHom.ker_comp_of_injective _ _
    (Classical.choice ((binaryWeakBN f.flag).rank_one _)).injective,
    ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact π.comap_pCore_of_ker_isPGroup hπ hp

variable {geometry : Geometry R}

/-- The second star as a subrepresentation of the original parabolic action. -/
noncomputable def secondParabolicRepresentation
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) :
    Subrepresentation (d.representation.comp
      (source.projection.comp (f.parabolic true).subtype)) where
  toSubmodule := Seed.secondTildeStar (geometry := geometry) d f 1
  apply_mem_toSubmodule m v hv := secondStar_normalized d f m m.property v hv

/-- The actual full-parabolic representation on the literal second star. -/
noncomputable def secondParabolicAction
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) :
    Representation (ZMod 2) (f.parabolic true)
      (Seed.secondTildeStar (geometry := geometry) d f 1) :=
  (secondParabolicRepresentation (geometry := geometry) d f).toRepresentation

/-- The core-fixed definition of the second star kills the whole intrinsic core. -/
theorem second_core_le_kernel (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) :
    pCore 2 (f.parabolic true) ≤
      (secondParabolicAction (geometry := geometry) d f).ker := by
  intro m hm
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change d.representation (source.projection m) v = (v : d.Space)
  have hc : Seed.secondCore f 1 = f.core true := by
    have he : (MulAut.conj (1 : M)).toMonoidHom = MonoidHom.id M := by
      ext x
      simp
    simp only [Seed.secondCore, he, Subgroup.map_id]
  have hv := Seed.secondTildeStar_le_fixed (geometry := geometry) d f 1 v.property
  rw [hc] at hv
  exact hv ⟨source.projection m, mem_map_of_mem _ (mem_map_of_mem _ hm)⟩

private theorem quotient_kernel_le [Finite M]
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) :
    (parabolicQuotient f true).ker ≤
      (secondParabolicAction (geometry := geometry) d f).asGroupHom.ker := by
  intro m hm
  apply Units.ext
  change secondParabolicAction (geometry := geometry) d f m = 1
  exact second_core_le_kernel d f ((parabolicQuotient_kernel f true).le hm)

private noncomputable def secondRankOneUnits [Finite M]
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) →*
      (Module.End (ZMod 2) (Seed.secondTildeStar (geometry := geometry) d f 1))ˣ :=
  (parabolicQuotient f true).liftOfSurjective (parabolicQuotient_surjective f true)
    ⟨(secondParabolicAction (geometry := geometry) d f).asGroupHom,
      quotient_kernel_le d f⟩

/-- Descend the actual second-star action to the full SL2(2) quotient. -/
noncomputable def secondRankOneAction [Finite M]
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) :
    Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (Seed.secondTildeStar (geometry := geometry) d f 1) :=
  (Units.coeHom _).comp (secondRankOneUnits d f)

/-- The descended action agrees with the original source projection on every lift. -/
theorem secondRankOneAction_apply [Finite M]
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (m : f.parabolic true) (v : Seed.secondTildeStar (geometry := geometry) d f 1) :
    (secondRankOneAction d f (parabolicQuotient f true m) v : d.Space) =
      d.representation (source.projection m) v := by
  have h : secondRankOneUnits (geometry := geometry) d f (parabolicQuotient f true m) =
      (secondParabolicAction (geometry := geometry) d f).asGroupHom m :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  exact congrArg (fun a : (Module.End (ZMod 2)
    (Seed.secondTildeStar (geometry := geometry) d f 1))ˣ =>
      (((a : Module.End (ZMod 2)
        (Seed.secondTildeStar (geometry := geometry) d f 1)) v) : d.Space)) h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
