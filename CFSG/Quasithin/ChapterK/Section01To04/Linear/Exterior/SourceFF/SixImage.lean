module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.OrthogonalSix
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Assembly.OrthogonalAction
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.ModuleFactors.StabilizerActions

/-!
# The actual six-space image in the ten-dimensional exterior module

The six retained wedge coordinates intertwine the literal stabilizer action
with the exterior square of its upper SL₄(2) block. Faithfulness of the latter
allows the block map to descend through the actual action image. This embeds
Aut_G(V₆) in SL₄(2), with its six-dimensional exterior module, so the established
A₈ calculation excludes strong offenders on this image. The B.7.1 restriction
argument then forces every minimal best offender stabilizing V₆ to centralize it.

Source: Aschbacher–Smith, K.3.2.3, printed p.455/PDF p.466, using the actual
parabolic and exterior-coordinate comparisons in 12.5.2(4).
-/

public noncomputable section

open Representation Representation.BinaryOffender
open Representation.SL5TenDimensional Representation.SL5ExteriorSquare
open Atlas.Order20160A8
namespace CFSG.Quasithin.ChapterK.Linear.Exterior.SourceFF

private theorem exteriorMap_injective
    {g h : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)}
    (he : Bivectors.exteriorMap g.val = Bivectors.exteriorMap h.val) : g = h := by
  apply Atlas.Order20160A8.Exterior.binary_injective
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  change Atlas.Order20160A8.Exterior.coordinates
      (Bivectors.exteriorMap g.val (Atlas.Order20160A8.Exterior.coordinates.symm w)) =
    Atlas.Order20160A8.Exterior.coordinates
      (Bivectors.exteriorMap h.val (Atlas.Order20160A8.Exterior.coordinates.symm w))
  rw [he]

private theorem stabilizer_intertwines
    (g : BinaryOffender.subspaceStabilizer (exteriorAction 2) V₆) (v : V₆) :
    v6Coordinates (subspaceImageRepresentation (exteriorAction 2) V₆
      (subspaceActionHom (exteriorAction 2) V₆ g) v) =
      Bivectors.exteriorMap (sixStabilizerNaturalProjection g).val (v6Coordinates v) :=
  v6Coordinates_action (sixStabilizerToParabolic g) v

private theorem action_kernel_le_block_kernel :
    (subspaceActionHom (exteriorAction 2) V₆).ker ≤
      sixStabilizerNaturalProjection.ker := by
  intro g hg
  apply exteriorMap_injective
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := v6Coordinates.surjective w
  change Bivectors.exteriorMap (sixStabilizerNaturalProjection g).val (v6Coordinates v) = _
  rw [← stabilizer_intertwines]
  have hv := congrArg
    (fun a => subspaceImageRepresentation (exteriorAction 2) V₆ a v) hg
  have hv' : subspaceImageRepresentation (exteriorAction 2) V₆
      (subspaceActionHom (exteriorAction 2) V₆ g) v = v := by
    simpa only [map_one, Module.End.one_apply] using hv
  rw [hv']
  rw [Matrix.SpecialLinearGroup.coe_one, Bivectors.exteriorMap_one, LinearMap.id_apply]

private theorem actionHom_surjective :
    Function.Surjective (subspaceActionHom (exteriorAction 2) V₆) :=
  (stabilizerRepresentation (exteriorAction 2) V₆).asGroupHom.rangeRestrict_surjective

/-- The upper block descends to the literal image of the action on V₆. -/
def sixImageActor : subspaceActionImage (exteriorAction 2) V₆ →*
    Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  (subspaceActionHom (exteriorAction 2) V₆).liftOfSurjective
    actionHom_surjective
    ⟨sixStabilizerNaturalProjection, action_kernel_le_block_kernel⟩

/-- The descended actor retains the upper block of each actual stabilizer element. -/
@[simp] theorem sixImageActor_actionHom
    (g : BinaryOffender.subspaceStabilizer (exteriorAction 2) V₆) :
    sixImageActor (subspaceActionHom (exteriorAction 2) V₆ g) =
      sixStabilizerNaturalProjection g := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

/-- The original six wedge coordinates intertwine the actual image action. -/
theorem sixImageActor_intertwines
    (g : subspaceActionImage (exteriorAction 2) V₆) (v : V₆) :
    v6Coordinates (subspaceImageRepresentation (exteriorAction 2) V₆ g v) =
      Bivectors.exteriorMap (sixImageActor g).val (v6Coordinates v) := by
  let a : BinaryOffender.subspaceStabilizer (exteriorAction 2) V₆ :=
    Classical.choose (actionHom_surjective g)
  have ha : subspaceActionHom (exteriorAction 2) V₆ a = g :=
    Classical.choose_spec (actionHom_surjective g)
  have hi := congrArg (fun b : subspaceActionImage (exteriorAction 2) V₆ =>
    v6Coordinates (subspaceImageRepresentation (exteriorAction 2) V₆ b v)) ha
  have hb := (sixImageActor_actionHom a).symm.trans (congrArg sixImageActor ha)
  exact hi.symm.trans ((stabilizer_intertwines a v).trans (congrArg
    (fun b : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) =>
      Bivectors.exteriorMap b.val (v6Coordinates v)) hb))

/-- No kernel remains after passing to the literal six-space action image. -/
theorem sixImageActor_injective : Function.Injective sixImageActor := by
  intro g h he
  apply subspaceImageRepresentation_injective (exteriorAction 2) V₆
  apply LinearMap.ext
  intro v
  apply v6Coordinates.injective
  exact (sixImageActor_intertwines g v).trans ((congrArg
    (fun b : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) =>
      Bivectors.exteriorMap b.val (v6Coordinates v)) he).trans
        (sixImageActor_intertwines h v).symm)

/-- The literal six-space action image has no strong offenders. -/
theorem sixImage_not_strong :
    ¬ IsStrongFFModule (subspaceImageRepresentation (exteriorAction 2) V₆) := by
  apply OrthogonalSix.not_strong_of_alternating_embedding
    (OrthogonalSix.sl4EquivAlternating.toMonoidHom.comp sixImageActor)
    (OrthogonalSix.sl4EquivAlternating.injective.comp sixImageActor_injective)
    (v6Coordinates.trans OrthogonalSix.exteriorEquivNatural)
  intro g v
  change OrthogonalSix.exteriorEquivNatural
    (v6Coordinates (subspaceImageRepresentation (exteriorAction 2) V₆ g v)) = _
  exact (congrArg OrthogonalSix.exteriorEquivNatural (sixImageActor_intertwines g v)).trans
    (OrthogonalSix.exteriorEquivNatural_intertwines (sixImageActor g) (v6Coordinates v))

/-- K.3.2.3: a minimal best offender preserving V₆ centralizes that same space. -/
theorem minimal_best_stable_centralizes
    {A : Subgroup Group} (hA : IsMinimalBestOffender (exteriorAction 2) A)
    (hstable : ∀ a ∈ A, ∀ w ∈ V₆, exteriorAction 2 a w ∈ V₆) :
    subspaceCommutator (exteriorAction 2) V₆ A = ⊥ := by
  by_contra hmove
  exact OrthogonalSix.exterior_restriction_exclusion sixImageActor sixImageActor_injective
    v6Coordinates sixImageActor_intertwines hA hstable hmove

/-- The fixed-space form of the actual K.3.2.3 restriction conclusion. -/
theorem minimal_best_stable_fixed
    {A : Subgroup Group} (hA : IsMinimalBestOffender (exteriorAction 2) A)
    (hstable : ∀ a ∈ A, ∀ w ∈ V₆, exteriorAction 2 a w ∈ V₆) :
    V₆ ≤ BinaryOffender.fixedSpace (exteriorAction 2) A :=
  (subspaceCommutator_eq_bot_iff (exteriorAction 2) V₆ A).mp
    (minimal_best_stable_centralizes hA hstable)

end CFSG.Quasithin.ChapterK.Linear.Exterior.SourceFF
