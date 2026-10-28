module

public import CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.LocalActions.Inputs
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions

/-!
# Assembling the common marking of the two local actions

Parabolic generators identify the actual Sylow image with the displayed
four-group. The quaternion residual calculation supplies an unmarked cubic
normalizing this same image. The concrete normalizer calculation conjugates
that cubic to the specified cubic or its inverse by an element of the
four-group. This single change of coordinates preserves the parabolic image
and the marked central involution, and gives both exact local images.

All maps below use the literal N_G(A)/C_G(A). The final theorem is a
conditional assembly from the two generator contracts. Constructing those
contracts, and A = J(T_L), from the genuine split natural block and the
quaternion residual is still required; no split-case source conclusion is
asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007.
-/

open Subgroup

namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage

variable {G : Type*} [Group G]

/-- Changing coordinates conjugates the faithful quotient action. -/
public theorem coordinateAction_changeCoordinates (A : Subgroup G)
    (e : A ≃* BinaryFourSplitPair.E) (d : MulAut BinaryFourSplitPair.E) :
    coordinateAction A (e.trans d) =
      (MulAut.conj d).toMonoidHom.comp (coordinateAction A e) := by
  ext x v
  rfl

/-- The coordinate change acts on the image of the actual ambient actor. -/
public theorem actorImage_changeCoordinates (A P : Subgroup G)
    (e : A ≃* BinaryFourSplitPair.E) (d : MulAut BinaryFourSplitPair.E) :
    actorImage A P (e.trans d) = (actorImage A P e).map (MulAut.conj d).toMonoidHom := by
  rw [actorImage_eq_map, actorImage_eq_map, Subgroup.map_map,
    coordinateAction_changeCoordinates]

/-- The first two quotient generators identify the common embedded four-group. -/
public theorem ParabolicGenerators.sylow_image {A L₂ TL : Subgroup G} {z : A}
    (p : ParabolicGenerators A L₂ TL z) :
    actorImage A TL p.coordinates = BinaryFourSplitPair.overlap := by
  rw [actorImage_eq_map, p.sylow_generators, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, p.row_action, p.column_action]
  rfl

/-- Adding the actual third generator gives the full first local image. -/
public theorem ParabolicGenerators.parabolic_image {A L₂ TL : Subgroup G} {z : A}
    (p : ParabolicGenerators A L₂ TL z) :
    actorImage A (L₂ ⊔ TL) p.coordinates = BinaryFourSplitPair.parabolic := by
  rw [actorImage_eq_map, p.parabolic_generators, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, p.row_action, p.column_action,
    p.cubic_action]
  rfl

/-- Combine the split parabolic calculation and the coordinate-free residual
cubic calculation. Neither exact model image nor a prescribed residual cubic
is a field of the supplied contracts. The source assembly must construct
these contracts on A = J(T_L). -/
public theorem markedLocalActions_of_generators {A L₂ TL K : Subgroup G} {z : A}
    (p : ParabolicGenerators A L₂ TL z) (q : QuaternionGenerators A K TL) :
    Nonempty (MarkedLocalActions A (L₂ ⊔ TL) (K ⊓ normalizer (A : Set G)) z) := by
  let f := coordinateAction A p.coordinates
  have hD : (quotientImage A TL).map f = BinaryFourSplitPair.overlap := by
    rw [← actorImage_eq_map]
    exact p.sylow_image
  have hn : f q.c ∈ normalizer (BinaryFourSplitPair.overlap : Set (MulAut BinaryFourSplitPair.E)) := by
    rw [← hD]
    exact (quotientImage A TL).le_normalizer_map f ⟨q.c, q.normalizes, rfl⟩
  have h3 : (f q.c) ^ 3 = 1 := by rw [← map_pow, q.cube, map_one]
  have hne : f q.c ≠ 1 := by
    intro h
    exact q.nonidentity (coordinateAction_injective A p.coordinates (h.trans f.map_one.symm))
  obtain ⟨d, _, hz, hP, hR⟩ := BinaryFourSplitPair.SplitBlockActions.align_cubic_extension
    (f q.c) hn h3 hne
  refine ⟨{
    coordinates := p.coordinates.trans d
    point_eq := ?_
    parabolic_normalizes := p.normalizes
    quaternion_normalizes := inf_le_right
    parabolic_image := ?_
    quaternion_image := ?_ }⟩
  · change d (p.coordinates z) = BinaryFourSplitPair.point
    rw [p.point_eq, hz]
  · rw [actorImage_changeCoordinates, p.parabolic_image]
    exact hP
  · rw [actorImage_changeCoordinates, actorImage_eq_map, q.generation,
      Subgroup.map_sup, hD, MonoidHom.map_zpowers]
    exact hR

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage
