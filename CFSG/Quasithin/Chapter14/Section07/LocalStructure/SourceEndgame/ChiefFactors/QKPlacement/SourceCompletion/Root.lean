module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion

/-!
# The last actual source chief layer in 14.7.71

The marked image of the original conjugate span S is the Borel root four-group:
the source (*) inclusion gives one containment, and S ≤ Q together with Q* = R₁*
gives the other. Restricting the original qH and then using additive root
coordinates gives a surjective map with kernel S ∩ Q_H. Conjugation by the
original L₁ acts through its surjective Borel image, so this last layer is
irreducible and noncentral. No containment S ≤ L₁ is required.

Source: Aschbacher–Smith, Lemma 14.7.71, printed p.1075, equation (*) and the
last chief factor above Q_H.
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Representation.SL2FourNatural.BorelDualCore
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The original qH on L₁, with its exact marked Borel codomain. -/
def leftBorelMap (hb : CompatibleBorel d) : F.Li L 1 →* borel d.naturalQuotient :=
  (d.qH.comp (Subgroup.inclusion ((F.Li_le L 1).trans inf_le_right))).codRestrict _
    (fun l => hb.left_image ▸ Subgroup.mem_map.mpr
      ⟨Subgroup.inclusion ((F.Li_le L 1).trans inf_le_right) l, l.property, rfl⟩)

/-- Forgetting the codomain restriction retains the original qH map. -/
theorem leftBorelMap_val (hb : CompatibleBorel d) (l : F.Li L 1) :
    (leftBorelMap d hb l).val =
      d.qH (Subgroup.inclusion ((F.Li_le L 1).trans inf_le_right) l) := by rfl

theorem leftBorelMap_surjective (hb : CompatibleBorel d) :
    Function.Surjective (leftBorelMap d hb) := by
  intro b
  have hmem : b.val ∈ ((F.Li L 1).subgroupOf F.H).map d.qH :=
    hb.left_image.symm ▸ b.property
  obtain ⟨l, hl, he⟩ := hmem
  exact ⟨⟨l.val, hl⟩, Subtype.ext he⟩

/-- The root representation with the literal L₁ actor. -/
def rootRepresentation (hb : CompatibleBorel d) :
    Representation (ZMod 2) (F.Li L 1) SL2FourNatural.F :=
  (actorCore d.naturalQuotient (borel d.naturalQuotient)
    (borel d.naturalQuotient).le_normalizer).comp (leftBorelMap d hb)

theorem rootRepresentation_irreducible (hb : CompatibleBorel d) :
    IsIrreducible (rootRepresentation d hb) := by
  apply (irreducible_comp_surjective_iff _ (leftBorelMap_surjective d hb) _).mpr
  exact actorCore_irreducible d.naturalQuotient _ le_rfl
    (borel d.naturalQuotient).le_normalizer

theorem rootRepresentation_noncentral (hb : CompatibleBorel d) :
    ∃ l v, rootRepresentation d hb l v ≠ v := by
  obtain ⟨b, v, hv⟩ := actorCore_noncentral d.naturalQuotient
    (borel d.naturalQuotient) le_rfl (borel d.naturalQuotient).le_normalizer
  obtain ⟨l, hl⟩ := leftBorelMap_surjective d hb b
  refine ⟨l, v, ?_⟩
  change actorCore d.naturalQuotient (borel d.naturalQuotient)
    (borel d.naturalQuotient).le_normalizer (leftBorelMap d hb l) v ≠ v
  simpa only [hl] using hv

private theorem marked_star (A : Subgroup G) :
    (star F A).map d.model.toMonoidHom = (A.subgroupOf F.H).map d.qH := by
  rw [CriticalFusion.Source.star, map_map]
  rfl

variable (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)

include structural c e mark in
/-- Both containments retain the original quotient map and the original S. -/
theorem root_image :
    ((SteinbergRecognition.S F L).subgroupOf F.H).map d.qH = root d.naturalQuotient := by
  apply le_antisymm
  · have hQ : ((Q T L).subgroupOf F.H).map d.qH = root d.naturalQuotient := by
      rw [← marked_star, e.images.image_eq, marked_star]
      exact mark
    exact (map_mono (subgroupOf_mono F.H (S_le_Q d structural e.separation))).trans_eq hQ
  · have h := map_mono (f := d.model.toMonoidHom)
      (star_twoCore_le_S d structural c e mark)
    rw [map_pCoreIn_of_injective 2 _ _ d.model.injective, marked_star, marked_star,
      (compatibleBorel_of_upperMarking d structural mark).left_image, borel_twoCore] at h
    exact h

include structural c e in
private theorem span_le_H : SteinbergRecognition.S F L ≤ F.H :=
  (S_le_Q d structural e.separation).trans (Q_le_H F)

/-- qH restricted to the actual span, before additive root coordinates. -/
def rootMap : SteinbergRecognition.S F L →* root d.naturalQuotient :=
  (d.qH.comp (Subgroup.inclusion (span_le_H d structural c e))).codRestrict _
    (fun s => root_image d structural c e mark ▸ Subgroup.mem_map.mpr
      ⟨Subgroup.inclusion (span_le_H d structural c e) s, s.property, rfl⟩)

theorem rootMap_surjective : Function.Surjective (rootMap d structural c e mark) := by
  intro r
  have hmem : r.val ∈ ((SteinbergRecognition.S F L).subgroupOf F.H).map d.qH :=
    (root_image d structural c e mark).symm ▸ r.property
  obtain ⟨s, hs, he⟩ := hmem
  exact ⟨⟨s.val, hs⟩, Subtype.ext he⟩

/-- Actual S/(S∩Q_H) coordinates, without assuming S lies in the actor. -/
def rootCoordinate : SteinbergRecognition.S F L →* Multiplicative SL2FourNatural.F :=
  (rootCoordinates d.naturalQuotient).toMonoidHom.comp (rootMap d structural c e mark)

theorem rootCoordinate_surjective :
    Function.Surjective (rootCoordinate d structural c e mark) :=
  (rootCoordinates d.naturalQuotient).surjective.comp (rootMap_surjective d structural c e mark)

theorem rootCoordinate_kernel (s : SteinbergRecognition.S F L) :
    rootCoordinate d structural c e mark s = 1 ↔ (s : G) ∈ F.H.pCoreIn 2 := by
  change rootCoordinates d.naturalQuotient (rootMap d structural c e mark s) = 1 ↔ _
  rw [map_eq_one_iff _ (rootCoordinates d.naturalQuotient).injective]
  change (⟨d.qH (Subgroup.inclusion (span_le_H d structural c e) s), _⟩ :
    root d.naturalQuotient) = 1 ↔ _
  rw [Subtype.ext_iff]
  change Subgroup.inclusion (span_le_H d structural c e) s ∈ d.qH.ker ↔ _
  rw [d.qH_ker]
  rfl

omit [Finite G] in
/-- The normalization needed to state the original L₁ conjugation action. -/
theorem left_normalizes_span : F.Li L 1 ≤ normalizer (SteinbergRecognition.S F L : Set G) :=
  ((F.Li_le L 1).trans inf_le_left).trans SteinbergRecognition.L_normalizes_S

/-- The root coordinates intertwine actual ambient conjugation, not a chosen action. -/
theorem rootCoordinate_equivariant (hb : CompatibleBorel d)
    (l : F.Li L 1) (s : SteinbergRecognition.S F L) :
    (rootCoordinate d structural c e mark
      ⟨(l : G) * s * (l : G)⁻¹,
        (mem_normalizer_iff.mp (left_normalizes_span (F := F) (L := L) l.property) s).mp
          s.property⟩).toAdd =
      rootRepresentation d hb l (rootCoordinate d structural c e mark s).toAdd := by
  have he := coordinateAction_equivariant (root d.naturalQuotient)
    (rootCoordinates d.naturalQuotient)
    (Subgroup.inclusion ((borel d.naturalQuotient).le_normalizer.trans
      (normalizer_le_root_normalizer d.naturalQuotient)) (leftBorelMap d hb l))
    (rootMap d structural c e mark s)
  change _ = (coordinateAction (root d.naturalQuotient) (rootCoordinates d.naturalQuotient)
    _ ((rootCoordinates d.naturalQuotient) (rootMap d structural c e mark s)).toAdd)
  rw [← he]
  apply congrArg Multiplicative.toAdd
  apply congrArg (rootCoordinates d.naturalQuotient)
  apply Subtype.ext
  rw [normalizerMonoidHom_apply_apply_coe]
  let lH : F.H := Subgroup.inclusion ((F.Li_le L 1).trans inf_le_right) l
  let sH : F.H := Subgroup.inclusion (span_le_H d structural c e) s
  change d.qH (lH * sH * lH⁻¹) = d.qH lH * d.qH sH * (d.qH lH)⁻¹
  simp only [map_mul, map_inv]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
