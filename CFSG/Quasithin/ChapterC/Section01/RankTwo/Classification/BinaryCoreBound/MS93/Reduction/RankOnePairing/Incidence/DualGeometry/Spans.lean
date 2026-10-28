module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry.Basic

/-!
# Literal lifts of the neighboring planes

Surjectivity lifts matrix actors into the specified local normalizers.
The coordinate-span lemmas then give the required ambient subgroup spans
modulo the actual pairing kernel. Natural coordinates on Z transport the
intersections of value spaces without adding any kernel.

This is conditional transport of the finite matrix calculation in
MS93 (1.7)(ii), p.848; its matrix premise remains explicit.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry
open Subgroup FixedGeometry.ValueConstruction
universe u
variable {M : Type u} [Group M] [Finite M]
variable {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M} [Z.Normal] [W.Normal]

omit [Finite M] [Z.Normal] in
private theorem lift_actor (f : LocalFacts e Z) (j : Bool) (a : modelParabolic e.flag j) :
    ∃ m : localParabolic e j, e.projection m = a := by
  obtain ⟨m, hm, he⟩ := (show (a : SL) ∈ (localParabolic e j).map e.projection by
    rw [f.parabolic_image]; exact a.property)
  exact ⟨⟨m, hm⟩, he⟩

private theorem seed_conjugate_image (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural)
    (g : MatrixGeometry d.natural.marking e.flag i) (a : M) :
    imageIn (generated X) n.coordinates (conjugate a X) =
      (seedLine d.natural.marking e.flag i).map
        (vectorAction (dualMark d.natural.marking (e.projection a))).toMonoidHom := by
  rw [dual_image_conjugate d f n X le_normalClosure, seed_image_eq d f n g]
  rfl

private theorem plane_conjugate_image (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural)
    (g : MatrixGeometry d.natural.marking e.flag i) (a : M) :
    imageIn (generated X) n.coordinates
      (conjugate a (localGenerated (localParabolic e (!i)) X)) =
      (neighboringPlane d.natural.marking e.flag i).map
        (vectorAction (dualMark d.natural.marking (e.projection a))).toMonoidHom := by
  rw [dual_image_conjugate d f n _ (localGenerated_le_generated _ X),
    neighboring_image_eq d f n g]
  rfl

private theorem value_conjugate_image (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (j : Bool) (a : M) :
    coordinateImage d.natural (conjugate a (localFixed e Z j)) =
      (modelValues d.natural.marking e.flag j).map
        (vectorAction (d.natural.marking (e.projection a))).toMonoidHom := by
  rw [coordinateImage_conjugate d.natural f.component_image (localFixed e Z j) inf_le_left a,
    coordinateImage_localFixed d.natural f.component_image f]

/-- The star of neighboring closures covers U modulo its pairing kernel. -/
theorem star_cover_of_matrixGeometry (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural)
    (g : MatrixGeometry d.natural.marking e.flag i) :
    generated X ≤ (⨆ p : localParabolic e i,
      conjugate (p : M) (localGenerated (localParabolic e (!i)) X)) ⊔ pairingKernel X W := by
  apply lift_imageIn_le _ _ _ _ n.coordinates n.kernel le_rfl
  rw [imageIn_iSup (generated X) n.coordinates
    (fun p : localParabolic e i => conjugate (p : M) (localGenerated (localParabolic e (!i)) X))
    (fun p => conjugate_le_carrier _ _ (localGenerated_le_generated _ X) (p : M))]
  apply le_trans le_top
  rw [← g.star_cover]
  apply iSup_le
  intro a
  obtain ⟨p, hp⟩ := lift_actor f i a
  apply le_iSup_of_le p
  rw [plane_conjugate_image d f n g, hp]

/-- Each plane in the star is spanned in two ways by the seed and an actual neighbor. -/
theorem star_neighbors_of_matrixGeometry (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural)
    (g : MatrixGeometry d.natural.marking e.flag i) (p : localParabolic e i) :
    ∃ r s : localParabolic e (!i),
      conjugate (p : M) (localGenerated (localParabolic e (!i)) X) ≤
        (X ⊔ conjugate ((p : M) * r) X) ⊔ pairingKernel X W ∧
      conjugate (p : M) (localGenerated (localParabolic e (!i)) X) ≤
        (X ⊔ conjugate ((p : M) * s) X) ⊔ pairingKernel X W ∧
      conjugate ((p : M) * r) (localFixed e Z i) ⊓
        conjugate ((p : M) * s) (localFixed e Z i) ≤
          conjugate (p : M) (localFixed e Z (!i)) ∧
      conjugate (p : M) (localFixed e Z (!i)) ≤ localFixed e Z i := by
  have hp : e.projection p ∈ modelParabolic e.flag i := by
    rw [← f.parabolic_image i]
    exact mem_map_of_mem _ p.property
  obtain ⟨r, s, hr, hs, hinter, hinc⟩ := g.star_neighbors ⟨e.projection p, hp⟩
  obtain ⟨r', hr'⟩ := lift_actor f (!i) r
  obtain ⟨s', hs'⟩ := lift_actor f (!i) s
  refine ⟨r', s', ?_, ?_, ?_, ?_⟩
  · apply dual_lift_span d n _ _ _
      (conjugate_le_carrier _ _ (localGenerated_le_generated _ X) p)
      le_normalClosure (conjugate_le_carrier _ _ le_normalClosure _)
    rw [plane_conjugate_image d f n g, seed_image_eq d f n g,
      seed_conjugate_image d f n g, map_mul, hr']
    exact hr
  · apply dual_lift_span d n _ _ _
      (conjugate_le_carrier _ _ (localGenerated_le_generated _ X) p)
      le_normalClosure (conjugate_le_carrier _ _ le_normalClosure _)
    rw [plane_conjugate_image d f n g, seed_image_eq d f n g,
      seed_conjugate_image d f n g, map_mul, hs']
    exact hs
  · apply (coordinateImage_le_iff d.natural
      (inf_le_left.trans (conjugate_le_carrier Z _ inf_le_left _))).mp
    change coordinateImage d.natural
      (conjugate ((p : M) * r') (localFixed e Z i) ⊓
        conjugate ((p : M) * s') (localFixed e Z i)) ≤
      coordinateImage d.natural (conjugate (p : M) (localFixed e Z (!i)))
    rw [coordinateImage_inf, value_conjugate_image d f i ((p : M) * r'),
      value_conjugate_image d f i ((p : M) * s'),
      value_conjugate_image d f (!i) (p : M)]
    simpa only [map_mul, hr', hs'] using hinter
  · apply (coordinateImage_le_iff d.natural
      (conjugate_le_carrier Z _ inf_le_left (p : M))).mp
    change coordinateImage d.natural (conjugate (p : M) (localFixed e Z (!i))) ≤
      coordinateImage d.natural (localFixed e Z i)
    rw [value_conjugate_image d f (!i) (p : M), coordinateImage_localFixed d.natural f.component_image f]
    exact hinc

/-- Two opposite planes give the covers and disjoint value lines with literal seed inclusions. -/
theorem opposite_cover_of_matrixGeometry (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural)
    (g : MatrixGeometry d.natural.marking e.flag i) :
    ∃ a b : M,
      conjugate a X ≤ localGenerated (localParabolic e (!i)) X ∧
      conjugate b X ≤ localGenerated (localParabolic e (!i)) X ∧
      generated X ≤ (localGenerated (localParabolic e (!i)) X ⊔
        conjugate a (localGenerated (localParabolic e (!i)) X)) ⊔ pairingKernel X W ∧
      generated X ≤ (localGenerated (localParabolic e (!i)) X ⊔
        conjugate b (localGenerated (localParabolic e (!i)) X)) ⊔ pairingKernel X W ∧
      conjugate a (localFixed e Z (!i)) ⊓ conjugate b (localFixed e Z (!i)) = ⊥ := by
  obtain ⟨r, s, a, b, ha, hb, hab⟩ := g.opposite_cover
  obtain ⟨r', hr⟩ := lift_actor f (!i) r
  obtain ⟨s', hs⟩ := lift_actor f (!i) s
  obtain ⟨a', hea⟩ := lift_actor f i a
  obtain ⟨b', heb⟩ := lift_actor f i b
  refine ⟨(r' : M) * a', (s' : M) * b', opposite_seed_le d f r' a',
    opposite_seed_le d f s' b', ?_, ?_, ?_⟩
  · apply dual_lift_span d n _ _ _ le_rfl (localGenerated_le_generated _ X)
      (conjugate_le_carrier _ _ (localGenerated_le_generated _ X) _)
    rw [neighboring_image_eq d f n g, plane_conjugate_image d f n g, map_mul, hr, hea, ha]
    exact le_top
  · apply dual_lift_span d n _ _ _ le_rfl (localGenerated_le_generated _ X)
      (conjugate_le_carrier _ _ (localGenerated_le_generated _ X) _)
    rw [neighboring_image_eq d f n g, plane_conjugate_image d f n g, map_mul, hs, heb, hb]
    exact le_top
  · apply (coordinateImage_eq_bot_iff d.natural
      (inf_le_left.trans (conjugate_le_carrier Z _ inf_le_left _))).mp
    change coordinateImage d.natural
      (conjugate ((r' : M) * a') (localFixed e Z (!i)) ⊓
        conjugate ((s' : M) * b') (localFixed e Z (!i))) = ⊥
    rw [coordinateImage_inf, value_conjugate_image d f (!i) ((r' : M) * a'),
      value_conjugate_image d f (!i) ((s' : M) * b')]
    simpa only [map_mul, hr, hs, hea, heb] using hab

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry
