module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.Natural
public import Theory.SpecificGroups.SymplecticFour.RootDisplacement

/-!
# A critical root in the selected original natural marking

The reciprocal field-sized critical indices make the displacement of the
opposite center a line in the same ambient natural cover. Its exact component
marking therefore identifies its full image with a long-root subgroup after
one inner conjugation. That conjugator is retained when passing to the full
fixed-core quotient and when choosing the whole-core natural coordinates.

Source: MS93 (3.7), pp.876–877, using (3.3), p.867.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
open DistanceTwoRecognition ChapterB.QuasisimpleSource MSCentralOrbit
open Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)

set_option maxHeartbeats 400000 in
/-- Select the long-root orientation in the actual ambient natural marking. -/
theorem exists_critical_root_marking (hinner : K ⊔ pCore 2 H = ⊤)
    {g : Geometry R} {a z : Vertex R} (path : CriticalPath R g a z)
    (hb : 0 < g.b R) (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    (cv : AmbientVertexCover R (originalMovedSection h) n a) :
    ∃ u : Sp cv.field.Carrier,
      ((Z R z).subgroupOf (stabilizer R a)).map
        ((MulAut.conj u).toMonoidHom.comp (coverQuotient h hinner cv)) =
          RootSubgroup.group 0 := by
  let : (K.map (QuotientGroup.mk' (pCore 2 H))).Normal := h.component_image_structure.2.1
  let s := originalMovedSection h
  have hFc : Nat.card cv.field.Carrier = 2^n := by rw [cv.field.card_eq,cv.degree]
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; exact hb)
        z path.end_color path.critical }
  obtain ⟨haq,hzq⟩ := h.original_small_critical_indices_eq_field path hb (by
    rw [hcritical,h.field_card]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)
  rw [h.field_card] at haq hzq
  have hZS : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := cv.quotient.comp (inclusion hZS)
  have hδcard : Nat.card δ.range = Nat.card cv.field.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZS cv.quotient cv.kernel_Q).trans
      (hzq.trans hFc.symm)
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev hb
    (MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer z path.end_color)
    h.nonbinary hFc s cv.equiv cv.cover h.component_image_structure.2.2.2.2
    cv.embedding cv.injective cv.range_eq δ
    (fun x v => cv.conjugation (inclusion hZS x) v) hδcard (haq.trans hFc.symm)
  have hmark (x : Z R z) :
      coverQuotient h hinner cv (inclusion hZS x) = (β x).val := by
    rw [coverQuotient_apply]
    rw [show (⟨cv.quotient (inclusion hZS x),_⟩ : K.map (QuotientGroup.mk' (pCore 2 H))) =
      cv.equiv.groupEquiv.symm (β x) from Subtype.ext (hβmark x).symm,
      cv.equiv.groupEquiv.apply_symm_apply]
  have himage : ((Z R z).subgroupOf (stabilizer R a)).map (coverQuotient h hinner cv) =
      β.range.map (commutator (Sp cv.field.Carrier)).subtype := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      refine ⟨β ⟨x.val,hx⟩,⟨_,rfl⟩,?_⟩
      exact (hmark ⟨x.val,hx⟩).symm
    · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
      exact ⟨inclusion hZS x,x.property,hmark x⟩
  have hcard : Nat.card (β.range.map (commutator (Sp cv.field.Carrier)).subtype) =
      Nat.card cv.field.Carrier := by
    rw [card_map_of_injective (commutator (Sp cv.field.Carrier)).subtype_injective,hβcard]
  obtain ⟨u,hu⟩ := FourLongRoots.exists_conjugate_root_of_displacement_one _ hcard hβdim hβquad
  refine ⟨u,?_⟩
  rw [←Subgroup.map_map,himage]
  exact hu

/-- The selected root is unchanged upon passage through the entire fixed
attachment. The resulting conjugator can also twist the natural coordinates. -/
theorem exists_critical_root_image (hinner : K ⊔ pCore 2 H = ⊤)
    {g : Geometry R} {a z : Vertex R} (path : CriticalPath R g a z)
    (hb : 0 < g.b R) (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    (cv : AmbientVertexCover R (originalMovedSection h) n a) :
    ∃ u : Sp cv.field.Carrier,
      (layerImage R a (Z R z)).map
        (markedQuotient R (coverQuotient h hinner cv) (coverQuotient_kernel h hinner cv) u) =
          RootSubgroup.group 0 := by
  obtain ⟨u,hu⟩ := exists_critical_root_marking h hinner path hb hcritical cv
  refine ⟨u,?_⟩
  change (((Z R z).subgroupOf (stabilizer R a)).map (fixedProjection R a)).map _ = _
  rw [Subgroup.map_map]
  have he : (markedQuotient R (coverQuotient h hinner cv)
      (coverQuotient_kernel h hinner cv) u).comp (fixedProjection R a) =
      (MulAut.conj u).toMonoidHom.comp (coverQuotient h hinner cv) := by
    apply MonoidHom.ext
    intro x
    exact markedQuotient_projection R _ _ u x
  rw [he]
  exact hu

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
