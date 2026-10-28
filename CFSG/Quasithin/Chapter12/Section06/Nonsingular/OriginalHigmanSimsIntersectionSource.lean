module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsIntersectionCard
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsImageIntersections
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsHyperplanes
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsLargeIntersectionPoint

/-!
# Original conjugate intersections in the remaining HS branch

The literal source fusion corrects a conjugator at a common nonsingular
point. The native HS image intersection bound then forces the two action
images to coincide. Their component preimage is the full original moved
subgroup, so that subgroup lies in the original intersection.

A second nonsingular point in this moved subgroup gives a second moved
hyperplane. The two hyperplanes generate the original V. Thus two distinct
original conjugates meet in order at most eight, without assuming the
nonsingular-centralizer conclusion that this branch is intended to prove.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- At a common nonsingular point, a large original intersection contains
the full original moved subgroup, not merely its central quotient image. -/
theorem SourceHypothesis.original_hs_moved_le_large_conjugate
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hZ : ZV L V = ⊥)
    (v : V) (hv : D.Nonsingular v) (hK : IsQuasisimple (Kv (v : G)))
    (hnot : ¬ Kv (v : G) ≤ M L)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (g : G) (hvg : (v : G) ∈ V.map (MulAut.conj g).toMonoidHom)
    (hlarge : 8 < Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    Vv L V (v : G) ≤ V.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨c,hc⟩ := H.fixed_free_centralizer_conjugator D hTV hTI hZ v.property hvg
  let c' : Gv (v : G) := c
  let a := nonsingularModelAction (v : G) e
  let E := (V.subgroupOf (Gv (v : G))).map a
  have hbig : 4 < Nat.card (E ⊓ E.map (MulAut.conj (a c')).toMonoidHom :
      Subgroup (MulAut Sporadic.LeechRelated.HS.Carrier)) :=
    H.nonsingular_hs_image_intersection_card_gt_four D v hv hK hTV hnot e c'
      (by simpa only [c',hc] using hlarge)
  obtain ⟨p,hp⟩ := H.nonsingular_hs_original_image_common_fixed_point D v hv hK e
  have heE := (H.nonsingular_original_model_action D v hv hK e).1
  have hcard := (H.nonsingular_hs_original_inner_part D v hv hK e).1
  have heq : E = E.map (MulAut.conj (a c')).toMonoidHom := by
    rcases OriginalHigmanSimsImageIntersections.pure_elementary_thirty_two_conjugate_intersection
        E (a c') heE hcard (fun x hx => ⟨p,hp x hx⟩) with he | hb
    · exact he
    · omega
  have hn := H.nonsingular_hs_image_normalizer_preserves_moved D v hv hK e c'
    (mem_normalizer_iff_map_conj_eq.mpr heq.symm)
  have hw := mem_normalizer_iff_map_conj_eq.mp hn
  calc
    Vv L V (v : G) = (Vv L V (v : G)).map (MulAut.conj (c : G)).toMonoidHom := hw.symm
    _ ≤ V.map (MulAut.conj (c : G)).toMonoidHom := map_mono (Vv_le_V H.chosen.normalizes _)
    _ = V.map (MulAut.conj g).toMonoidHom := hc

/-- The original HS contrary branch supplies the uniform intersection bound
on V using the same full ambient group, Sylow, and chosen orthogonal marking. -/
theorem SourceHypothesis.original_hs_conjugate_intersection_bound
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3 := by
  obtain ⟨hZ,hall⟩ := H.original_hs_all_nonsingular_points D hTV hTI v hv he
  intro g hg
  by_contra hlarge
  have hbig : 8 < Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by omega
  obtain ⟨u,hu,huI⟩ := D.exists_nonsingular_of_card_gt_eight hZ _ inf_le_left hbig
  have hmove (w : V) (hw : D.Nonsingular w)
      (hwg : (w : G) ∈ V.map (MulAut.conj g).toMonoidHom) :
      Vv L V (w : G) ≤ V.map (MulAut.conj g).toMonoidHom := by
    obtain ⟨hK,hnot,⟨e⟩⟩ := hall w hw
    exact H.original_hs_moved_le_large_conjugate D hTV hTI hZ w hw hK hnot e g hwg hbig
  have huW := hmove u hu huI.2
  obtain ⟨w,hw,hwu,hwm⟩ := D.exists_other_nonsingular_in_moved H.chosen u hu
  have hwW := hmove w hw (huW hwm)
  have hVW : V ≤ V.map (MulAut.conj g).toMonoidHom := by
    exact (D.nonsingular_moved_sup H.chosen hZ u w hu hw hwu.symm).ge.trans (sup_le huW hwW)
  apply hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (eq_of_le_of_card_ge hVW (by rw [card_map_of_injective (MulAut.conj g).injective])).symm

end CFSG.Quasithin.Chapter12.Section06
