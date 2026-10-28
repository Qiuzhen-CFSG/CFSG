module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.FourBlockConjugacy
public import Theory.SpecificGroups.SymmetricEight.NineBlockContainment
/-!
# Discharging the four-block contrary-fusion premises

The literal fused action image has a two-core quotient of order nine, so
`NineBlockContainment` places it in an actual S₈ four-block stabilizer. The
existing full-Q lifting theorem then aligns the original residuals.

For the Sylow placement, conjugate the image of the original T_v inside M
into the original T. The same correcting element transports the fused point,
its full centralizer, and the fusion conjugator. Its membership in M returns
the conclusion for the original conjugator. Thus neither permutation
containment nor T_v placement remains an extra premise in the selected
weight-four source application. The original V, fixed space, coordinates,
point and full-kernel lifting maps are retained.

This completes the four-block contrary-fusion step of Aschbacher--Smith
12.6.19, printed p.828 of the 1 March 2004 manuscript. Full fusion, HS/J₄
exclusions, weak closure, splitting and fixed-space elimination remain with
this owner; neither 12.6.2 nor 12.6.23 is asserted here. Earlier invariance/TI
and final earlier-source discharge retain their existing owners.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
open BinaryPermutation.TerminalOrthogonal
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
/-- The actual E₉ quotient supplies the permutation containment needed by the
full-kernel lifting theorem. -/
theorem SourceHypothesis.weight_four_conjugator_mem_of_placement
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (l : L) (w : V) (hw : (w : G) = (l : G) * (v : G) * (l : G)⁻¹)
    (a z : G) (ha : MulAut.conj a (w : G) = z) (hz : Gv z ≤ M L)
    (hS : (Tv T (w : G)).map (MulAut.conj a).toMonoidHom ≤ LT T L) :
    a ∈ M L ∧ z ∉ centralizer (L : Set G) := by
  let g : LT T L := inclusion le_sup_left l
  have hB := H.weight_four_fused_residual_le_component D E hE v hv g w hw a z ha hz
  obtain ⟨b,_,_,q,_⟩ := H.weight_four_fused_image_quotient D E hE v hv l w hw a hB
  let I := (((Lv L (w : G)).map (MulAut.conj a).toMonoidHom).subgroupOf L).map
    ((alternatingGroup (Fin 8)).subtype.comp D.actorMap)
  have hI : I ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨x,_,rfl⟩
    exact (D.actorMap x).property
  have hc : Nat.card (I ⧸ pCore 2 I) = 9 :=
    (Nat.card_congr q.toEquiv).trans FourBlockResidual.E9_card
  have hi := Theory.SpecificGroups.SymmetricEight.NineBlockContainment.exists_conjugate_le_fourStabilizer
    I hI hc
  exact H.weight_four_conjugator_mem_of_image D hTV E hE v hv l w hw a z ha hz hS hi

private theorem sylow_place_in_overgroup (T : Sylow 2 G) (M P : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hP : IsPGroup 2 P) (hPM : P ≤ M) :
    ∃ c : M, P.map (MulAut.conj (c : G)).toMonoidHom ≤ (T : Subgroup G) := by
  obtain ⟨S,hS⟩ := hP.comap_subtype.exists_le_sylow (P := P.subgroupOf M)
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq M S (T.subtype hTM)
  have hle : (P.subgroupOf M).map (MulAut.conj c).toMonoidHom ≤
      ((T.subtype hTM : Sylow 2 M) : Subgroup M) := by
    rw [←hc]
    exact map_mono hS
  have hh := map_mono (f := M.subtype) hle
  have he : M.subtype.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj (c : G)).toMonoidHom.comp M.subtype := by ext; rfl
  rw [map_map,he,←map_map,map_subgroupOf_eq_of_le hPM] at hh
  exact ⟨c,hh.trans_eq (map_subgroupOf_eq_of_le hTM)⟩

/-- The Sylow correction is made inside M and explicitly transports both
the fused point and its T-centralizer. No placement premise remains. -/
theorem SourceHypothesis.weight_four_conjugator_mem
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (l : L) (w : V) (hw : (w : G) = (l : G) * (v : G) * (l : G)⁻¹)
    (a z : G) (ha : MulAut.conj a (w : G) = z) (hz : Gv z ≤ M L) :
    a ∈ M L ∧ z ∉ centralizer (L : Set G) := by
  let P := (Tv T (w : G)).map (MulAut.conj a).toMonoidHom
  have hp : IsPGroup 2 P := (T.isPGroup'.to_le (show Tv T (w : G) ≤ T from inf_le_left)).map _
  have hPz : P ≤ Gv z := by
    have hh := map_mono (f := (MulAut.conj a).toMonoidHom)
      (show Tv T (w : G) ≤ Gv (w : G) from inf_le_right)
    rw [Gv,map_pointCentralizer] at hh
    exact hh.trans_eq (congrArg Gv ha)
  obtain ⟨c,hc⟩ := sylow_place_in_overgroup T (M L) P
    H.chosen.sylow_normalizes_component hp (hPz.trans hz)
  let d : G := (c : G)*a
  let z' : G := MulAut.conj (c : G) z
  have hd : MulAut.conj d (w : G) = z' := by
    dsimp [d,z']
    rw [←ha]
    simp only [MulAut.conj_apply,mul_inv_rev,mul_assoc]
  have hMM : (M L).map (MulAut.conj (c : G)).toMonoidHom = M L :=
    mem_normalizer_iff_map_conj_eq.mp ((M L).le_normalizer c.property)
  have hz' : Gv z' ≤ M L := by
    have hh := map_mono (f := (MulAut.conj (c : G)).toMonoidHom) hz
    rwa [Gv,map_pointCentralizer,hMM] at hh
  have hS : (Tv T (w : G)).map (MulAut.conj d).toMonoidHom ≤ LT T L := by
    have he : (MulAut.conj d).toMonoidHom =
        (MulAut.conj (c : G)).toMonoidHom.comp (MulAut.conj a).toMonoidHom := by
      ext x
      simp [d,MulAut.conj_apply,mul_assoc]
    rw [he,←map_map]
    exact hc.trans le_sup_right
  obtain ⟨hdM,hz'NC⟩ := H.weight_four_conjugator_mem_of_placement D hTV E hE v hv l w hw d z' hd hz' hS
  refine ⟨?_,?_⟩
  · have hh := (M L).mul_mem ((M L).inv_mem c.property) hdM
    simpa only [d,inv_mul_cancel_left] using hh
  · intro hzc
    apply hz'NC
    exact ((normalizer_le_normalizer_centralizer L c.property) z).mp hzc

/-- The original nonzero fixed-space constructor now supplies the contrary
fusion conclusion without image-containment or Sylow-placement assumptions. -/
theorem SourceHypothesis.exists_selected_weight_four_fusion_control
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥) :
    ∃ (E : Additive V ≃ₗ[ZMod 2] core (Fin 8)) (v : V),
      (∀ l u, E (seedRepresentation L V H.chosen.normalizes l u) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u)) ∧
      (∀ u, coreToNatural (Fin 8) (E u) = D.coordinates (Submodule.Quotient.mk u)) ∧
      E (Additive.ofMul v) = FourBlockPoint.point ∧
      ∃ l : L, let w := conjugation L V H.chosen.normalizes l v
        Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
        (Tv T (w : G)).relIndex (T : Subgroup G) = 2 ∧
        ∀ (a z : G), MulAut.conj a (w : G) = z → Gv z ≤ M L →
          a ∈ M L ∧ z ∉ centralizer (L : Set G) := by
  obtain ⟨E,v,hE,hproj,hv,l,hs,hi,_⟩ := H.exists_selected_weight_four_core D hTV hTI hz
  refine ⟨E,v,hE,hproj,hv,l,hs,hi,?_⟩
  intro a z ha hc
  exact H.weight_four_conjugator_mem D hTV E hE v hv l _ rfl a z ha hc

end CFSG.Quasithin.Chapter12.Section06
