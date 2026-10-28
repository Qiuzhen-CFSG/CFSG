module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalPairedAxes

/-!
# The original component on the paired five-letter axes

Canonical component correspondence locates the original component on one
of the same two residual factors. Thompson movement is the actual earlier
source input; no Baumann-normalizer escape is required.
Source: Aschbacher–Smith E.2.3 and 10.2.3(4), pp.216–217 and746.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
open ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false in
theorem source_original_paired_five_axes_of_source
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from
      le_sup_right)) : Subgroup (localJoin T L)) ≤
      centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)))
    (hp : SourcePairedFiveAction D) :
    SourceOriginalPairedAxes D := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple :=
    ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hG := (D.local_internal_module hu).sqtk
  have hP := source_a5_minimal_parabolic D e hn
  obtain ⟨d,t,ht₁,ht₂,⟨c⟩⟩ := hp
  let B := (alternatingGroup (Fin 5)).map
    (SymmetricFive.Paired.leftFactorMap Y c.action.groupEquiv)
  obtain ⟨K,hK,him,heK,hcan,hUK,hBK,hfit,R,hR⟩ :=
    first_five_component_geometry h36 hG S hP U hU hJ q hq hk
      (source_join_not_solvable D) (source_join_fitting D) d c ⟨t,ht₁,ht₂⟩
  have hJA : (elementaryAbelianMaxJ (S : Subgroup H)).map q ≤ Y :=
    ChapterB.RankOneBaumann.thompson_image_le_offender_layer S U q hq hk
      (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)) Y le_rfl
  have hgen := selected_component_sup_sylow S hP U hU hJ q hq hk Y B hJA
    (five_first_axis_normalized Y c.action.groupEquiv) K hK hcan
  obtain ⟨s,hs⟩ := source_original_component_conjugate_of_generating_component D K hK hgen
  have hNK : Y.comap q ≤ normalizer (K : Set H) :=
    selected_component_normalized q B K (Y.comap q) hcan
      ((map_comap_le q Y).trans (five_first_axis_normalized Y c.action.groupEquiv))
  have hnorm : Y.comap q ≤ normalizer (L.subgroupOf H : Set H) := by
    rw [hs]
    have hh := (map_mono (f := (MulAut.conj (s:H)).toMonoidHom) hNK).trans
      (K.le_normalizer_map (MulAut.conj (s:H)).toMonoidHom)
    have heq : (Y.comap q).map (MulAut.conj (s:H)).toMonoidHom = Y.comap q :=
      normal_iff_map_conj_eq.mp (inferInstance : (Y.comap q).Normal) (s:H)
    rwa [heq] at hh
  have hfirst : K.map q = (factorResidual q Y d.first).map q := by
    rw [him,paired_symmetric_first_residual_image α q hq d c]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨(a,1),⟨ha,one_mem _⟩,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      refine ⟨a.1,ha.1,?_⟩
      change ((c.action.groupEquiv.symm (a.1,1) : Y) : H ⧸ C) = _
      exact congrArg (fun a => ((c.action.groupEquiv.symm a : Y) : H ⧸ C))
        (Prod.ext rfl ha.2.symm)
  have hmap : (L.subgroupOf H).map q =
      ((factorResidual q Y d.first).map (MulAut.conj (s:H)).toMonoidHom).map q := by
    rw [hs,map_map,map_map]
    have hcomp : q.comp (MulAut.conj (s:H)).toMonoidHom =
        (MulAut.conj (q (s:H))).toMonoidHom.comp q := by
      ext x
      change q ((s:H) * x * (s:H)⁻¹) = q (s:H) * q x * (q (s:H))⁻¹
      rw [map_mul,map_mul,map_inv]
    rw [hcomp,←map_map,←map_map,hfirst]
  refine ⟨d,c,⟨t,ht₁,ht₂⟩,hnorm,?_⟩
  rcases paired_residual_factors_permuted U hU q hq hk d (s:H) with h | h
  · exact Or.inl (hmap.trans (congrArg (map q) h.1))
  · exact Or.inr (hmap.trans (congrArg (map q) h.1))
end CFSG.Quasithin.Chapter10
