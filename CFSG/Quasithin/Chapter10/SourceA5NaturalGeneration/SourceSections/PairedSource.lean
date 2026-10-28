module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalPairedAxes
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.OriginalLinearLocalClass
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairSourceOrbitSpan

/-!
# Original E.2.3 inputs from the same paired natural source

The canonical first component generates the original local join with its
prescribed Sylow subgroup. Component correspondence and source factor
permutation therefore locate the original L on one of the same two marked
axes. C.1.17 applies to the original component and its actual local ambient.
The exact E.2.3 orbit identity also places the original Sylow center in the
local moved layer plus the retained central alpha summand.

The actual B.5.6 paired natural marker and Thompson movement remain explicit
source inputs; no fixed-center or block conclusion is assumed.
Source: Aschbacher–Smith E.2.3 and 10.2.3(4), pp.216–217 and746.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction ChapterB ChapterB.SourceInduction
open ChapterB.QuasisimpleSource ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false in
theorem source_original_component_localClass_of_paired_linear
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let X := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
    let U := D.moduleSubgroup.subgroupOf X
    letI := (source_parabolic_module_reduced D).normal
    letI := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    letI := offenderSubgroup_normal α
    ∀ (_hJ : ¬ elementaryAbelianMaxJ (S : Subgroup X) ≤ centralizer (U : Set X))
      (d : SourceTwoFactorCase (α.comp Y.subtype)) (F : BinaryField)
      (_c : d.MarkedProduct (linearNatural F 2))
      (_hexchange : ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.first),
      let A := L.subgroupOf X
      let B := baumann (S : Subgroup X)
      U ≤ normalizer (A : Set X) ∧ B ≤ normalizer (A : Set X) ∧
        ChapterC.GlaubermanNiles.InLocalClass (inclusion (show B ≤ A ⊔ B from le_sup_right)) ∧
        (ChapterC.GlaubermanNiles.localV (inclusion (show B ≤ A ⊔ B from le_sup_right))).map
          (A ⊔ B).subtype = ⁅U,A⁆ ⊔ (thompsonAlpha (S : Subgroup X) ⊓ centralizer (A : Set X)) := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  dsimp only
  intro hJ d F c hexchange
  have h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple :=
    ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun Z _ _ => ChapterA.Section02.theoremA_knownSimple (G := Z))
    (fun Z _ _ => ChapterA.Section02.theoremC_knownSimple (G := Z))
    D.simpleQTKE T D.maximal
  have hG := (D.local_internal_module hu).sqtk
  have hP := source_a5_minimal_parabolic D e hn
  obtain ⟨K,hK,hi,hcan,_,_,_,_⟩ := first_component_localClass h36 hG S hP U hU hJ q hq hk
    (source_join_not_solvable D) (source_join_fitting D) d F c hexchange
  have hJY : (elementaryAbelianMaxJ (S : Subgroup X)).map q ≤ Y :=
    RankOneBaumann.thompson_image_le_offender_layer S U q hq hk
      (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)) Y le_rfl
  let := d.product.first_normal
  have hYA : Y ≤ normalizer (d.first.map Y.subtype : Set (X ⧸ C)) := by
    have hh := d.first.le_normalizer_map Y.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hgen := selected_component_sup_sylow S hP U hU hJ q hq hk Y _ hJY hYA K hK hcan
  obtain ⟨s,hs⟩ := source_original_component_conjugate_of_generating_component D K hK hgen
  have hcY : pCore 2 Y = ⊥ := by
    have hle : (pCore 2 Y).map Y.subtype ≤ pCore 2 (X ⧸ C) :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map Y.subtype⟩
    rw [hU.quotient_pCore_eq_bot] at hle
    apply bot_unique
    intro y hy
    exact Subtype.ext (hle (mem_map_of_mem Y.subtype hy))
  have hm : (L.subgroupOf X).map q =
      (d.first.map (MulAut.conjNormal (q (s:X))).toMonoidHom).map Y.subtype := by
    rw [hs,map_map]
    have hcomp : q.comp (MulAut.conj (s:X)).toMonoidHom =
        (MulAut.conj (q (s:X))).toMonoidHom.comp q := by
      ext x
      change q ((s:X)*x*(s:X)⁻¹) = q (s:X)*q x*(q (s:X))⁻¹
      rw [map_mul,map_mul,map_inv]
    rw [hcomp,←map_map,hi,map_map,map_map]
    rfl
  have himage : (L.subgroupOf X).map q = d.first.map Y.subtype ∨
      (L.subgroupOf X).map q = d.second.map Y.subtype := by
    rcases d.automorphism_permutation hcY (MulAut.conjNormal (q (s:X))) with h | h
    · exact Or.inl (hm.trans (congrArg (map Y.subtype) h.1))
    · exact Or.inr (hm.trans (congrArg (map Y.subtype) h.1))
  have hA : (L.subgroupOf X).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  exact component_localClass_of_linear_axis h36 hG S hP U hU hJ q hq hk
    (source_join_not_solvable D) (source_join_fitting D) d F c hexchange _ hA himage
set_option backward.isDefEq.respectTransparency false in
theorem source_original_seed_le_moved_sup_central_alpha_of_paired_linear
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let X := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
    let U := D.moduleSubgroup.subgroupOf X
    letI := (source_parabolic_module_reduced D).normal
    letI := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    letI := offenderSubgroup_normal α
    ∀ (_hJ : ¬ elementaryAbelianMaxJ (S : Subgroup X) ≤ centralizer (U : Set X))
      (d : SourceTwoFactorCase (α.comp Y.subtype)) (F : BinaryField)
      (_c : d.MarkedProduct (linearNatural F 2))
      (_hexchange : ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.first),
      omegaOneCenterAmbient (T : Subgroup G) ≤
        ⁅D.moduleSubgroup,localOrbit T L⁆ ⊔
          (thompsonAlpha (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)) := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let := offenderSubgroup_normal α
  dsimp only
  intro hJ d F c hexchange
  have hspan := paired_orbit_span_of_source_model S (source_a5_minimal_parabolic D e hn)
    U hU hJ q hq hk d F c hexchange
  have hplace : omegaOneCenterAmbient (S : Subgroup X) ≤
      ⁅U,pResidual 2 X⁆ ⊔ (thompsonAlpha (S : Subgroup X) ⊓ centralizer (pResidual 2 X : Set X)) :=
    (omegaCenter_le_omegaCenter_maxJ (S : Subgroup X)).trans
      ((le_conjugateSpanBy _ _).trans_eq hspan)
  have hS : (S : Subgroup X).map X.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hZ : (omegaOneCenterAmbient (S : Subgroup X)).map X.subtype =
      omegaOneCenterAmbient (T : Subgroup G) := by
    rw [←omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,hS]
  have hα : (thompsonAlpha (S : Subgroup X)).map X.subtype = thompsonAlpha (T : Subgroup G) := by
    unfold thompsonAlpha
    rw [←omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hS]
  have hm := map_mono (f := X.subtype) hplace
  rw [hZ,Subgroup.map_sup,map_commutator,
    map_subgroupOf_eq_of_le (D.module_le_core.trans (pCoreIn_le 2 X)),source_join_residual D] at hm
  apply hm.trans
  apply sup_le le_sup_left
  apply le_trans ?_ le_sup_right
  rintro z ⟨w,hw,rfl⟩
  refine ⟨hα ▸ mem_map_of_mem X.subtype hw.1,?_⟩
  intro l hl
  obtain ⟨a,ha,rfl⟩ := (source_join_residual D).symm ▸ hl
  exact congrArg X.subtype (hw.2 a ha)

end CFSG.Quasithin.Chapter10
