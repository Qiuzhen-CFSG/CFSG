module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.PairedSource
public import CFSG.Quasithin.Chapter10.SourceA5ActionKernel
public import BenderSuzuki.External.Huppert.II.theorem_6_14
/-!
# The selected original paired field has order four

The first component supplied by the same paired source generates the local
join with its Sylow subgroup and is a Sylow conjugate of the original L.
Its actual quotient image therefore has order sixty. The marked product
identifies that image with SL₂ of the selected binary field, whose order
formula forces the field order to be four. No block premise or chosen
identification of different binary fields is used.

Source: Aschbacher--Smith 10.2.3(4), p.746, using E.2.3 and the original
A₅ component quotient.
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
theorem source_original_paired_field_card
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
      Nat.card F.Carrier = 4 := by
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
  have h60 : Nat.card ((L.subgroupOf X).map q) = 60 := by
    obtain ⟨a⟩ := (source_a5_local_action_original_component D e hn).2
    rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hfirst : Nat.card d.first = 60 := by
    rwa [hm,card_map_of_injective Y.subtype_injective,
      card_map_of_injective (f := (MulAut.conjNormal (q (s:X)) : MulAut Y).toMonoidHom)
        (MulAut.conjNormal (q (s:X)) : MulAut Y).injective] at h60
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) = 60 := by
    rw [←c.first_eq,card_map_of_injective c.action.groupEquiv.symm.injective] at hfirst
    rw [Nat.card_congr ((⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F.Carrier)).prodEquiv
      (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F.Carrier))).toEquiv,
      Nat.card_prod,card_top,card_bot,mul_one] at hfirst
    exact hfirst
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup] at hSL
  have hge : 1 < Nat.card F.Carrier := Finite.one_lt_card
  have hsquare : 1 ≤ Nat.card F.Carrier ^ 2 := by nlinarith
  have hsub := Nat.sub_add_cancel hsquare
  have hle : Nat.card F.Carrier ≤ 4 := by
    by_contra! h
    have hmul := congrArg (fun x : ℕ => Nat.card F.Carrier * x) hsub
    simp only [mul_add,mul_one,hSL] at hmul
    nlinarith
  interval_cases h : Nat.card F.Carrier <;> first | rfl | norm_num [h] at hSL

end CFSG.Quasithin.Chapter10
