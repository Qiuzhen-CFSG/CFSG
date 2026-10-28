module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.PairedSource
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.CommonBaumann

/-!
# The original natural component in the common Baumann local class

The canonical linear factor is conjugate to the original component under T.
Permutation of the two marked factors identifies the original component's
image, so the intrinsic local-class theorem applies to that same component.
Transport then uses the literal inclusion of the ambient Baumann subgroup.
The final theorem discharges the parabolic and paired-source inputs from the
original moving context and its even-field quotient.

Source: Aschbacher–Smith C.1.17, C.1.26 and 10.2.3(4), pp.132,746.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterE.ThompsonAction ChapterB ChapterB.SourceInduction
open ChapterB.QuasisimpleSource ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false in
theorem source_original_component_localClass_of_natural_source
    (hP : IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)) ⊤) :
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
/-- The actual original paired source uses the same ambient Baumann group
as the other local-class applications, with its inclusion retained. -/
theorem source_original_common_baumann_embedding_of_natural_source
    (hP : IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)) ⊤) :
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
      let N := L.subgroupOf X ⊔ baumann (S : Subgroup X)
      ∃ f : baumann (T : Subgroup G) →* N,
        ChapterC.GlaubermanNiles.InLocalClass f ∧
        (X.subtype.comp N.subtype).comp f = (baumann (T : Subgroup G)).subtype := by
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
  have hc := source_original_component_localClass_of_natural_source D hP hJ d F c hexchange
  exact ChapterC.GlaubermanNiles.original_baumann_embedding
    (T : Subgroup G) X le_sup_right (L.subgroupOf X ⊔ baumann (S : Subgroup X))
    le_sup_right hc.2.2.1

/-- The original context constructs its component local class and the literal
ambient Baumann embedding, without an additional marked-source premise. -/
theorem Context.original_common_baumann_embedding
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    let X := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
    let A := L.subgroupOf X
    let U := D.moduleSubgroup.subgroupOf X
    let B := baumann (S : Subgroup X)
    U ≤ normalizer (A : Set X) ∧ B ≤ normalizer (A : Set X) ∧
      ChapterC.GlaubermanNiles.InLocalClass (inclusion (show B ≤ A ⊔ B from le_sup_right)) ∧
      (ChapterC.GlaubermanNiles.localV (inclusion (show B ≤ A ⊔ B from le_sup_right))).map
        (A ⊔ B).subtype = ⁅U,A⁆ ⊔ (thompsonAlpha (S : Subgroup X) ⊓ centralizer (A : Set X)) ∧
      ∃ f : baumann (T : Subgroup G) →* (A ⊔ B : Subgroup X),
        ChapterC.GlaubermanNiles.InLocalClass f ∧
        (X.subtype.comp (A ⊔ B).subtype).comp f = (baumann (T : Subgroup G)).subtype := by
  have hP := source_natural_minimal_parabolic D e n hn hF ctx.nonnormal
  have hJ := source_hstar_local_thompson_moves_of_omega_commutator D ctx.hstar ctx.moving
  obtain ⟨d,E,⟨c⟩,hexchange⟩ := ctx.original_paired_linear D n hn hF e
  obtain ⟨hU,hB,hlocal,hv⟩ := source_original_component_localClass_of_natural_source D hP hJ d E c hexchange
  exact ⟨hU,hB,hlocal,hv,
    source_original_common_baumann_embedding_of_natural_source D hP hJ d E c hexchange⟩

end CFSG.Quasithin.Chapter10.MovingHall
