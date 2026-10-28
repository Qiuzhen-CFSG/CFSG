module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.PairedSource
public import CFSG.Quasithin.Chapter10.SourceA5ActionKernel
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.BlockRecovery.FullCore
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.SourceGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.LinearOffenders
/-!
# The original Baumann subgroup inside the component product

The genuine paired natural source identifies the Baumann image with the
Sylow intersection in its perfect product layer. The actual action kernel
is O₂(L₀T), and full-core movement places that kernel in L₀. Consequently
Baum(T) itself lies in L₀. The same marked source supplies its full Sylow
property, retaining the original quotient and all subgroup inclusions.
Source: Aschbacher--Smith 10.2.3(4), printed pp.746--747; B.6.10 and E.2.3.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction ChapterB ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false in
theorem source_original_baumann_le_orbit_of_paired_linear
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (localJoin T L).pCoreIn 2 ≤ localOrbit T L) :
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
      (_hF : 3 < Nat.card F.Carrier) (_c : d.MarkedProduct (linearNatural F 2))
      (_hexchange : ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.first),
      baumann (T : Subgroup G) ≤ localOrbit T L := by
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
  intro hJ d F hF c hexchange
  obtain ⟨ρ,hfaith,hnat,he,⟨hJq,hBq⟩,hfixed⟩ :=
    RankOneBaumann.PairedFactorOrbit.source_images_and_fixedSpace S (source_a5_minimal_parabolic D e hn)
      U hU hJ q hq hk d F c hexchange
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hF
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F.Carrier ×
      Matrix.SpecialLinearGroup (Fin 2) F.Carrier) := ⟨by
    rw [commutator_def,←top_prod_top,commutator_prod_prod]
    simp only [←commutator_def,Group.IsPerfect.commutator_eq_top]⟩
  let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective
    (f := c.action.groupEquiv.symm.toMonoidHom) c.action.groupEquiv.symm.surjective
  let : Group.IsNilpotent ((X ⧸ C) ⧸ pResidual 2 (X ⧸ C)) :=
    (isPGroup_quotient_pResidual 2).isNilpotent
  have hY : Y ≤ (pResidual 2 X).map q := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact le_of_isPerfect_of_solvable_quotient Y _
  have hkr : q.ker ≤ pResidual 2 X := by
    rw [hk]
    change centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)) ≤ _
    rw [source_a5_local_module_kernel_eq_twoCore D e hn]
    apply (map_le_map_iff_of_injective X.subtype_injective).mp
    rw [source_join_residual D]
    exact hcore
  have hB : baumann (S : Subgroup X) ≤ pResidual 2 X := by
    have hh : (baumann (S : Subgroup X)).map q ≤ (pResidual 2 X).map q :=
      hBq.le.trans (inf_le_right.trans hY)
    have hm := (map_le_iff_le_comap).mp hh
    rw [comap_map_eq,sup_eq_left.mpr hkr] at hm
    exact hm
  have hBm := map_mono (f := X.subtype) hB
  have hSm : (S : Subgroup X).map X.subtype=(T : Subgroup G) := map_subgroupOf_eq_of_le le_sup_right
  have hBmEq := baumann_map_injective X.subtype X.subtype_injective (S : Subgroup X)
  change (baumann (S : Subgroup X)).map X.subtype=baumann ((S : Subgroup X).map X.subtype) at hBmEq
  rw [hSm] at hBmEq
  rwa [source_join_residual D,hBmEq] at hBm
set_option backward.isDefEq.respectTransparency false in
theorem source_original_baumann_in_orbit_of_source
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
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
      (_hF : 3 < Nat.card F.Carrier) (_c : d.MarkedProduct (linearNatural F 2))
      (_hexchange : ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.first),
      baumann (T : Subgroup G) ≤ localOrbit T L ∧
        Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
          (localOrbit T L ⊔ baumann (T : Subgroup G)) := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker=C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let := offenderSubgroup_normal α
  dsimp only
  intro hJ d F hF c hexchange
  have hcore' : pCore 2 X ≤ pResidual 2 X := by
    rw [source_original_full_core_moved D e hn hb hz hH hZH]
    exact commutator_le_right _ _
  have hcore : X.pCoreIn 2 ≤ localOrbit T L :=
    (map_mono (f := X.subtype) hcore').trans_eq (source_join_residual D)
  have hB := source_original_baumann_le_orbit_of_paired_linear D e hn hcore hJ d F hF c hexchange
  have hs := (RankOneBaumann.PairedFactorOrbit.source_global_baumann_and_alpha
    S (source_a5_minimal_parabolic D e hn) U hU hJ q hq hk d F c hexchange).1
  have hm := Chapter1.Section02.IndexTwo.isSylowIn_map hs X.subtype
  have hSm : (S : Subgroup X).map X.subtype=(T : Subgroup G) := map_subgroupOf_eq_of_le le_sup_right
  have hBm := baumann_map_injective X.subtype X.subtype_injective (S : Subgroup X)
  change (baumann (S : Subgroup X)).map X.subtype=baumann ((S : Subgroup X).map X.subtype) at hBm
  rw [hSm] at hBm
  rw [Subgroup.map_sup,source_join_residual D,hBm] at hm
  exact ⟨hB,hm⟩
end CFSG.Quasithin.Chapter10
