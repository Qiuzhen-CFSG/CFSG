module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryLeftCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFour
public import Theory.SpecificGroups.PSL3.RootPlaneGeometry
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
/-!
# The second-parabolic contradiction in the unitary row

Write R = O₂(J) and U = O₂(L) for the original proper overcomponent.
The natural or dual action gives |R| = q³, |U| = q⁴, and C_R(u) = R ∩ U
for every u in U outside R. Consequently every involution of RU lies in
R or U. Every elementary subgroup of RU of order |U| is therefore U,
so N_J(RU) normalizes U. This lifts the entire quotient normalizer of the
literal image of U to N_J(U), without assuming the extension splits.

That image is a full elementary q² subgroup of SL₃(q). Sylow conjugacy
and the two root planes identify its normalizer with an actual parabolic,
whose SL₂(q) section is nonsolvable. The previously proved solvability of
N_J(U) now gives the contradiction. Thus the original right factor is
maximal and its normalizer pair satisfies the source 5.3 local conditions,
in both unitary orientations and in the degree-two extension.

Source: Aschbacher–Smith 5.2.8, printed pp.652–653 (`refs/quasithin.pdf`).
Original uniqueness remains in Preparation. Exhaustive amalgam comparison
and ambient completion recognition are separate remaining obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryLeftCore
variable {G : Type*} [Group G] [Finite G]

/-- The original left core is preserved by every normalizer of its product
with the natural core; no splitting of the extension is required. -/
theorem normalizer_product_le {h : HasCharacteristicTwo G} {m : ℕ}
    (d : UnitaryCover.NaturalCoreAction h m)
    (hphi : frattini (pCore 2 G) = ⊥) (hm : 0 < m)
    [IsElementaryAbelian 2 (pCore 2 G)]
    (hR : Nat.card (pCore 2 G) = (2^m)^3)
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hU : Nat.card U = (2^m)^4) :
    normalizer ((pCore 2 G ⊔ U : Subgroup G) : Set G) ≤ normalizer (U : Set G) := by
  let R := pCore 2 G
  obtain ⟨hI,hC,_⟩ := left_core_geometry d hphi hm hR U hU
  have hfix (u : G) (hu : u ∈ U) (hur : u ∉ R) :
      R ⊓ centralizer ({u} : Set G) = R ⊓ U := by
    apply (eq_of_le_of_card_ge ?_ ?_).symm
    · exact inf_le_inf_left R (fun x hx _ hy => by
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact U.le_centralizer hx _ hu)
    · rw [hI]
      exact fixed_core_card_le d hphi u hur
  have hexp (x : G) (hx : x ∈ R ⊔ U) (hxx : x^2 = 1) : x ∈ R ∨ x ∈ U := by
    obtain ⟨r,hr,u,hu,rfl⟩ := mem_sup_of_normal_left.mp hx
    by_cases hur : u ∈ R
    · exact .inl (R.mul_mem hr hur)
    · have hrr : r*r = 1 := by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) r hr
      have huu : u*u = 1 := by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu
      have hru : r*u = u*r := by
        have hi := inv_eq_of_mul_eq_one_right (show (r*u)*(r*u)=1 by simpa only [pow_two] using hxx)
        simpa only [mul_inv_rev,inv_eq_of_mul_eq_one_right hrr,
          inv_eq_of_mul_eq_one_right huu] using hi.symm
      have hrC : r ∈ R ⊓ centralizer ({u} : Set G) :=
        ⟨hr,fun _ hv => by rcases Set.mem_singleton_iff.mp hv with rfl; exact hru.symm⟩
      exact .inr (U.mul_mem ((hfix u hu hur).le hrC).2 hu)
  have hunique (E : Subgroup G) [IsElementaryAbelian 2 E]
      (hE : E ≤ R ⊔ U) (hc : Nat.card E = Nat.card U) : E = U := by
    have hEU : E ≤ R ∨ E ≤ U := SubgroupClass.subset_union.mp
      (fun x hx => hexp x (hE hx) (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx))
    rcases hEU with hER | hEU
    · have hh := card_le_of_le hER
      rw [hc,hU,hR] at hh
      have hq : 1 < 2^m := by simpa using Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) hm
      exact False.elim ((not_lt_of_ge hh) (Nat.pow_lt_pow_right hq (by decide : 3 < 4)))
    · exact eq_of_le_of_card_ge hEU hc.ge
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  let a := MulAut.conj g
  let : IsElementaryAbelian 2 (U.map a.toMonoidHom) := IsElementaryAbelian.map _
  change U.map a.toMonoidHom = U
  apply hunique
  · exact (map_mono (show U ≤ R ⊔ U from le_sup_right)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp hg)
  · exact card_map_of_injective a.injective

/-- The quotient root-plane normalizer lifts to the literal left-core normalizer. -/
theorem normalizer_image_eq {h : HasCharacteristicTwo G} {m : ℕ}
    (d : UnitaryCover.NaturalCoreAction h m)
    (hphi : frattini (pCore 2 G) = ⊥) (hm : 0 < m)
    [IsElementaryAbelian 2 (pCore 2 G)]
    (hR : Nat.card (pCore 2 G) = (2^m)^3)
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hU : Nat.card U = (2^m)^4) :
    (normalizer (U : Set G)).map (QuotientGroup.mk' (pCore 2 G)) =
      normalizer (U.map (QuotientGroup.mk' (pCore 2 G)) : Set (G ⧸ pCore 2 G)) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hc : (U.map q).comap q = pCore 2 G ⊔ U := by
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_comm]
  have hn : (normalizer (U.map q : Set (G ⧸ pCore 2 G))).comap q ≤ normalizer (U : Set G) := by
    rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),hc]
    exact normalizer_product_le d hphi hm hR U hU
  apply le_antisymm (U.le_normalizer_map q)
  intro x hx
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G) x
  exact mem_map_of_mem q (hn hx)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryLeftCore
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryLeftCore
open Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3Even.UnipotentGeometry
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

private theorem parabolic_not_solvable (hF : 2 < Nat.card F) (b : Bool) :
    ¬ Group.IsSolvable (parabolicSL F b) := by
  intro hs
  let := hs
  have hp : ∃ P : Subgroup SL(3,F), P ≤ parabolicSL F b ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* SL(2,F)) := by
    cases b
    · exact ⟨lineLocalSL F,lineLocalSL_le F,⟨lineLocalSLCoreQuotientEquiv F⟩⟩
    · exact ⟨pointLocalSL F,pointLocalSL_le F,⟨pointLocalSLCoreQuotientEquiv F⟩⟩
  obtain ⟨P,hP,⟨e⟩⟩ := hp
  let : Group.IsSolvable P := Group.isSolvable_of_isSolvable_injective (inclusion_injective hP)
  let : Group.IsSolvable SL(2,F) := Group.isSolvable_of_surjective
    (f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P)))
    (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 P)))
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hF
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hF
  exact Group.IsPerfect.not_isSolvable SL(2,F) inferInstance

/-- A full elementary root plane in SL₃ has nonsolvable normalizer.
The plane is obtained by conjugating the supplied elementary subgroup,
not by supplying an unconnected abstract parabolic. -/
theorem full_elementary_normalizer_not_solvable {m : ℕ} (hm : 1 < m)
    (hF : Nat.card F = 2^m) (A : Subgroup SL(3,F))
    [IsElementaryAbelian 2 A] (hA : Nat.card A = (2^m)^2) :
    ¬ Group.IsSolvable (normalizer (A : Set SL(3,F))) := by
  intro hs
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(3,F) S
    (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F (by omega) hF)
  let a := MulAut.conj g
  let E := A.map a.toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hE : E ≤ unipotentSL F := by
    have hh : (S : Subgroup SL(3,F)).map a.toMonoidHom = unipotentSL F := congrArg Sylow.toSubgroup hg
    exact (map_mono hAS).trans_eq hh
  let D := E.comap (specialLinear F)
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.comap_of_injective _ (specialLinear_injective F) _
  have hDm : D.map (specialLinear F) = E := map_comap_eq_self (by rwa [specialLinear_range])
  have hEc : Nat.card E = (2^m)^2 := (card_map_of_injective a.injective).trans hA
  have hplane : ∃ b : Bool, E = rootPlaneSL F b := by
    have hcard (b : Bool) : Nat.card (rootPlaneSL F b) = (2^m)^2 := by
      cases b <;> simp only [rootPlaneSL,Bool.false_eq_true,↓reduceIte,
        card_map_of_injective (specialLinear_injective F),card_V₁,card_V₂,hF]
    rcases elementary_le_plane F D with hD | hD
    · refine ⟨true,eq_of_le_of_card_ge ?_ ?_⟩
      · exact hDm ▸ map_mono hD
      · rw [hcard,hEc]
    · refine ⟨false,eq_of_le_of_card_ge ?_ ?_⟩
      · exact hDm ▸ map_mono hD
      · rw [hcard,hEc]
  obtain ⟨b,hb⟩ := hplane
  let := hs
  have hn : (normalizer (A : Set SL(3,F))).map a.toMonoidHom =
      parabolicSL F b := by
    rw [map_equiv_normalizer_eq]
    change normalizer (E : Set SL(3,F)) = _
    rw [hb,normalizer_rootPlaneSL]
  have hh : Group.IsSolvable ((normalizer (A : Set SL(3,F))).map a.toMonoidHom) :=
    Group.isSolvable_of_surjective (a.toMonoidHom.subgroupMap_surjective _)
  have hq : 2 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) hm
    simpa only [pow_one] using hh
  exact parabolic_not_solvable F hq b (hn ▸ hh)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryLeftCore
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryLeftCore
variable {G : Type*} [Group G] [Finite G]
/-- N(U) is nonsolvable for the original elementary q⁴ subgroup in the
natural q³ extension of SL₃(q). -/
theorem left_core_normalizer_not_solvable {h : HasCharacteristicTwo G} {m : ℕ}
    (d : UnitaryCover.NaturalCoreAction h m)
    (hphi : frattini (pCore 2 G) = ⊥) (hm : 1 < m)
    [IsElementaryAbelian 2 (pCore 2 G)]
    (hR : Nat.card (pCore 2 G) = (2^m)^3)
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hU : Nat.card U = (2^m)^4) :
    ¬ Group.IsSolvable (normalizer (U : Set G)) := by
  intro hs
  let := hs
  let q := QuotientGroup.mk' (pCore 2 G)
  have hn := normalizer_image_eq d hphi (by omega) hR U hU
  have hsol : Group.IsSolvable (normalizer (U.map q : Set (G ⧸ pCore 2 G))) := by
    rw [←hn]
    exact Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  obtain ⟨_,_,helem,hAc,_⟩ := left_core_geometry d hphi (by omega) hR U hU
  obtain ⟨F,_,_,_,hF,e,_⟩ := d.exists_coordinates
  let A := (U.map q).map e.toMonoidHom
  let := helem
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hA : Nat.card A = (2^m)^2 := (card_map_of_injective e.injective).trans hAc
  apply full_elementary_normalizer_not_solvable F hm hF A hA
  let := hsol
  rw [←map_equiv_normalizer_eq]
  exact Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective _)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryLeftCore
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- The marked left-core normalizer is nonsolvable: its quotient image is
an actual root-plane parabolic, and every normalizer there lifts to U. -/
theorem Preparation.unitary_overcomponent_left_core_normalizer_not_solvable
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    ¬ Group.IsSolvable (J ⊓ normalizer (L.pCoreIn 2 : Set G) : Subgroup G) := by
  have hUJ := (d.unitary_overcomponent_left_core_normalizer h hH hp m hm he hJ hKJ hQR).1
  obtain ⟨_,hRc,hc,hact⟩ :=
    d.unitary_overcomponent_whole_natural_core h hH hp m hm he hJ hKJ hQR
  obtain ⟨hRe,hphi⟩ :=
    d.unitary_overcomponent_elementary_core h hH hp m hm he hJ hKJ hQR
  obtain ⟨hm',_,hUe,hUc,_⟩ := d.unitary_core_structure h hH.1.1.2 hp m hm he
  let U := (L.pCoreIn 2).subgroupOf J
  let : IsElementaryAbelian 2 (pCore 2 L) := hUe
  let : IsElementaryAbelian 2 (L.pCoreIn 2) := IsElementaryAbelian.map L.subtype
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUJ
  let : IsElementaryAbelian 2 (J.pCoreIn 2) := hRe
  let eR : pCore 2 J ≃* J.pCoreIn 2 :=
    (pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective
  let : IsElementaryAbelian 2 (pCore 2 J) := IsElementaryAbelian.of_injective
    eR.toMonoidHom eR.injective
  have hUcard : Nat.card U = (2^m)^4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUJ).toEquiv]
    exact (Nat.card_congr ((pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective).symm.toEquiv).trans hUc
  have hRcard : Nat.card (pCore 2 J) = (2^m)^3 :=
    (Nat.card_congr ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).toEquiv).trans hRc
  have hns := UnitaryLeftCore.left_core_normalizer_not_solvable hact hphi hm' hRcard U hUcard
  have hNm : (normalizer (U : Set J)).map J.subtype =
      J ⊓ normalizer (L.pCoreIn 2 : Set G) := by
    rw [←subgroupOf_normalizer_eq hUJ,subgroupOf_map_subtype,inf_comm]
  intro hs
  apply hns
  have hs' : Group.IsSolvable ((normalizer (U : Set J)).map J.subtype) := hNm.symm ▸ hs
  let := hs'
  exact Group.isSolvable_of_isSolvable_injective
    (f := ((normalizer (U : Set J)).equivMapOfInjective J.subtype J.subtype_injective).toMonoidHom)
    ((normalizer (U : Set J)).equivMapOfInjective J.subtype J.subtype_injective).injective

/-- The nonnormal-core alternative of source 5.2.8 is impossible for both
unitary orientations, including the degree-two extension. -/
theorem Preparation.unitary_nonnormal_core_impossible
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J)
    (hn : ¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G)) : False := by
  have hQR := d.unitary_nonnormal_core_not_le h hH hp m hm he hJ hKJ.le hn
  exact d.unitary_overcomponent_left_core_normalizer_not_solvable h hH hp m hm he hJ.1 hKJ hQR
    (d.unitary_overcomponent_left_core_normalizer_solvable h hH hp m hm he hJ.1 hKJ hQR)

/-- Source 5.2.8 for the unitary row: the original right factor is maximal. -/
theorem Preparation.unitary_right_maximal :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) := by
  rcases d.unitary_maximal_or_nonnormal_core h hH hp m hm he with hmax | ⟨J,hJ,hKJ,hn⟩
  · exact hmax
  · exact (d.unitary_nonnormal_core_impossible h hH hp m hm he hJ hKJ hn).elim

/-- The literal source normalizer pair now satisfies all 5.3 local conditions
in the unitary row, with no remaining overcomponent alternative. -/
theorem Preparation.unitary_normalizer_local_conditions :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) := by
  rcases d.unitary_normalizer_or_nonnormal_core h hH hp m hm he with hlocal | ⟨J,hJ,hKJ,hn⟩
  · exact hlocal
  · exact (d.unitary_nonnormal_core_impossible h hH hp m hm he hJ hKJ hn).elim
end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
