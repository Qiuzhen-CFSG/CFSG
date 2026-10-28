module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerPlane
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionAmbient
public import Theory.Representation.BinaryAlternatingFiveExtension.SylowModel
public import Theory.SpecificGroups.SymmetricFourWreath.ElementaryGeometry
public import Theory.SpecificGroups.SymmetricFourWreath.ElementaryGeometry.Intersections

/-!
# The elementary subgroup family of the original exceptional Sylow

The proved ambient Sylow marking and the literal extended-plane equivalence
identify the original T with D8 wr C2. The existing dihedral wreath calculation
therefore bounds every elementary subgroup of T by sixteen. Its four coordinate
products exhaust those of order sixteen, and injective transport shows that
the original ambient family has exactly four members.

Source: Aschbacher--Smith F.5.4(4), printed p.301. Only the original source
hypotheses are used. The labels A1, A2, A2^y, Q2 and their conjugacy properties
require additional source arguments; this module proves the bound and exhaustion.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn)
  (h : Source.Hypotheses c i z)
include h

theorem normalizer_T_wreath : Nonempty (Source.sylowImage c i ≃* SymmetricFourWreath.P) := by
  obtain ⟨S,hS⟩ := source_sylowImage_isSylow c i z h
  have hSM : (S : Subgroup G) ≤ M c i true := hS ▸ sylowImage_le_M c i true
  let S' : Sylow 2 (M c i true) := S.subtype hSM
  obtain ⟨e,_,_,_⟩ := UnitaryTwo.ExtendedAffinePlane.exists_marked_plane_equiv
  let eM : M c i true ≃* BinaryPermutation.AlternatingFiveExtension.Model :=
    (MonoidHom.ofInjective (endpointMap_injective c i h.embedding_injective true)).symm.trans e.symm
  let S'' := S'.mapSurjective (f := eM.toMonoidHom) eM.surjective
  exact ⟨(MulEquiv.subgroupCongr hS.symm).trans
    ((subgroupOfEquivOfLe hSM).symm.trans
      (((S' : Subgroup (M c i true)).equivMapOfInjective eM.toMonoidHom eM.injective).trans
        (BinaryPermutation.AlternatingFiveExtension.SylowModel.sylowEquiv S'')))⟩

theorem normalizer_elementary_bound (B : Subgroup G) (hB : B ≤ Source.sylowImage c i)
    (he : IsElementaryAbelian 2 B) : Nat.card B ≤ 16 := by
  obtain ⟨e⟩ := normalizer_T_wreath c i z h
  let B' := B.subgroupOf (Source.sylowImage c i)
  have he' : IsElementaryAbelian 2 B' := IsElementaryAbelian.subgroupOf hB
  have hh := SymmetricFourWreath.elementaryInP_card_bound (B'.map e.toMonoidHom) (he'.map _)
  rw [card_map_of_injective e.injective,
    Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv] at hh
  exact hh

theorem normalizer_elementary_family_card :
    Nat.card {B : Subgroup G // B ≤ Source.sylowImage c i ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 16} = 4 := by
  classical
  obtain ⟨e⟩ := normalizer_T_wreath c i z h
  let j : SymmetricFourWreath.P →* G := (Source.sylowImage c i).subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := (Source.sylowImage c i).subtype_injective.comp e.symm.injective
  have hcomp : j.comp e.toMonoidHom = (Source.sylowImage c i).subtype := by
    ext x
    change (e.symm (e x)).val = x.val
    rw [e.symm_apply_apply]
  let F (a : Bool × Bool) : {B : Subgroup G // B ≤ Source.sylowImage c i ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 16} :=
    ⟨(SymmetricFourWreath.elementaryInP a.1 a.2).map j,
      by rintro _ ⟨x,_,rfl⟩;exact (e.symm x).property,
      IsElementaryAbelian.map j,by rw [card_map_of_injective hj,SymmetricFourWreath.card_elementaryInP]⟩
  have hF : Function.Bijective F := by
    constructor
    · intro a b hab
      have hbase := Subgroup.map_injective hj (congrArg Subtype.val hab)
      apply SymmetricFourWreath.elementary_injective
      exact congrArg (fun U : Subgroup SymmetricFourWreath.P =>
        U.map SymmetricFourWreath.sylowEmbedding) hbase
    · rintro ⟨B,hB,hBe,hBc⟩
      let B0 := (B.subgroupOf (Source.sylowImage c i)).map e.toMonoidHom
      let := hBe
      have hB0e : IsElementaryAbelian 2 B0 := by
        let : IsElementaryAbelian 2 (B.subgroupOf (Source.sylowImage c i)) :=
          IsElementaryAbelian.subgroupOf hB
        exact IsElementaryAbelian.map _
      have hB0c : Nat.card B0 = 16 := by
        rw [card_map_of_injective e.injective,
          Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv,hBc]
      have hB0map : B0.map j = B := by
        rw [map_map,hcomp,map_subgroupOf_eq_of_le hB]
      obtain ⟨a,b,hab⟩ := (SymmetricFourWreath.maximum_elementaryInP B0).mp
        ⟨le_top,hB0e,fun U _ hU =>
          (SymmetricFourWreath.elementaryInP_card_bound U hU).trans_eq hB0c.symm⟩
      refine ⟨(a,b),Subtype.ext ?_⟩
      change (SymmetricFourWreath.elementaryInP a b).map j = B
      rw [←hab,hB0map]
  rw [←Nat.card_congr (Equiv.ofBijective F hF)]
  norm_num [Nat.card_eq_fintype_card]

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
