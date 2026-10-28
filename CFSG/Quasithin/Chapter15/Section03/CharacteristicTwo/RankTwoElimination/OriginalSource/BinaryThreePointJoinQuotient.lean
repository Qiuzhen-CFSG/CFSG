module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointQuotient

/-!
# The original Sylow join keeps its binary-three quotient

The marked BinaryMS input supplies the actual projection
LS → SL₃(2), with kernel exactly O₂(LS). At the chosen original point
centralizer C, its full Sylow P maps onto the original S. Thus the image
of LS in C/O₂(C) is precisely the join of the original component image
with the image of P. Removing the two-group kernel preserves the
quotient by the two-core, including its PSL₃(2) marking.

This retains the stronger original Sylow-join datum needed by the odd
ternary carrier sieve; a smaller-component quotient alone would discard it.
Source: Aschbacher--Smith 15.3.23, printed pp.1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- The literal point quotient preserves the PSL₃(2) marking of the join
of the smaller component with the full original Sylow. -/
theorem binary_three_point_join_core_quotient
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (z : G) (hLS : L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (L.subgroupOf C).map q
    let Pbar := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
    let J := B ⊔ (Pbar : Subgroup (C ⧸ pCore 2 C))
    Nonempty ((J ⧸ pCore 2 J) ≃* PSL(3,ZMod 2)) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let J := L ⊔ d.S
  let A := J.subgroupOf C
  have hLC : L ≤ C := le_sup_left.trans hLS
  have hSC : d.S ≤ C := le_sup_right.trans hLS
  have hPe : (P : Subgroup C) = d.S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le hSC]
    exact hP
  have himage : A.map q = (L.subgroupOf C).map q ⊔
      (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) : Subgroup (C ⧸ pCore 2 C)) := by
    change (J.subgroupOf C).map q = _
    rw [show J = L ⊔ d.S from rfl,subgroupOf_sup hLC hSC,Subgroup.map_sup]
    congr 1
    change (d.S.subgroupOf C).map q = (P : Subgroup C).map q
    rw [hPe]
  have hk : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let a : A ≃* J := subgroupOfEquivOfLe hLS
  let e : (J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.SL :=
    (QuotientGroup.quotientMulEquivOfEq b.coreProjection_kernel.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective b.coreProjection b.coreProjection_surjective)
  have he : Nonempty (((A.map q) ⧸ pCore 2 (A.map q)) ≃* PSL(3,ZMod 2)) :=
    ⟨((q.subgroupMap A).pCoreQuotientEquiv (q.subgroupMap_surjective A) hk).symm.trans
      (((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e).trans Matrix.PSL3Two.equiv)⟩
  let j := MulEquiv.subgroupCongr himage
  exact ⟨((QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).symm.trans he.some)⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
