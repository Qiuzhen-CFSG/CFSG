module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointJoinResidual
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The actual restricted carrier join retains its PSL3(2) quotient

The smaller component is the residual of the full original Sylow join.
Its perfect quotient by the two-core is therefore covered by every
intermediate subgroup containing that residual. Restricting the original
Sylow to the actual normal carrier gives just such a subgroup. The
literal restricted join consequently has two-core quotient PSL3(2),
with no new quotient or flag premise.

Source: Aschbacher--Smith15.3.23, printed pp.1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open ChapterC BinaryMS.MS93

private theorem quotient_of_residual_le
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect (A ⧸ pCore 2 A)]
    (H : Subgroup A) (hH : pResidual 2 A ≤ H) :
    Nonempty ((H ⧸ pCore 2 H) ≃* (A ⧸ pCore 2 A)) := by
  let q := QuotientGroup.mk' (pCore 2 A)
  have himage : H.map q = ⊤ := by
    apply top_unique
    rw [←pResidual_eq_top_of_isPerfect 2,
      ←map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)]
    exact map_mono hH
  let f := q.comp H.subtype
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp (by
    rw [MonoidHom.range_comp,range_subtype]
    exact himage)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((q.comp H.subtype).ker)
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  exact ⟨(f.pCoreQuotientEquiv hf hk).trans
    ((QuotientGroup.quotientMulEquivOfEq (pCore_quotient_pCore_eq_bot (p := 2))).trans
      QuotientGroup.quotientBot)⟩

variable {G : Type*} [Group G] [Finite G]

/-- The same full Sylow restricted to the normal containing carrier gives
an actual join whose quotient by its own two-core is still PSL3(2). -/
theorem binary_three_point_containing_join_core_quotient
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (z : G) (hLS : L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (L.subgroupOf C).map q
    let S := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
    ∃ T : Sylow 2 K, (T : Subgroup K) = (S : Subgroup (C ⧸ pCore 2 C)).subgroupOf K ∧
      let J₀ := B.subgroupOf K ⊔ (T : Subgroup K)
      Nonempty ((J₀ ⧸ pCore 2 J₀) ≃* PSL(3,ZMod 2)) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (L.subgroupOf C).map q
  let S := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
  let J := B ⊔ (S : Subgroup (C ⧸ pCore 2 C))
  obtain ⟨hres,T,hT,_⟩ := binary_three_point_join_residual d L b z hLS P hP K hBK
  change (pResidual 2 J).map J.subtype = B at hres
  change (T : Subgroup K) = (S : Subgroup (C ⧸ pCore 2 C)).subgroupOf K at hT
  obtain ⟨eJ⟩ := binary_three_point_join_core_quotient d L b z hLS P hP
  let : Group.IsPerfect (PSL(3,ZMod 2)) := Atlas.psl_perfect 3 (by decide)
  let : Group.IsPerfect (J ⧸ pCore 2 J) :=
    Group.IsPerfect.ofSurjective (f := eJ.symm.toMonoidHom) eJ.symm.surjective
  let D := B.subgroupOf K
  let J₀ := D ⊔ (T : Subgroup K)
  let Y := J₀.map K.subtype
  have hTmap : (T : Subgroup K).map K.subtype ≤ (S : Subgroup _) := by
    rintro x ⟨t,ht,rfl⟩
    rw [hT] at ht
    exact ht
  have hYJ : Y ≤ J := by
    change (D ⊔ (T : Subgroup K)).map K.subtype ≤ J
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBK]
    exact sup_le le_sup_left (hTmap.trans le_sup_right)
  have hBY : B ≤ Y := by
    have hh := map_mono (f := K.subtype) (show D ≤ J₀ from le_sup_left)
    rwa [map_subgroupOf_eq_of_le hBK] at hh
  have hHY : pResidual 2 J ≤ Y.subgroupOf J := by
    intro x hx
    have hh := mem_map_of_mem J.subtype hx
    rw [hres] at hh
    exact hBY hh
  obtain ⟨eY⟩ := quotient_of_residual_le (Y.subgroupOf J) hHY
  let i : J₀ ≃* Y.subgroupOf J :=
    (J₀.equivMapOfInjective K.subtype K.subtype_injective).trans (subgroupOfEquivOfLe hYJ).symm
  exact ⟨T,hT,⟨((QuotientGroup.congr _ _ i (pCore_map_iso 2 i)).trans eY).trans eJ⟩⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
