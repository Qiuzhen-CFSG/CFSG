module

public import Theory.GroupTheory.CyclicIndexTwoTransfer
public import CFSG.Quasithin.ChapterI.Section04To05.SmallSylow.DihedralData
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# The central involution centralizer in the dihedral case

The actual Sylow subgroup lies in the centralizer of its rotation involution.
The cyclic-index-two transfer theorem produces a normal odd complement there.
Even characteristic, applied to this two-local Sylow overgroup, gives a
self-centralizing two-core and therefore trivial odd core. Thus the whole
centralizer is the original Sylow subgroup.

Source: Aschbacher–Smith I.4.3, printed p.416.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterI.SmallSylow
variable {G : Type*} [Group G] [Finite G]
/-- Even characteristic kills the odd complement in the central involution centralizer. -/
public theorem centralizer_eq_sylow_of_rotation_data
    (T : Sylow 2 G) (hE : IsEvenCharacteristic G)
    (R : Subgroup T) [IsCyclic R] (hindex : R.index = 2)
    (z : R) (hz : orderOf z = 2) (hzT : (z : T) ∈ center T)
    (hout : ∀ v : T, v ∉ R → orderOf v = 2) :
    centralizer ({(z : G)} : Set G) = (T : Subgroup G) := by
  let H := centralizer ({(z : G)} : Set G)
  have hzG : orderOf (z : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hz
  have hTH : (T : Subgroup G) ≤ H := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp hzT ⟨x, hx⟩)
  let S := T.subtype hTH
  let e : S ≃* T := subgroupOfEquivOfLe hTH
  let R' := R.map e.symm.toMonoidHom
  let : IsCyclic R' := (e.symm.subgroupMap R).isCyclic.mp inferInstance
  let z' : R' := e.symm.subgroupMap R z
  have hi : R'.index = 2 := (index_map_equiv R e.symm).trans hindex
  have hz' : orderOf z' = 2 := ((e.symm.subgroupMap R).orderOf_eq z).trans hz
  have hzc : (z' : H) ∈ center H := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp x.property)
  have hout' : ∀ v : S, v ∉ R' → orderOf v = 2 := by
    intro v hv
    have hne : e v ∉ R := by
      intro he
      exact hv ⟨e v, he, e.symm_apply_apply v⟩
    exact (e.orderOf_eq v).symm.trans (hout (e v) hne)
  have hcomp : HasNormalPComplement 2 H :=
    S.normalTwoComplement_of_cyclic_index_two R' hi z' hz' hzc hout'
  have hchar : HasCharacteristicTwo H :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T (hE T)
      (Theory.GroupTheory.isTwoLocal_involution_centralizer hzG) hTH)
  have ho : pPrimeCore 2 H = ⊥ :=
    Theory.GroupTheory.pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hchar
  have hHp : IsPGroup 2 H := by
    have hq := isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 H hcomp
    exact hq.of_equiv ((QuotientGroup.quotientMulEquivOfEq ho).trans
      QuotientGroup.quotientBot)
  exact (T.is_maximal' hHp hTH)
end CFSG.Quasithin.ChapterI.SmallSylow
