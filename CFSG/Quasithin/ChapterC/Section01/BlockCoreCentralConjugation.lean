module
public import CFSG.Quasithin.ChapterC.Section01.BlockCoreConjugation
public import Theory.GroupTheory.CommutatorPreimage
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation

/-!
# Central intersections with the core of a short block

A normal subgroup of the elementary short module is central or contains the
whole module. This follows by adjoining the central fixed layer and then
recovering the module as its commutator with the block. If an outside actor
normalizes a two-group and a subgroup of the block containing the module,
a noncommuting conjugate rules out the second alternative. This version
retains a possibly nontrivial center in the original block.

Source: Aschbacher–Smith 2.4.23(5), printed pp.537–538.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G]

/-- A normal subgroup of the actual short module either is central or contains
all of the module; adjoining its central fixed layer does not change this test. -/
theorem IsShort.normal_core_dichotomy {L : Type*} [Group L]
    (hL : IsShort L) (N : Subgroup L) [N.Normal] (hN : N ≤ blockU L) :
    N ≤ center L ∨ blockU L ≤ N := by
  let Z := blockU L ⊓ center L
  have hZ : Z ≤ blockU L := inf_le_left
  rcases hL.irreducible.2 (N ⊔ Z) inferInstance le_sup_right (sup_le hN hZ) with he | he
  · exact .inl ((show N≤N⊔Z from le_sup_left).trans (he.le.trans inf_le_right))
  · right
    rw [←ExceptionalRestrictions.short_commutator hL,←he]
    have hpre : N ⊔ Z ≤ commutatorPreimage (N ⊔ Z) (⊤ : Subgroup L) N := by
      apply sup_le
      · exact le_commutatorPreimage le_sup_left (commutator_le_left _ _)
      · apply le_commutatorPreimage le_sup_right
        rw [commutator_top_right_eq_bot_iff_le_center.mpr (show Z≤center L from inf_le_right)]
        exact bot_le
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)

/-- The noncommuting conjugate rules out the full-module alternative even
when the original block has nontrivial center. -/
theorem IsShort.inf_le_center_of_noncommuting_conjugate
    {L : Subgroup G} (hL : IsShort L) (Q R : Subgroup G)
    (hQ : IsPGroup 2 Q) (hLQ : L ≤ normalizer (Q : Set G))
    (hcore : pCore 2 L = blockU L)
    (hUR : (blockU L).map L.subtype ≤ R) (hRL : R ≤ L)
    (x : G) (hxQ : x ∈ normalizer (Q : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ ((blockU L).map L.subtype).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer ((blockU L).map L.subtype : Set G)) :
    Q ⊓ L ≤ (center L).map L.subtype := by
  let N := Q.subgroupOf L
  let : N.Normal := normal_subgroupOf_of_le_normalizer hLQ
  have hNp : IsPGroup 2 N := hQ.comap_of_injective L.subtype L.subtype_injective
  have hNU : N ≤ blockU L := hcore ▸ (show N ≤ pCore 2 L from le_sSup ⟨inferInstance,hNp⟩)
  rcases hL.normal_core_dichotomy N hNU with hc | hu
  · simpa only [N,subgroupOf_map_subtype,inf_comm] using map_mono (f:=L.subtype) hc
  · have hUQ : (blockU L).map L.subtype ≤ Q := by
      exact (map_mono hu).trans (map_comap_le _ _)
    have hUxx : ((blockU L).map L.subtype).map (MulAut.conj x⁻¹).toMonoidHom ≤ Q ⊓ L := by
      have hq : Q.map (MulAut.conj x⁻¹).toMonoidHom = Q :=
        mem_normalizer_iff_map_conj_eq.mp ((normalizer (Q : Set G)).inv_mem hxQ)
      have hr : R.map (MulAut.conj x⁻¹).toMonoidHom = R :=
        mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hxR)
      exact le_inf ((map_mono hUQ).trans_eq hq) (((map_mono hUR).trans_eq hr).trans hRL)
    have hQU : Q ⊓ L ≤ (blockU L).map L.subtype := by
      simpa only [N,subgroupOf_map_subtype,inf_comm] using map_mono (f:=L.subtype) hNU
    exfalso
    apply hnc
    let := hL.elementary
    let : IsElementaryAbelian 2 ((blockU L).map L.subtype) := IsElementaryAbelian.map L.subtype
    exact (hUxx.trans hQU).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
end CFSG.Quasithin.ChapterC
