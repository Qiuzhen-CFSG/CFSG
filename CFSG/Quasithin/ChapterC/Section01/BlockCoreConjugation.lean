module
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.PCoreLocalSetup
/-!
# A normal core and a noncommuting conjugate of a short module

For a centerless short block with O₂(L)=U(L), irreducibility makes any
normalized two-subgroup intersect L trivially or contain all of U(L).
The latter alternative is impossible if an actor normalizes that two-group
and a subgroup of L containing U(L), but sends U(L) to a noncommuting module.

Source: Aschbacher–Smith, the core argument in 2.4.7, printed p.541.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G]

/-- A normal two-subgroup cannot meet a centerless short block whose
natural core has a noncommuting conjugate inside the same Sylow factor. -/
theorem IsShort.inf_eq_bot_of_noncommuting_conjugate
    {L : Subgroup G} (hL : IsShort L) (Q R : Subgroup G)
    (hQ : IsPGroup 2 Q) (hLQ : L ≤ normalizer (Q : Set G))
    (hcenter : center L = ⊥) (hcore : pCore 2 L = blockU L)
    (hUR : (blockU L).map L.subtype ≤ R) (hRL : R ≤ L)
    (x : G) (hxQ : x ∈ normalizer (Q : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ ((blockU L).map L.subtype).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer ((blockU L).map L.subtype : Set G)) :
    Q ⊓ L = ⊥ := by
  let N := Q.subgroupOf L
  let : N.Normal := normal_subgroupOf_of_le_normalizer hLQ
  have hNp : IsPGroup 2 N := hQ.comap_of_injective L.subtype L.subtype_injective
  have hNU : N ≤ blockU L := hcore ▸ (show N ≤ pCore 2 L from le_sSup ⟨inferInstance,hNp⟩)
  have hlow : blockU L ⊓ center L ≤ N := by rw [hcenter,inf_bot_eq]; exact bot_le
  rcases hL.irreducible.2 N inferInstance hlow hNU with he | he
  · have hm := congrArg (Subgroup.map L.subtype) he
    simpa only [N,subgroupOf_map_subtype,hcenter,inf_bot_eq,bot_inf_eq,Subgroup.map_bot,inf_comm] using hm
  · have hm : Q ⊓ L = (blockU L).map L.subtype := by
      simpa only [N,subgroupOf_map_subtype,inf_comm] using congrArg (Subgroup.map L.subtype) he
    have hUQ : (blockU L).map L.subtype ≤ Q := hm.symm.le.trans inf_le_left
    have hUxx : ((blockU L).map L.subtype).map (MulAut.conj x⁻¹).toMonoidHom ≤ Q ⊓ L := by
      have hq : Q.map (MulAut.conj x⁻¹).toMonoidHom = Q :=
        mem_normalizer_iff_map_conj_eq.mp ((normalizer (Q : Set G)).inv_mem hxQ)
      have hr : R.map (MulAut.conj x⁻¹).toMonoidHom = R :=
        mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hxR)
      exact le_inf ((map_mono hUQ).trans_eq hq) (((map_mono hUR).trans_eq hr).trans hRL)
    exfalso
    apply hnc
    let := hL.elementary
    let : IsElementaryAbelian 2 ((blockU L).map L.subtype) := IsElementaryAbelian.map L.subtype
    exact (hUxx.trans_eq hm).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)

end CFSG.Quasithin.ChapterC

