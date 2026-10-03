module
public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.QuotientModuleOffender
public import Stellmacher.SectionEight.LemmaEightOneIndex

/-!
# The critical endpoint supplies a nontrivial quotient offender

For the initial center's faithful quotient-module witness, the projected
final endpoint center lies in Section 1's offender family for the projected
Sylow S. In particular, the resulting J is nontrivial, so Stellmacher (1.7)
applies to this exact action.

Critical minimality places the final center in S. The local quotient index
bound at the opposite endpoint gives the reversed ambient inequality, which
transports to the offender condition m ≤ 1. A trivial projected endpoint
center would lie in the centralizer kernel and make the two endpoint centers
commute, contrary to the Section 8 hypothesis.

This is the step asserting barred Z_{a'} ≤ J(Z_a, barred S) in the proof
of (8.1), journal p.37. The witness action and faithful image orders are
retained throughout; no ambient LocalJ surrogate is used. The graph-local
endpoint `eight_five_offender_local` is owned here so the opposite-closure
foundation can reuse it without importing the later order-four recognition.
The original canonical theorem is a graph-preserving wrapper.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

/-- The opposite center projects to a nontrivial offender for the initial center. -/
public theorem eight_five_offender_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    SectionOne.oneA (G := w.X) (V := ZAt ctx.Γ ctx.criticalPath.a)
      ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection)
      (((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
        (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) ∧
    SectionOne.oneJ (G := w.X) (V := ZAt ctx.Γ ctx.criticalPath.a)
      ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) ≠ ⊥ := by
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have h74 := lemma_seven_four h Γ cp
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hlen := cp.length_pos
  let last : Γ.Vertex := cp.path ⟨cp.length - 1, by omega⟩
  have hlastadj : Γ.adjacent cp.a' last := by
    have he := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hi : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hi, cp.path_end] at he
    exact Γ.adjacent_symm he
  have hlast : last ∈ neighborhood Γ cp.a' :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hlastadj
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hlast
  have hZendS : z Γ cp.a' ≤ S := by
    have hdist : Γ.distance cp.a' cp.firstStep < cp.length := by
      rw [Γ.distance_symm]
      have hd := SevenSix.path_distance_le Γ cp 1 cp.length (by omega) le_rfl
      have hd' : Γ.distance cp.firstStep cp.a' ≤ cp.length - 1 := by
        simpa [cp.path_first, cp.path_end] using hd
      omega
    exact (SevenSix.critical_minimality Γ cp hdist).trans
      (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hSP : S ≤ stabilizer Γ cp.a := cp.S_le_edge_stabilizers.trans inf_le_left
  have hZaPend : z Γ cp.a ≤ stabilizer Γ cp.a' :=
    h74.first_containment.1.trans h74.first_containment.2
  have hZanot : ¬ z Γ cp.a ≤ Subgroup.centralizer (z Γ cp.a' : Set G) := by
    intro hcentral
    exact ctx.commutator_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral)
  have hbound := local_quotient_index_bound h Γ cp.a' hlast (z Γ cp.a) hZaPend hZanot
  have hA := w.oneA_of_card_le (z Γ cp.a') S hZendS hSP hbound
  refine ⟨hA, ?_⟩
  intro hJbot
  apply ctx.commutator_ne
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro y hy
  let yA : stabilizer Γ cp.a := ⟨y, hZendS.trans hSP hy⟩
  have himage : w.projection yA ∈
      ((z Γ cp.a').subgroupOf (stabilizer Γ cp.a)).map w.projection :=
    Subgroup.mem_map_of_mem w.projection hy
  have hJle : ((z Γ cp.a').subgroupOf (stabilizer Γ cp.a)).map w.projection ≤
      SectionOne.oneJ (G := w.X) (V := z Γ cp.a)
        ((S.subgroupOf (stabilizer Γ cp.a)).map w.projection) := le_sSup hA
  have hJmem := hJle himage
  rw [hJbot, Subgroup.mem_bot] at hJmem
  have hk : yA ∈ w.projection.ker := hJmem
  rw [w.kernel_eq] at hk
  exact hk.2

/-- The opposite center projects to a nontrivial offender for the initial center. -/
public theorem lemma_eight_one_offender
    {G : Type u} [Group G] [Finite G]
    {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    SectionOne.oneA (G := w.X) (V := ZAt ctx.Γ ctx.criticalPath.a)
      ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection)
      (((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
        (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) ∧
    SectionOne.oneJ (G := w.X) (V := ZAt ctx.Γ ctx.criticalPath.a)
      ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) ≠ ⊥ := by
  exact eight_five_offender_local ctx.toLocalContext w

end Stellmacher.SectionEight
