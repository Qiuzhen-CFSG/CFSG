module
public import Stellmacher.LaterDefs
public import Stellmacher.ElementaryAbelianMaxOrder
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts

/-!
# The next-core Thompson subgroup is outside the initial core

Assume Qa=Za and Qa lies in the next vertex core T for the actual Section
Eight critical pair. Then J(T) is not contained in Qa. If it were, a
maximal elementary subgroup of T and the elementary subgroup Qa would have
the same maximal order, giving J(T)=Qa. The next stabilizer normalizes J(T)
and the initial stabilizer normalizes Qa. Their join is the ambient group,
so Qa would be a nontrivial normal two-subgroup, contrary to Hypothesis Two.

This supplies the noncontainment needed for the application of (3.4) in
Stellmacher (8.3), journal p38, after its center-free core collapse.
The proof uses the actual graph stabilizers and their generating edge.
Source: refs/latex/stellmacher-n-group.tex.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext

public theorem eight_three_thompson_not_le_core
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcore : QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a)
    (hcontained : QAt ctx.Γ ctx.criticalPath.a ≤ QAt ctx.Γ ctx.criticalPath.firstStep) :
    ¬ elementaryAbelianMaxJ (QAt ctx.Γ ctx.criticalPath.firstStep) ≤
      QAt ctx.Γ ctx.criticalPath.a := by
  classical
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Pb := stabilizer Γ cp.firstStep
  let Q := q Γ cp.a
  let T := q Γ cp.firstStep
  let J := elementaryAbelianMaxJ T
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have helem : IsElementaryAbelian 2 Q := by
    change IsElementaryAbelian 2 (QAt Γ cp.a)
    rw [hcore]
    exact SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  have hQT : Q ≤ T := hcontained
  intro hJQ
  have hQJ : Q ≤ J := by
    obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty T
    have hAQ : A ≤ Q := (le_sSup hA).trans hJQ
    have heq : A = Q := Subgroup.eq_of_le_of_card_ge hAQ (hA.2.2 Q hQT helem)
    rw [← heq]
    exact le_sSup hA
  have hJ : J = Q := le_antisymm hJQ hQJ
  have hPbT : Pb ≤ Subgroup.normalizer (T : Set H) := by
    rw [show T = twoCoreIn Pb from Γ.twoCoreAt_def cp.firstStep]
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hPbQ : Pb ≤ Subgroup.normalizer (Q : Set H) := by
    rw [← hJ]
    intro g hg
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (elementaryAbelianMaxJ T).map (MulAut.conj g).toMonoidHom = elementaryAbelianMaxJ T
    rw [← elementaryAbelianMaxJ_map_equiv]
    have ht : T.map (MulAut.conj g).toMonoidHom = T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPbT hg)
    rw [ht]
  have hPQ : P ≤ Subgroup.normalizer (Q : Set H) := by
    rw [show Q = twoCoreIn P from Γ.twoCoreAt_def cp.a]
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hcover : P ⊔ Pb = ⊤ := by
    rcases cp.edge_stabilizers_are_P with hedge | hedge
    · rw [show P = P1 from hedge.1, show Pb = P2 from hedge.2, ctx.generated]
    · rw [show P = P2 from hedge.1, show Pb = P1 from hedge.2, sup_comm, ctx.generated]
  have hQN : Q.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hcover]
    exact sup_le hPQ hPbQ
  have hQp : IsPGroup 2 Q := by
    rw [show Q = twoCoreIn P from Γ.twoCoreAt_def cp.a]
    exact (pCore_isPGroup (p := 2) (G := P)).map P.subtype
  have hQbot : Q = ⊥ := le_bot_iff.mp
    ((show Q ≤ pCore 2 H from le_sSup ⟨hQN, hQp⟩).trans_eq h.twoCore_eq_bot)
  have hPset := (SevenSix.edge_local_data h Γ cp).1
  apply hPset.1.1.2.2.1
  exact (show Q = twoCoreIn P from Γ.twoCoreAt_def cp.a).symm.trans hQbot

end Stellmacher.SectionEight
