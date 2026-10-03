module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Theory.GroupTheory.Commutator.FullActorNormalLayer
/-!
# From the V₁ bound to the initial residual bound

In the actual Section Nine local context, let U lie in the edge Sylow
subgroup and satisfy [E_initial,U]=E_initial. If U centralizes the
initial two-core modulo the initial vertex center, the whole initial
residual does so. Neither the critical length nor a faithful-action
classification is an additional hypothesis.

Restrict the core, center, residual, and U to the initial stabilizer.
The core and vertex center are normal there. The generic full-actor
normal-layer theorem applies in its quotient by the vertex center;
map the resulting commutator bound back to the ambient graph group.

This is the final transfer before the core-collapse argument in
Stellmacher (9.1), Journal of Algebra190 (1997), p.48, relation(11).
It leaves the genuine core-action bound explicit for the source's
noncentral-chief-factor exclusion to supply.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u
public theorem distance_one_residual_bound_of_v1_bound
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (U : Subgroup G) (hUT : U ≤ T)
    (hEU : ⁅twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a),U⁆ =
      twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a))
    (hQU : ⁅q ctx.Γ ctx.criticalPath.a,U⁆ ≤ z ctx.Γ ctx.criticalPath.a) :
    ⁅q ctx.Γ ctx.criticalPath.a,twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a)⁆ ≤
      z ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Q := q Γ cp.a
  let Z := z Γ cp.a
  let E := twoResidualIn P
  have hUP : U ≤ P := hUT.trans (edge_sylow_data ctx.sectionSeven Γ cp).1.1
  have hQP : Q ≤ P := by
    change q Γ cp.a ≤ stabilizer Γ cp.a
    rw [q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hEP : E ≤ P := Subgroup.map_subtype_le _
  have hZQ : Z ≤ Q :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).trans
      (Subgroup.map_subtype_le _)
  have hZP := hZQ.trans hQP
  let _ : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr (stabilizer_le_normalizer_q Γ cp.a)
  let _ : (Z.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZP).mpr (stabilizer_le_normalizer_z Γ cp.a)
  have hQU' : ⁅Q.subgroupOf P,U.subgroupOf P⁆ ≤ Z.subgroupOf P := by
    apply Subgroup.commutator_le.mpr
    intro q hq u hu
    exact hQU (Subgroup.commutator_mem_commutator hq hu)
  have hEU' : ⁅E.subgroupOf P,U.subgroupOf P⁆ = E.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hEP,
      Subgroup.map_subgroupOf_eq_of_le hUP,hEU]
  have h := Subgroup.map_mono (f := P.subtype)
    (Subgroup.commutator_le_of_full_actor (Q.subgroupOf P) (E.subgroupOf P)
      (U.subgroupOf P) (Z.subgroupOf P) hQU' hEU')
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQP,
    Subgroup.map_subgroupOf_eq_of_le hEP, Subgroup.map_subgroupOf_eq_of_le hZP] at h
  exact h
end Stellmacher.SectionNine
