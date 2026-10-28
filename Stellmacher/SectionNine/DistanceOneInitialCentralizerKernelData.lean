module
public import Stellmacher.SectionNine.NineTwoAmbientCentralizerCommutator
/-!
# Initial-center kernel data from the actual (7.7)(a) bound

In an ambient Section Nine configuration of critical length one, suppose
U lies in the terminal two-core and is its own commutator with the
terminal residual. Then U lies in that residual's two-core. The kernel
C of the initial stabilizer's action on its vertex center is normal,
meets the edge Sylow in the initial two-core, and centralizes both the
initial residual and U modulo that core.

Normality of the terminal residual first places U inside it. Its
intersection with the terminal core is precisely its own two-core.
The already proved ambient-retaining (7.7)(a) bound therefore applies
to both specified actors. Normalizer covariance supplies C's normality,
and (7.4)'s edge-centralizer equality supplies the Sylow intersection.
All conclusions retain the original graph group and ambient hypotheses.

This is the exact kernel input in the use of (7.7)(a) before Stellmacher
(9.1)(10), Journal of Algebra190 (1997), p.47. It does not identify the
full initial-center kernel with the core.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u
public theorem distance_one_initial_centralizer_kernel_data
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (U : Subgroup G)
    (hUQ : U ≤ q ctx.Γ ctx.criticalPath.a')
    (hUE : ⁅U,twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a')⁆ = U) :
    let P := stabilizer ctx.Γ ctx.criticalPath.a
    let C := P ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G)
    U ≤ twoCoreIn (twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a')) ∧
    (C.subgroupOf P).Normal ∧ C ⊓ T = q ctx.Γ ctx.criticalPath.a ∧
    ⁅C,twoResidualIn P⁆ ≤ q ctx.Γ ctx.criticalPath.a ∧
    ⁅C,U⁆ ≤ q ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let R := stabilizer Γ cp.a'
  let E := twoResidualIn R
  let C := P ⊓ Subgroup.centralizer (z Γ cp.a : Set G)
  have hlen : cp.length = 1 := hb
  have hstep : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hb.symm
      _ = cp.a' := cp.path_end
  have hQP : q Γ cp.a' ≤ R := by
    change q Γ cp.a' ≤ stabilizer Γ cp.a'
    rw [q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hRE : R ≤ Subgroup.normalizer (E:Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidualIn_le R)).mp (twoResidualIn_normal R)
  have hUEle : U ≤ E := by
    rw [← hUE]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp ((hUQ.trans hQP).trans hRE)
  have hUcore : U ≤ twoCoreIn E := by
    rw [residual_core_eq_inter_core]
    refine le_inf hUEle ?_
    change U ≤ twoCoreIn (stabilizer Γ cp.a')
    change U ≤ q Γ cp.a' at hUQ
    rw [q,Γ.twoCoreAt_def] at hUQ
    exact hUQ
  have hPnormC : P ≤ Subgroup.normalizer (C:Set G) :=
    (le_inf Subgroup.le_normalizer ((stabilizer_le_normalizer_z Γ cp.a).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (z Γ cp.a:Set G))).mp inferInstance))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hCn : (C.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hPnormC
  have hCT : C ⊓ T = q Γ cp.a := by
    have hTP : T ≤ P := (edge_sylow_data ctx.sectionSeven Γ cp).1.1
    change (P ⊓ Subgroup.centralizer (z Γ cp.a:Set G)) ⊓ T = _
    rw [inf_right_comm, inf_eq_right.mpr hTP, (lemma_seven_four ctx.sectionSeven Γ cp).edge_centralizer]
  have h77 : ⁅C,twoResidualIn P ⊔ twoCoreIn E⁆ ≤ q Γ cp.a := by
    have hh := nine_two_initial_centralizer_commutator ctx
    change ⁅Subgroup.centralizer (z Γ cp.a:Set G),
      e Γ cp.a ⊔ twoCoreIn (e Γ cp.firstStep)⁆ ≤ q Γ cp.a at hh
    rw [hstep, CosetGraphContext.e, CosetGraphContext.e, Γ.twoResidualAt_def, Γ.twoResidualAt_def] at hh
    exact (Subgroup.commutator_mono inf_le_right le_rfl).trans hh
  exact ⟨hUcore,hCn,hCT,(Subgroup.commutator_mono le_rfl le_sup_left).trans h77,
    (Subgroup.commutator_mono le_rfl (hUcore.trans le_sup_right)).trans h77⟩
end Stellmacher.SectionNine
