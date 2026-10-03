module

public import Stellmacher.SectionNine.DistanceOneChiefBranchReduction

/-!
# The terminal-product commutator bound in the noncentral chief branch

At distance one the terminal vertex center lies in the initial vertex center.
Consequently every subgroup of Z_initial Q_terminal has commutator with the
extracted U contained in Z_initial. This is the last commutator implication
in the fixed-complement paragraph on printed p.48 of Stellmacher's paper.
It does not construct the fixed complement or assert its required containment.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u

public theorem distance_one_terminal_center_le_initial_center
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : ctx.criticalPath.length = 1) :
    z ctx.Γ ctx.criticalPath.a' ≤ z ctx.Γ ctx.criticalPath.a := by
  have hstep : ctx.criticalPath.firstStep = ctx.criticalPath.a' := by
    rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
    congr 1
    exact Fin.ext hb.symm
  have hcenter :=
    (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).next_center.1
  rw [hstep] at hcenter
  rw [hcenter]
  obtain ⟨_, sylow, hsylow⟩ :=
    (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  rw [z, ctx.Γ.zAt_def]
  exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩

private theorem commutator_join_le
    {G : Type*} [Group G] (actors first second target : Subgroup G)
    (hnorm : first ⊔ second ≤ Subgroup.normalizer (target : Set G))
    (hfirst : ⁅actors, first⁆ ≤ target) (hsecond : ⁅actors, second⁆ ≤ target) :
    ⁅actors, first ⊔ second⁆ ≤ target := by
  apply Subgroup.commutator_le.mpr
  intro actor hactor element helement
  have hclosure : Subgroup.closure ((first : Set G) ∪ (second : Set G)) = first ⊔ second := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [← hclosure] at helement
  induction helement using Subgroup.closure_induction with
  | mem element helement =>
    rcases helement with hmem | hmem
    · exact Subgroup.commutator_le.mp hfirst actor hactor element hmem
    · exact Subgroup.commutator_le.mp hsecond actor hactor element hmem
  | one => simp
  | mul firstElement secondElement hfirstMem _ hfirstComm hsecondComm =>
    rw [commutatorElement_mul_right_eq_mul_conj]
    simpa only [mul_assoc] using target.mul_mem hfirstComm
      ((Subgroup.le_normalizer_iff.mp hnorm firstElement (hclosure ▸ hfirstMem))
        _ hsecondComm)
  | inv element helement hcomm =>
    rw [commutatorElement_inv_right, ← commutatorElement_inv]
    simpa only [inv_inv] using Subgroup.le_normalizer_iff.mp hnorm element⁻¹
      ((first ⊔ second).inv_mem (hclosure ▸ helement)) _ (target.inv_mem hcomm)

public theorem distance_one_chief_terminal_product_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (branch : DistanceOneChiefBranchData ctx)
    (fixed : Subgroup G)
    (hfixed : fixed ≤ z ctx.Γ ctx.criticalPath.a ⊔ q ctx.Γ ctx.criticalPath.a') :
    ⁅fixed, branch.U⁆ ≤ z ctx.Γ ctx.criticalPath.a := by
  let initial := z ctx.Γ ctx.criticalPath.a
  let terminal := q ctx.Γ ctx.criticalPath.a'
  have hTnorm : T ≤ Subgroup.normalizer (initial : Set G) :=
    (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1.trans
      (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a)
  have hstep : ctx.criticalPath.firstStep = ctx.criticalPath.a' := by
    rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
    congr 1
    exact Fin.ext hb.symm
  have hterminal : terminal ≤ T := by
    have hcores := (local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
    rwa [hstep] at hcores
  have hinitial : ⁅branch.U, initial⁆ ≤ initial :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp (branch.le_sylow.trans hTnorm)
  have hcomm : ⁅branch.U, terminal⁆ ≤ initial := by
    rw [branch.terminal_core_commutator]
    exact distance_one_terminal_center_le_initial_center ctx.toLocalContext hb
  rw [Subgroup.commutator_comm]
  exact (Subgroup.commutator_mono le_rfl hfixed).trans
    (commutator_join_le branch.U initial terminal initial
      (sup_le Subgroup.le_normalizer (hterminal.trans hTnorm)) hinitial hcomm)

end Stellmacher.SectionNine
