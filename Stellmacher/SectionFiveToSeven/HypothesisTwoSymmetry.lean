module
public import Stellmacher.SectionFiveToSeven.Defs

/-!
# Symmetry in the noncentral case of Hypothesis Two

When the second member acts nontrivially on the omega-one center of the
common Sylow subgroup, Hypothesis Two also holds with the two members
interchanged. The first member then acts nontrivially on this center too.
These are the symmetry reductions at the start of Stellmacher (6.2),
Journal of Algebra 190 (1997), p.30; source:
`refs/latex/stellmacher-n-group.tex`.

The nontrivial commutator excludes alternative (5.1)(b), whose second
member lies in the center's centralizer. Alternatives (a) and (c) swap
their paired fields, preserving the actual generated join and all local
stability hypotheses. Their nonnormality field for the first member rules
out centralization, since a centralized subgroup is normalized.
-/

namespace Stellmacher.SectionsFiveToSeven

private theorem normal_of_centralizes
    {H : Type*} [Group H] (Z P : Subgroup H) (hZP : Z ≤ P)
    (hcomm : ⁅P,Z⁆ = ⊥) : NormalIn Z P := by
  refine ⟨hZP, (Subgroup.normal_subgroupOf_iff_le_normalizer hZP).mpr ?_⟩
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
    (Subgroup.centralizer_le_normalizer _)

public theorem HypothesisTwo.swap_of_commutator_ne_bot
    {H : Type*} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ ≠ ⊥) :
    HypothesisTwo H S0 S P2 P1 := by
  refine ⟨h.hyp1, ?_, h.local_B⟩
  refine ⟨h.fiveOne.S_nontrivial, h.fiveOne.S_le_S0,
    h.fiveOne.P2_mem, h.fiveOne.P1_mem, ?_, ?_⟩
  · simpa [sup_comm] using h.fiveOne.join_twoCore_eq_bot
  · cases h.fiveOne.alternative with
    | a hS h1 h2 => exact .a hS h2 h1
    | b hS hP => exact (hcomm
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hP.1.1.1)).elim
    | c M hM hS h1 h2 hJ1 hJ2 hP1 hP2 hN1 hN2 hstable htransfer =>
        exact .c M hM hS h2 h1 hJ2 hJ1 hP2 hP1 hN2 hN1 hstable htransfer

public theorem HypothesisTwo.left_commutator_ne_bot
    {H : Type*} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ ≠ ⊥) :
    ⁅P1, omegaOneCenter S⁆ ≠ ⊥ := by
  intro hzero
  have hZS : omegaOneCenter S ≤ S := Subgroup.map_subtype_le _
  have hn : NormalIn (omegaOneCenter S) P1 :=
    normal_of_centralizes _ _ (hZS.trans h.fiveOne.P1_mem.1.2.1.1) hzero
  cases h.fiveOne.alternative with
  | a _ h1 _ => exact h1 hn
  | b _ hP =>
      exact hcomm (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hP.1.1.1)
  | c _ _ _ h1 _ _ _ _ _ _ _ _ _ => exact h1 hn

end Stellmacher.SectionsFiveToSeven
