module

public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.SectionFiveToSeven.SixThreeNativeQuotients
public import Stellmacher.SL2FrattiniDihedralCore

/-!
# Stellmacher (6.3): the two ordinary dihedral core quotients

Under Hypothesis Two, nontrivial action by P2 on Omega_1(Z(S)) forces both
ordinary quotients Pi/O2(Pi) to be dihedral with rotation order a power of
three. The native-quotient companion proves B(S)=S and identifies both
nested Frattini quotients with SL2(2), using the actual selected modules,
core-free pair and small-hyperplane argument.

The local groups are solvable by (5.3) and have nontrivial two-core by their
family membership. In each core-free quotient the Frattini subgroup has
odd order; its Sylow subgroup therefore has order two. The existing
(3.3)/(3.6) recognition applied to the nested quotient gives the displayed
ordinary core quotient isomorphisms for both original groups.

Source: Stellmacher (6.3), Journal of Algebra 190 (1997), p.31,
refs/latex/stellmacher-n-group.tex. Both original public quotient conclusions
are preserved; no faithful-action quotient replaces them.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

/-- **Stellmacher (6.3).** Each local two-core quotient is an ordinary
 dihedral group of order twice a power of three. -/
public theorem lemma_six_three
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ ≠ ⊥) :
    (∃ n1 : ℕ,
      Nonempty ((P1 ⧸ pCore 2 P1) ≃* DihedralGroup (3 ^ n1))) ∧
    (∃ n2 : ℕ,
      Nonempty ((P2 ⧸ pCore 2 P2) ≃* DihedralGroup (3 ^ n2))) := by
  obtain ⟨_hB, hA1, hA2⟩ := sixThree_native_quotients S0 S P1 P2 h hcomm
  obtain ⟨hsol1, _hchar1, hsol2, _hchar2⟩ := lemma_five_three S0 S P1 P2 h
  obtain ⟨_hSP1, T1, _hT1⟩ := h.fiveOne.P1_mem.1.2.1
  obtain ⟨_hSP2, T2, _hT2⟩ := h.fiveOne.P2_mem.1.2.1
  have hcore1 : pCore 2 P1 ≠ ⊥ := by
    intro hb
    apply h.fiveOne.P1_mem.1.2.2.1
    simp [twoCoreIn, hb]
  have hcore2 : pCore 2 P2 ≠ ⊥ := by
    intro hb
    apply h.fiveOne.P2_mem.1.2.2.1
    simp [twoCoreIn, hb]
  exact ⟨dihedral_three_power_core_quotient_of_nested hsol1 T1 hcore1 hA1,
    dihedral_three_power_core_quotient_of_nested hsol2 T2 hcore2 hA2⟩

end Stellmacher.SectionsFiveToSeven
