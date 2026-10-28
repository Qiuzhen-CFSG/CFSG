module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.CentralIdentities.Chunk00

/-!
# Checked cyclic and power equations for the central presentation

The trace uses contextual rewriting, cyclic splitting, and powers of
previously proved equations. All word and exponent calculations are checked
by the kernel. No quotient finiteness or multiplier bound is assumed.

Source: the literal max4 relators in `LocalCoverBounds.Presentation`;
Aschbacher–Smith I.1.3(1), p.407.
See `CentralIdentities/source/README.md` for the reproducible certificate.
-/

@[expose] public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation.CentralKernel.IdentityReplay.Certificate

theorem eq_109 : Eqn alphabet [1, 0, 2, 0, 1, 0, 0] [0, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_symm eq_108) (by decide)

theorem eq_110 : Eqn alphabet [0, 2, 0, 1, 0, 0, 2] [2, 0, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 0, 2] [2, 0, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 2, 0, 1, 0, 0, 2] [2, 0, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 0, 1, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 2] [0, 2, 0, 1, 0, 0, 2] [2, 0, 0, 1, 0, 2, 0] false 3 ![4, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 0, 1, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 2] [] ![4, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_107) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 0, 2] [0, 2, 0, 1, 0, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 0, 2]
  have hb : Eqn alphabet [2, 0, 0, 1, 0, 2, 0] [2, 0, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 0, 1, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_117 : Eqn alphabet [0, 2, 0, 1, 0, 0] [2, 0, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 0] [2, 0, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 2, 0, 1, 0, 0] [2, 0, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [2] [1] [0, 2, 0, 1, 0, 0] [] [0, 0, 1, 0, 2, 0, 1] [2, 1] [1, 0, 2, 0, 1, 0, 0] (by decide) (by decide) eq_1 eq_109) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 0] [0, 2, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 0]
  have hb : Eqn alphabet [2, 0, 0, 1, 0, 2, 0, 1] [2, 0, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 0, 1, 0, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_118 : Eqn alphabet [2, 0, 0, 1, 0, 2, 0, 1] [0, 2, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_symm eq_117) (by decide)

theorem eq_119 : Eqn alphabet [0, 2, 0, 1, 0, 0, 0] [0, 2, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 0, 0] [2, 1, 0, 2, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 2, 0, 1, 0, 0, 0] [2, 1, 0, 2, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [2] [0, 0, 1, 0, 2, 0, 1] [0] [0, 2, 0, 1, 0, 0] [1, 0, 2, 0, 1, 0] [2, 0, 0, 1, 0, 2, 0, 1] [0, 0, 1, 0, 2, 0, 1, 0] (by decide) (by decide) eq_118 eq_107) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 0, 0] [0, 2, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 0, 0]
  have hb : Eqn alphabet [2, 1, 0, 2, 0, 1, 0] [0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [2, 1, 0, 2, 0, 1, 0]) (eqn_cast [2, 1, 0, 2, 0, 1, 0] [0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 2, 0, 1, 0] eq_1) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_122 : Eqn alphabet [0, 1, 0, 0, 0, 0] [1, 0, 0, 2, 0, 1] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 1, 0, 0, 0, 0] [1, 0, 0, 2, 0, 1] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 1, 0, 0, 0, 0] [1, 0, 0, 2, 0, 1] ![1, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 2, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0] [0, 1, 0, 0, 0, 0] [1, 0, 0, 2, 0, 1] false 2 ![4, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 2, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0] [] ![4, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_119) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 0, 0, 0] [0, 1, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 0, 0, 0]
  have hb : Eqn alphabet [1, 0, 0, 2, 0, 1] [1, 0, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 0, 2, 0, 1]
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_123 : Eqn alphabet [1, 0, 0, 2, 0, 1] [0, 1, 0, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![(-1), 0, 0, 0, 0, 0, 0] (eqn_symm eq_122) (by decide)

theorem eq_124 : Eqn alphabet [1, 0, 0, 0, 0, 2] [0, 1, 0, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [1, 0, 0, 0, 0, 2] [0, 1, 0, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [1, 0, 0, 0, 0, 2] [0, 1, 0, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 2, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0] [1, 0, 0, 0, 0, 2] [0, 1, 0, 0, 2, 0] false 3 ![4, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 2, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0] [] ![4, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_119) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 0, 0, 0, 2] [1, 0, 0, 0, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 0, 0, 0, 2]
  have hb : Eqn alphabet [0, 1, 0, 0, 2, 0] [0, 1, 0, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_125 : Eqn alphabet [0, 0, 0, 0, 2, 0] [2, 0, 1, 0, 0, 2] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 0, 0, 2, 0] [2, 0, 1, 0, 0, 2] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 0, 0, 2, 0] [2, 0, 1, 0, 0, 2] ![1, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 2, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0] [0, 0, 0, 0, 2, 0] [2, 0, 1, 0, 0, 2] false 4 ![4, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 2, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0] [] ![4, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_119) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 0, 0, 2, 0] [0, 0, 0, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 0, 0, 2, 0]
  have hb : Eqn alphabet [2, 0, 1, 0, 0, 2] [2, 0, 1, 0, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 0, 2]
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_127 : Eqn alphabet [0, 0, 1, 0, 0, 2, 0] [1, 0, 0, 2, 0] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 1, 0, 0, 0, 0, 2] [1, 0, 0, 2, 0] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 1, 0, 0, 0, 0, 2] [1, 0, 0, 2, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [1, 0, 0, 2, 0] [1] [2] [0, 1, 0, 0, 0, 0] [] [1, 0, 0, 2, 0, 1] [1, 2] (by decide) (by decide) eq_123 eq_0) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 0, 0, 0, 2] [0, 0, 1, 0, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 1, 0, 0, 0, 0, 2]) (eqn_cast [0, 1, 0, 0, 0, 0, 2] [0, 0, 1, 0, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [0] [] eq_124) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [1, 0, 0, 2, 0] [1, 0, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 0, 2, 0]
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_128 : Eqn alphabet [0, 0, 1, 0, 0, 2] [1, 0, 0, 2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 1, 0, 0, 2] [1, 0, 0, 2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 1, 0, 0, 2] [1, 0, 0, 2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2] [0, 0, 1, 0, 0, 2] [1, 0, 0, 2, 0, 0] false 0 ![4, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2] [] ![4, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_127) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 1, 0, 0, 2] [0, 0, 1, 0, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 1, 0, 0, 2]
  have hb : Eqn alphabet [1, 0, 0, 2, 0, 0] [1, 0, 0, 2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 0, 2, 0, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_129 : Eqn alphabet [1, 0, 0, 2, 0, 0] [0, 0, 1, 0, 0, 2] ![0, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_symm eq_128) (by decide)

theorem eq_130 : Eqn alphabet [0, 0, 2, 0, 0, 1] [2, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 2, 0, 0, 1] [2, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 2, 0, 0, 1] [2, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2] [0, 0, 2, 0, 0, 1] [2, 0, 0, 1, 0, 0] false 3 ![4, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2] [] ![4, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_127) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 2, 0, 0, 1] [0, 0, 2, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 2, 0, 0, 1]
  have hb : Eqn alphabet [2, 0, 0, 1, 0, 0] [2, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 0, 1, 0, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_133 : Eqn alphabet [0, 0, 1, 0, 0, 0, 0] [1, 0, 0, 0, 0] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 1, 0, 0, 2, 0, 1] [1, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 1, 0, 0, 2, 0, 1] [1, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [1, 0, 0, 0, 0] [2] [1] [0, 1, 0, 0, 2, 0] [] [1, 0, 0, 0, 0, 2] [2, 1] (by decide) (by decide) eq_124 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 0, 2, 0, 1] [0, 0, 1, 0, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] :=
    eqn_change ![(-1), 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 1, 0, 0, 2, 0, 1]) (eqn_cast [0, 1, 0, 0, 2, 0, 1] [0, 0, 1, 0, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] (eqn_context [0] [] eq_123) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [1, 0, 0, 0, 0] [1, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 0, 0, 0]
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_134 : Eqn alphabet [0, 0, 1, 0, 0, 0] [1, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 1, 0, 0, 0] [1, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 1, 0, 0, 0] [1, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2] [0, 0, 1, 0, 0, 0] [1, 0, 0, 0, 0, 0] false 0 ![5, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2] [] ![5, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_133) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 1, 0, 0, 0] [0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 1, 0, 0, 0]
  have hb : Eqn alphabet [1, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 0, 0, 0, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_135 : Eqn alphabet [1, 0, 0, 0, 0, 0] [0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_symm eq_134) (by decide)

theorem eq_136 : Eqn alphabet [0, 0, 0, 0, 0, 0] [2, 0, 0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 0, 0, 0, 0] [2, 0, 0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 0, 0, 0, 0] [2, 0, 0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2] [0, 0, 0, 0, 0, 0] [2, 0, 0, 1, 0, 0] false 3 ![5, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2] [] ![5, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_133) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 0, 0, 0, 0] [0, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 0, 0, 0, 0]
  have hb : Eqn alphabet [2, 0, 0, 1, 0, 0] [2, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 0, 1, 0, 0]
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_137 : Eqn alphabet [2, 0, 0, 1, 0, 0] [0, 2, 0, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 0, 0, 0, 0] [0, 2, 0, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 0, 0, 0, 0] [0, 2, 0, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2] [0, 0, 0, 0, 0, 0] [0, 2, 0, 0, 1, 0] false 4 ![5, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2] [] ![5, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_133) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 0, 0, 0, 0] [2, 0, 0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 0, 0, 0, 0, 0]) (eqn_cast [0, 0, 0, 0, 0, 0] [2, 0, 0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [] eq_136) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [0, 2, 0, 0, 1, 0] [0, 2, 0, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_138 : Eqn alphabet [0, 2, 0, 0, 1, 0] [2, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_symm eq_137) (by decide)

private theorem reduce_139_a_0 : Eqn alphabet [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] [0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 1, 0] ![3, 0, 0, 0, 0, 0, 0] :=
  eqn_change ![3, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0]) (eqn_cast [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] [2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] eq_138) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] [2, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [2, 0, 0, 1, 0] [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] eq_130) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] [2, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [2, 0, 0, 1] [0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] eq_138) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] [2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [2, 0, 0] [0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] eq_0) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] [2, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2, 0, 0] [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] eq_133) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] [2, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2] [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] eq_133) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] eq_1) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] [0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [0] [0, 1, 0, 0, 2, 0, 0, 1, 0] eq_125) (by decide) (by decide) (by decide))) (by decide)

private theorem reduce_139_a_1 : Eqn alphabet [0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 1, 0] [1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0] ![1, (-1), 0, 0, 0, 0, 0] :=
  eqn_change ![1, (-1), 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 1, 0]) (eqn_cast [0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 1, 0] [2, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 1, 0, 0, 2, 0, 0, 1, 0] eq_110) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] [2, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [2, 0, 0, 1] [0, 2, 0, 0, 1, 0] eq_138) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0] [2, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [2, 0, 0] [0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0] eq_0) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0] [2, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [2, 0, 0, 0, 0, 1, 0] [0] eq_130) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 0] [2, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [2, 0, 0, 0, 0, 1] [0, 0] eq_138) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0] [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [2, 0, 0, 0, 0] [0, 0, 1, 0, 0, 0, 0] eq_0) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] [2, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2] [1, 0, 0, 0, 0] eq_136) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0] [1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0] ![0, (-1), 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 1, 0, 0, 1, 0, 0, 0, 0] eq_3) (by decide) (by decide) (by decide))) (by decide)

private theorem reduce_139_a_2 : Eqn alphabet [1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0] [0, 0, 1, 0, 0, 2] ![2, 1, 0, 0, 0, 0, 0] :=
  eqn_change ![2, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0]) (eqn_cast [1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0] [1, 0, 0, 1, 1, 0, 0, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [1, 0, 0, 1] [] eq_133) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 0, 1, 1, 0, 0, 0, 0] [1, 0, 0, 2, 0, 0, 0, 0] ![0, 1, 0, 0, 0, 0, 0] (eqn_context [1, 0, 0] [0, 0, 0, 0] eq_4) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 0, 2, 0, 0, 0, 0] [0, 0, 1, 0, 0, 2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0] eq_129) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 1, 0, 0, 2, 0, 0] [1, 0, 0, 2, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [0] eq_127) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 0, 2, 0, 0] [0, 0, 1, 0, 0, 2] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [] eq_129) (by decide) (by decide) (by decide))) (by decide)

private theorem reduce_139_b_0 : Eqn alphabet [2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] [2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0] ![3, 0, 0, 0, 0, 0, 0] :=
  eqn_change ![3, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![3, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0]) (eqn_cast [2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] [2, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2] [0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] eq_127) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] eq_1) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] [2, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] eq_130) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] [2, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2] [2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] eq_133) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] eq_1) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] [2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 1, 0, 0, 2, 0, 0, 1, 0, 0] eq_125) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] [2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] (eqn_context [2, 0] [0, 0, 2, 0, 0, 1, 0, 0] eq_123) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0] [2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2] [0, 0, 2, 0, 0, 1, 0, 0] eq_133) (by decide) (by decide) (by decide))) (by decide)

private theorem reduce_139_b_1 : Eqn alphabet [2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0] [0, 0, 0, 0] ![3, 0, 0, 0, 0, 0, 0] :=
  eqn_change ![3, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![3, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0]) (eqn_cast [2, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0] [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0] eq_1) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0] [2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [2, 0, 0, 1, 0, 0] eq_136) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] [2, 1, 0, 0, 2, 0, 0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2] [0, 1, 0, 0] eq_127) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 1, 0, 0, 2, 0, 0, 1, 0, 0] [0, 0, 2, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 2, 0, 0, 1, 0, 0] eq_1) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 2, 0, 0, 1, 0, 0] [2, 0, 0, 1, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0] eq_130) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 1, 0, 0, 0, 0] [2, 1, 0, 0, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2] [] eq_133) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 1, 0, 0, 0, 0] [0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 0, 0] eq_1) (by decide) (by decide) (by decide))) (by decide)

theorem eq_139 : Eqn alphabet [0, 0, 1, 0, 0, 2] [0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] [2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] [2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_power eq_138 4) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0] [0, 0, 1, 0, 0, 2] ![6, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![6, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![4, (-1), 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![3, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0]) reduce_139_a_0) (by decide)) reduce_139_a_1) (by decide)) reduce_139_a_2) (by decide)
  have hb : Eqn alphabet [2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0] [0, 0, 0, 0] ![6, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![6, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![3, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0]) reduce_139_b_0) (by decide)) reduce_139_b_1) (by decide)
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_142 : Eqn alphabet [0, 1, 0, 0, 2] [0, 0, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 1, 0, 0, 2] [0, 0, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 1, 0, 0, 2] [0, 0, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 0, 1, 0, 0, 2, 0, 0, 0, 0] [0, 1, 0, 0, 2] [0, 0, 0, 0, 0] false 1 ![4, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 0, 1, 0, 0, 2, 0, 0, 0, 0] [] ![4, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_139) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 0, 2] [0, 1, 0, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 0, 2]
  have hb : Eqn alphabet [0, 0, 0, 0, 0] [0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 0, 0, 0]
  exact eqn_change ![(-1), 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_143 : Eqn alphabet [1, 0, 0, 2, 0] [0, 0, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [1, 0, 0, 2, 0] [0, 0, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] :=
    eqn_cast [1, 0, 0, 2, 0] [0, 0, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 0, 1, 0, 0, 2, 0, 0, 0, 0] [1, 0, 0, 2, 0] [0, 0, 0, 0, 0] false 2 ![4, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 0, 1, 0, 0, 2, 0, 0, 0, 0] [] ![4, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_139) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 0, 2, 0] [1, 0, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 0, 2, 0]
  have hb : Eqn alphabet [0, 0, 0, 0, 0] [0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 0, 0, 0]
  exact eqn_change ![(-1), 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_144 : Eqn alphabet [0, 0, 2, 0, 0] [2, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 2, 0, 0] [2, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 2, 0, 0] [2, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 0, 1, 0, 0, 2, 0, 0, 0, 0] [0, 0, 2, 0, 0] [2, 0, 0, 0, 0] false 3 ![4, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 0, 1, 0, 0, 2, 0, 0, 0, 0] [] ![4, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_139) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 2, 0, 0] [0, 0, 2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 2, 0, 0]
  have hb : Eqn alphabet [2, 0, 0, 0, 0] [2, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 0, 0, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_145 : Eqn alphabet [0, 0, 0, 0, 0, 1] [0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 0, 0, 0, 1] [0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 0, 0, 0, 1] [0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [0, 1, 0, 0] [2] [1] [0, 0, 0, 0, 0] [] [0, 1, 0, 0, 2] [2, 1] (by decide) (by decide) eq_142 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 0, 0, 0, 1] [0, 0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 0, 0, 0, 1]
  have hb : Eqn alphabet [0, 1, 0, 0] [0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 0]
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_146 : Eqn alphabet [0, 0, 2, 0] [2, 0, 0, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 2, 0] [2, 0, 0, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 2, 0] [2, 0, 0, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [2] [1] [0, 0, 2, 0] [] [0, 0, 0, 0, 0] [2, 1] [1, 0, 0, 2, 0] (by decide) (by decide) eq_1 eq_143) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 2, 0] [0, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 2, 0]
  have hb : Eqn alphabet [2, 0, 0, 0, 0, 0] [2, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 0, 0, 0, 0]
  exact eqn_change ![(-1), 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_147 : Eqn alphabet [2, 0, 0, 0, 0, 0] [0, 0, 2, 0] ![1, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_symm eq_146) (by decide)

theorem eq_148 : Eqn alphabet [0, 0, 2, 0, 1] [2, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 2, 0, 1] [2, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 2, 0, 1] [2, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [2] [0, 0, 0, 0, 0] [1] [0, 0, 2, 0] [0, 1, 0, 0] [2, 0, 0, 0, 0, 0] [0, 0, 0, 0, 0, 1] (by decide) (by decide) eq_147 eq_145) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 2, 0, 1] [0, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 2, 0, 1]
  have hb : Eqn alphabet [2, 0, 1, 0, 0] [2, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_149 : Eqn alphabet [0, 0, 0, 0, 0, 2] [0, 1, 0, 0, 1] ![1, (-1), 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 0, 0, 0, 2] [0, 1, 0, 0, 1] ![1, (-1), 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 0, 0, 0, 2] [0, 1, 0, 0, 1] ![1, (-1), 0, 0, 0, 0, 0] (eqn_overlap_checked [0, 1, 0, 0] [2] [2] [0, 0, 0, 0, 0] [1] [0, 1, 0, 0, 2] [2, 2] (by decide) (by decide) eq_142 eq_3) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 0, 0, 0, 2] [0, 0, 0, 0, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 0, 0, 0, 2]
  have hb : Eqn alphabet [0, 1, 0, 0, 1] [0, 1, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 0, 1]
  exact eqn_change ![1, (-1), 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_152 : Eqn alphabet [2, 0, 1, 0, 0, 1] [0, 0, 2, 0, 2] ![0, 1, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [2, 0, 1, 0, 0, 1] [0, 0, 2, 0, 2] ![0, 1, 0, 0, 0, 0, 0] :=
    eqn_cast [2, 0, 1, 0, 0, 1] [0, 0, 2, 0, 2] ![0, 1, 0, 0, 0, 0, 0] (eqn_overlap_checked [0, 0, 2, 0] [1] [1] [2, 0, 1, 0, 0] [2] [0, 0, 2, 0, 1] [1, 1] (by decide) (by decide) eq_148 eq_4) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 0, 1] [2, 0, 1, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 0, 1]
  have hb : Eqn alphabet [0, 0, 2, 0, 2] [0, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 2, 0, 2]
  exact eqn_change ![0, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_153 : Eqn alphabet [0, 0, 2, 0] [2, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 2, 0, 0, 0] [1, 1, 0, 0, 0] ![1, (-1), 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 2, 0, 0, 0] [1, 1, 0, 0, 0] ![1, (-1), 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0] [0, 0, 2, 0, 0, 0] [1, 1, 0, 0, 0] false 7 ![4, (-1), 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0] [] ![4, (-1), 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_149) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 2, 0, 0, 0] [0, 0, 2, 0] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 0, 2, 0, 0, 0]) (eqn_cast [0, 0, 2, 0, 0, 0] [2, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0] eq_144) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 0, 0, 0] [0, 0, 2, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [] eq_147) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [1, 1, 0, 0, 0] [2, 0, 0, 0] ![0, 1, 0, 0, 0, 0, 0] :=
    eqn_change ![0, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [1, 1, 0, 0, 0]) (eqn_cast [1, 1, 0, 0, 0] [2, 0, 0, 0] ![0, 1, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 0] eq_4) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_154 : Eqn alphabet [0, 0, 0, 0] [1, 0, 0, 2] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 0, 0] [1, 0, 0, 2] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 0, 0] [1, 0, 0, 2] ![1, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 0, 2, 0, 0, 0, 0, 1] [0, 0, 0, 0] [1, 0, 0, 2] false 3 ![3, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 0, 2, 0, 0, 0, 0, 1] [] ![3, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_153) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 0, 0] [0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 0, 0]
  have hb : Eqn alphabet [1, 0, 0, 2] [1, 0, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 0, 2]
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_155 : Eqn alphabet [1, 0, 0, 2] [0, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![(-1), 0, 0, 0, 0, 0, 0] (eqn_symm eq_154) (by decide)


end Rudvalis.Multiplier.TwoPrimary.LocalPresentation.CentralKernel.IdentityReplay.Certificate
