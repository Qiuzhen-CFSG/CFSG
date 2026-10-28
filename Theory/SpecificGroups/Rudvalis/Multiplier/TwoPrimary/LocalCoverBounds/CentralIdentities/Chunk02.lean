module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.CentralIdentities.Chunk01

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

theorem eq_156 : Eqn alphabet [0, 0, 0, 1] [0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 0, 1] [0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 0, 1] [0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 0, 2, 0, 0, 0, 0, 1] [0, 0, 0, 1] [0, 1, 0, 0] false 4 ![3, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 0, 2, 0, 0, 0, 0, 1] [] ![3, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_153) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 0, 1] [0, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 0, 1]
  have hb : Eqn alphabet [0, 1, 0, 0] [0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_157 : Eqn alphabet [0, 1, 0, 0] [0, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_symm eq_156) (by decide)

theorem eq_158 : Eqn alphabet [0, 0, 0, 0, 1] [1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 0, 0, 1] [1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 0, 0, 1] [1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [1, 0, 0] [2] [1] [0, 0, 0, 0] [] [1, 0, 0, 2] [2, 1] (by decide) (by decide) eq_155 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 0, 0, 1] [0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 0, 0, 1]
  have hb : Eqn alphabet [1, 0, 0] [1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 0]
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

private theorem reduce_159_a_0 : Eqn alphabet [0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] [2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] ![4, 1, 0, 0, 0, 0, 0] :=
  eqn_change ![4, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![4, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![3, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![3, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]) (eqn_cast [0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] eq_158) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] eq_135) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [0] [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] eq_157) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] eq_158) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] [1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [1] [0, 0, 0, 0, 1, 0, 0, 0, 0, 1] eq_158) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] ![0, 1, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] eq_4) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 1, 0, 0, 0, 0, 1] eq_147) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1] [2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 1, 0, 0, 0, 0, 1] eq_153) (by decide) (by decide) (by decide))) (by decide)

private theorem reduce_159_a_1 : Eqn alphabet [2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] [0, 0, 1] ![3, 0, 0, 0, 0, 0, 0] :=
  eqn_change ![3, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![3, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]) (eqn_cast [2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] [2, 1, 0, 0, 0, 0, 0, 0, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2] [0, 0, 0, 0, 1] eq_158) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 1, 0, 0, 0, 0, 0, 0, 1] [0, 0, 0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 0, 0, 0, 0, 1] eq_1) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 0, 0, 0, 0, 1] [2, 0, 0, 1, 0, 0, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [1] eq_136) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 1, 0, 0, 1] [2, 0, 0, 0, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [2, 0] [1] eq_157) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 0, 0, 1, 1] [2, 1, 0, 0, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2] [1] eq_158) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 1, 0, 0, 1] [0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 1] eq_1) (by decide) (by decide) (by decide))) (by decide)

theorem eq_159 : Eqn alphabet [0, 0, 1] [1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] [1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0] ![4, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] [1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0] ![4, 0, 0, 0, 0, 0, 0] (eqn_power eq_158 4) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] [0, 0, 1] ![7, 1, 0, 0, 0, 0, 0] :=
    eqn_change ![7, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![4, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]) reduce_159_a_0) (by decide)) reduce_159_a_1) (by decide)
  have hb : Eqn alphabet [1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0] [1, 0, 0] ![3, 1, 0, 0, 0, 0, 0] :=
    eqn_change ![3, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0]) (eqn_cast [1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0] [1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [1, 0] [1, 0, 0, 1, 0, 0] eq_157) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0] [1, 1, 0, 0, 1, 0, 0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [1] [1, 0, 0, 1, 0, 0] eq_158) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 1, 0, 0, 1, 0, 0, 1, 0, 0] [2, 0, 0, 1, 0, 0, 1, 0, 0] ![0, 1, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 1, 0, 0, 1, 0, 0] eq_4) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 1, 0, 0, 1, 0, 0] [2, 0, 0, 0, 0, 1, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [2, 0] [1, 0, 0] eq_157) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 0, 0, 1, 1, 0, 0] [2, 1, 0, 0, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2] [1, 0, 0] eq_158) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 1, 0, 0, 1, 0, 0] [0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 1, 0, 0] eq_1) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 1, 0, 0] [0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [0] [] eq_157) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 0, 0, 1] [1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [] eq_158) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_160 : Eqn alphabet [1, 0, 0] [0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_symm eq_159) (by decide)

theorem eq_161 : Eqn alphabet [0, 0, 2] [2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 2] [2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 2] [2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [1, 0, 0, 2, 0, 0] [0, 0, 2] [2, 0, 0] false 1 ![2, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [1, 0, 0, 2, 0, 0] [] ![2, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_160) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 2] [0, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 2]
  have hb : Eqn alphabet [2, 0, 0] [2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_162 : Eqn alphabet [0, 0] [2, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0] [2, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0] [2, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [2] [1] [0, 0] [] [0, 0, 1] [2, 1] [1, 0, 0] (by decide) (by decide) eq_1 eq_160) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0] [0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0]
  have hb : Eqn alphabet [2, 0, 0, 1] [2, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_163 : Eqn alphabet [2, 0, 0, 1] [0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_symm eq_162) (by decide)

theorem eq_164 : Eqn alphabet [0, 0, 0, 0] [0, 0] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [1, 0, 0, 1, 0, 0, 1, 0, 0] [0, 0, 1, 0, 0, 1, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [1, 0, 0, 1, 0, 0, 1, 0, 0] [0, 0, 1, 0, 0, 1, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_power eq_160 3) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 0, 1, 0, 0, 1, 0, 0] [0, 0, 0, 0] ![1, 1, 0, 0, 0, 0, 0] :=
    eqn_change ![1, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [1, 0, 0, 1, 0, 0, 1, 0, 0]) (eqn_cast [1, 0, 0, 1, 0, 0, 1, 0, 0] [0, 0, 1, 1, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [1, 0, 0, 1, 0, 0] eq_160) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 1, 1, 0, 0, 1, 0, 0] [0, 0, 2, 0, 0, 1, 0, 0] ![0, 1, 0, 0, 0, 0, 0] (eqn_context [0, 0] [0, 0, 1, 0, 0] eq_4) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 2, 0, 0, 1, 0, 0] [2, 0, 0, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 1, 0, 0] eq_161) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 0, 0, 1, 0, 0] [2, 1, 0, 0, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2] [0, 0] eq_158) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 1, 0, 0, 0, 0] [0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 0, 0] eq_1) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [0, 0, 1, 0, 0, 1, 0, 0, 1] [0, 0] ![2, 1, 0, 0, 0, 0, 0] :=
    eqn_change ![2, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![2, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 0, 1, 0, 0, 1, 0, 0, 1]) (eqn_cast [0, 0, 1, 0, 0, 1, 0, 0, 1] [0, 0, 0, 0, 1, 1, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [0, 0] [1, 0, 0, 1] eq_160) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 0, 0, 1, 1, 0, 0, 1] [1, 0, 0, 1, 0, 0, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [1, 0, 0, 1] eq_158) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 0, 1, 0, 0, 1] [0, 0, 1, 1, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [1, 0, 0, 1] eq_160) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 1, 1, 0, 0, 1] [0, 0, 2, 0, 0, 1] ![0, 1, 0, 0, 0, 0, 0] (eqn_context [0, 0] [0, 0, 1] eq_4) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 2, 0, 0, 1] [2, 0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0, 1] eq_161) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 0, 0, 0, 1] [2, 1, 0, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2] [] eq_158) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 1, 0, 0] [0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 0] eq_1) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_165 : Eqn alphabet [0, 0, 1, 0, 2] [1, 0, 2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 1, 0, 2] [1, 0, 2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 1, 0, 2] [1, 0, 2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [1, 0] [0] [0, 2] [0, 0, 1] [2, 0, 0] [1, 0, 0] [0, 0, 2] (by decide) (by decide) eq_160 eq_161) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 1, 0, 2] [0, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 1, 0, 2]
  have hb : Eqn alphabet [1, 0, 2, 0, 0] [1, 0, 2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_166 : Eqn alphabet [1, 0, 2, 0, 0] [0, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_symm eq_165) (by decide)

theorem eq_167 : Eqn alphabet [2, 0, 0, 0, 1, 0] [2, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 2, 0, 1, 0] [2, 0, 2, 2, 0] ![1, 1, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 2, 0, 1, 0] [2, 0, 2, 2, 0] ![1, 1, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [2, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0] [0, 0, 2, 0, 1, 0] [2, 0, 2, 2, 0] false 9 ![3, 1, 0, 0, 0, 0, 0] (by decide) (eqn_cast [2, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0] [] ![3, 1, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_152) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 2, 0, 1, 0] [2, 0, 0, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 0, 2, 0, 1, 0]) (eqn_cast [0, 0, 2, 0, 1, 0] [2, 0, 0, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 1, 0] eq_161) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [2, 0, 2, 2, 0] [2, 0, 1, 0] ![0, (-1), 0, 0, 0, 0, 0] :=
    eqn_change ![0, (-1), 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [2, 0, 2, 2, 0]) (eqn_cast [2, 0, 2, 2, 0] [2, 0, 1, 0] ![0, (-1), 0, 0, 0, 0, 0] (eqn_context [2, 0] [0] eq_3) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_168 : Eqn alphabet [0, 0, 0, 1, 0] [0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 0, 1, 0] [1, 2, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 0, 1, 0] [1, 2, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [1] [2] [0, 0, 0, 1, 0] [] [2, 0, 1, 0] [1, 2] [2, 0, 0, 0, 1, 0] (by decide) (by decide) eq_0 eq_167) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 0, 1, 0] [0, 0, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 0, 1, 0]
  have hb : Eqn alphabet [1, 2, 0, 1, 0] [0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [1, 2, 0, 1, 0]) (eqn_cast [1, 2, 0, 1, 0] [0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 1, 0] eq_0) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_169 : Eqn alphabet [0, 2, 0] [0, 2, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 1, 2] [0, 2, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 2, 0, 1, 2] [0, 2, 0, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [2, 0, 0, 0, 1, 0, 0, 2, 0, 1] [0, 2, 0, 1, 2] [0, 2, 0, 0, 0] false 6 ![3, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [2, 0, 0, 0, 1, 0, 0, 2, 0, 1] [] ![3, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_167) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 2] [0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 2, 0, 1, 2]) (eqn_cast [0, 2, 0, 1, 2] [0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [0, 2, 0] [] eq_0) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [0, 2, 0, 0, 0] [0, 2, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 0, 0]
  exact eqn_change ![(-1), 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_170 : Eqn alphabet [0, 2, 0, 0, 0] [0, 2, 0] ![1, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_symm eq_169) (by decide)

theorem eq_171 : Eqn alphabet [0, 0, 1, 0, 1, 0] [1, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 1, 0, 1, 0] [1, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 1, 0, 1, 0] [1, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [1] [0, 0] [0, 1, 0] [0, 0, 1] [0, 1, 0] [1, 0, 0] [0, 0, 0, 1, 0] (by decide) (by decide) eq_160 eq_168) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 1, 0, 1, 0] [0, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 1, 0, 1, 0]
  have hb : Eqn alphabet [1, 0, 1, 0] [1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0]
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_172 : Eqn alphabet [0, 2, 0, 2] [0, 2, 0, 2, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 2] [0, 2, 0, 2, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 2, 0, 2] [0, 2, 0, 2, 0, 0] ![(-1), 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [0, 2, 0] [0, 0] [2] [0, 2, 0] [2, 0, 0] [0, 2, 0, 0, 0] [0, 0, 2] (by decide) (by decide) eq_170 eq_161) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2] [0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2]
  have hb : Eqn alphabet [0, 2, 0, 2, 0, 0] [0, 2, 0, 2, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 0]
  exact eqn_change ![(-1), 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_173 : Eqn alphabet [0, 2, 0, 2, 0, 0] [0, 2, 0, 2] ![1, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_symm eq_172) (by decide)

theorem eq_174 : Eqn alphabet [0, 0, 1, 0, 2, 0] [1, 0, 2, 0] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 1, 0, 2, 0] [1, 0, 2, 0] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 1, 0, 2, 0] [1, 0, 2, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [1] [0, 2, 0, 0] [0] [0, 0, 1, 0, 2] [0, 2, 0] [1, 0, 2, 0, 0] [0, 2, 0, 0, 0] (by decide) (by decide) eq_166 eq_170) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 1, 0, 2, 0] [0, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 1, 0, 2, 0]
  have hb : Eqn alphabet [1, 0, 2, 0] [1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0]
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_175 : Eqn alphabet [1, 0, 1, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 2, 0, 2] ![4, 2, (-1), 0, 0, 0, 0] := by
  have h : Eqn alphabet [1, 0, 1, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 2, 0, 2] ![4, 2, (-1), 0, 0, 0, 0] :=
    eqn_cast [1, 0, 1, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 2, 0, 2] ![4, 2, (-1), 0, 0, 0, 0] (eqn_overlap_checked [2] [2] [0, 1, 0, 2, 0, 1, 0, 1] [1] [0, 2, 0, 1, 0, 2, 0, 2] [2, 2] [2, 0, 1, 0, 2, 0, 1, 0, 1] (by decide) (by decide) eq_3 eq_102) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 0, 2, 0, 1, 0, 1] [1, 0, 1, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 2, 0, 1, 0, 1]
  have hb : Eqn alphabet [2, 0, 2, 0, 1, 0, 2, 0, 2] [2, 0, 2, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 1, 0, 2, 0, 2]
  exact eqn_change ![4, 2, (-1), 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_176 : Eqn alphabet [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2] [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0] ![(-8), 0, 2, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2] [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0] ![(-8), 0, 2, 0, 0, 0, 0] :=
    eqn_cast [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2] [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0] ![(-8), 0, 2, 0, 0, 0, 0] (eqn_overlap_checked [2, 0, 1, 0, 2, 0] [1, 0, 1] [0, 2, 0, 1, 0, 2] [0, 2, 0, 1, 0, 2, 0, 2] [2, 0, 2, 0, 1, 0, 2, 0] [2, 0, 1, 0, 2, 0, 1, 0, 1] [1, 0, 1, 0, 2, 0, 1, 0, 2] (by decide) (by decide) eq_102 eq_104) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2] [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2]
  have hb : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0] [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0]
  exact eqn_change ![(-8), 0, 2, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_177 : Eqn alphabet [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0] ![(-8), 0, 2, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0] ![(-8), 0, 2, 0, 0, 0, 0] :=
    eqn_cast [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0] ![(-8), 0, 2, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0] false 14 ![(-1), 0, 2, 0, 0, 0, 0] (by decide) (eqn_cast [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [] ![(-1), 0, 2, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_176) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1]
  have hb : Eqn alphabet [1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0] [1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0]
  exact eqn_change ![(-8), 0, 2, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_178 : Eqn alphabet [1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0] [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![8, 0, (-2), 0, 0, 0, 0] := by
  exact eqn_change ![8, 0, (-2), 0, 0, 0, 0] (eqn_symm eq_177) (by decide)

theorem eq_179 : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] ![(-7), 0, 0, 1, 0, 0, 0] := by
  have h : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] ![(-7), 0, 0, 1, 0, 0, 0] :=
    eqn_cast [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] ![(-7), 0, 0, 1, 0, 0, 0] (eqn_overlap_checked [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [1] [2] [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] [] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] [1, 2] (by decide) (by decide) eq_10 eq_0) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2]
  have hb : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
  exact eqn_change ![(-7), 0, 0, 1, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_182 : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] ![(-7), 1, 0, 1, 0, 0, 0] := by
  have h : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] ![(-7), 1, 0, 1, 0, 0, 0] :=
    eqn_cast [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] ![(-7), 1, 0, 1, 0, 0, 0] (eqn_overlap_checked [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [1] [1] [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] [2] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] [1, 1] (by decide) (by decide) eq_10 eq_4) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1] [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1]
  have hb : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2]
  exact eqn_change ![(-7), 1, 0, 1, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_183 : Eqn alphabet [2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] ![7, (-1), 0, (-1), 0, 0, 0] := by
  have h : Eqn alphabet [2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] ![7, (-1), 0, (-1), 0, 0, 0] :=
    eqn_cast [2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] ![7, (-1), 0, (-1), 0, 0, 0] (eqn_overlap_checked [1] [1] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [2] [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [1, 1] [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] (by decide) (by decide) eq_4 eq_12) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
  have hb : Eqn alphabet [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2]
  exact eqn_change ![7, (-1), 0, (-1), 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_184 : Eqn alphabet [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] ![(-7), 1, 0, 1, 0, 0, 0] := by
  exact eqn_change ![(-7), 1, 0, 1, 0, 0, 0] (eqn_symm eq_183) (by decide)

theorem eq_185 : Eqn alphabet [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2] ![0, 1, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2] ![0, 1, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2] ![0, 1, 0, 0, 0, 0, 0] (eqn_overlap_checked [2, 0, 1, 0, 2, 0] [1, 0, 1] [0, 2, 0, 1, 0, 1] [0, 2, 0, 1, 0, 2, 0, 2] [2, 0, 2, 0, 1, 0, 2, 0, 2] [2, 0, 1, 0, 2, 0, 1, 0, 1] [1, 0, 1, 0, 2, 0, 1, 0, 1] (by decide) (by decide) eq_102 eq_175) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1]
  have hb : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2] [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2]
  exact eqn_change ![0, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_186 : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2] [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] ![0, (-1), 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, (-1), 0, 0, 0, 0, 0] (eqn_symm eq_185) (by decide)

theorem eq_187 : Eqn alphabet [2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [1, 0, 1, 0, 2, 0] [1, 0, 1] [0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 2, 0, 2] [2, 0, 2, 0, 1, 0, 2, 0, 2] [1, 0, 1, 0, 2, 0, 1, 0, 1] [1, 0, 1, 0, 2, 0, 1, 0, 1] (by decide) (by decide) eq_175 eq_175) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1]
  have hb : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2] [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_188 : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2] [2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_symm eq_187) (by decide)

theorem eq_189 : Eqn alphabet [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] ![(-7), 2, 0, 1, 0, 0, 0] := by
  have h : Eqn alphabet [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] ![(-7), 2, 0, 1, 0, 0, 0] :=
    eqn_cast [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] ![(-7), 2, 0, 1, 0, 0, 0] (eqn_overlap_checked [2] [2] [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1] [1] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] [2, 2] [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1] (by decide) (by decide) eq_3 eq_182) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1] [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1]
  have hb : Eqn alphabet [2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] [2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2]
  exact eqn_change ![(-7), 2, 0, 1, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)


end Rudvalis.Multiplier.TwoPrimary.LocalPresentation.CentralKernel.IdentityReplay.Certificate
