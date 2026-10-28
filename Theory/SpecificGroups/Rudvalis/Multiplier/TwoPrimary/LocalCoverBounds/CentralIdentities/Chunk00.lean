module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.CentralIdentities.Inputs

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

theorem eq_0 : Eqn alphabet [1, 2] [] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [1, 2] [] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [1, 2] [] ![0, 0, 0, 0, 0, 0, 0] ((show Eqn alphabet [1, 2] [] ![0, 0, 0, 0, 0, 0, 0] from by simp [Eqn, alphabet, readWord_cons, readWord_nil, collect])) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 2] [1, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 2]
  have hb : Eqn alphabet [] [] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet []
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_1 : Eqn alphabet [2, 1] [] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [2, 1] [] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [2, 1] [] ![0, 0, 0, 0, 0, 0, 0] ((show Eqn alphabet [2, 1] [] ![0, 0, 0, 0, 0, 0, 0] from by simp [Eqn, alphabet, readWord_cons, readWord_nil, collect])) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 1] [2, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 1]
  have hb : Eqn alphabet [] [] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet []
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_2 : Eqn alphabet [1] [2, 2] ![0, 1, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [1] [2, 2] ![0, 1, 0, 0, 0, 0, 0] :=
    eqn_cast [1] [2, 2] ![0, 1, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 1) [1] [2, 2] false 0 (sourceExponent 1) (by decide) (source_relation 1)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1] [1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1]
  have hb : Eqn alphabet [2, 2] [2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2]
  exact eqn_change ![0, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_3 : Eqn alphabet [2, 2] [1] ![0, (-1), 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, (-1), 0, 0, 0, 0, 0] (eqn_symm eq_2) (by decide)

theorem eq_4 : Eqn alphabet [1, 1] [2] ![0, 1, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [1, 1] [2] ![0, 1, 0, 0, 0, 0, 0] :=
    eqn_cast [1, 1] [2] ![0, 1, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 1) [1, 1] [2] false 0 (sourceExponent 1) (by decide) (source_relation 1)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1] [1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1]
  have hb : Eqn alphabet [2] [2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2]
  exact eqn_change ![0, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_5 : Eqn alphabet [0, 2, 0, 1, 0, 2, 0, 1] [2, 0, 1, 0, 2, 0, 1, 0] ![(-4), 0, 1, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 2, 0, 1] [2, 0, 1, 0, 2, 0, 1, 0] ![(-4), 0, 1, 0, 0, 0, 0] :=
    eqn_cast [0, 2, 0, 1, 0, 2, 0, 1] [2, 0, 1, 0, 2, 0, 1, 0] ![(-4), 0, 1, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 2) [0, 2, 0, 1, 0, 2, 0, 1] [2, 0, 1, 0, 2, 0, 1, 0] false 0 (sourceExponent 2) (by decide) (source_relation 2)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 2, 0, 1] [0, 2, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 2, 0, 1]
  have hb : Eqn alphabet [2, 0, 1, 0, 2, 0, 1, 0] [2, 0, 1, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 1, 0]
  exact eqn_change ![(-4), 0, 1, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_6 : Eqn alphabet [2, 0, 1, 0, 2, 0, 1, 0] [2, 0, 1, 0, 2, 0, 1, 0] ![(-8), 0, 2, 0, 0, 0, 0] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 0, 1, 0] [0, 2, 0, 1, 0, 2, 0, 1] ![(-4), 0, 1, 0, 0, 0, 0] :=
    eqn_cast [2, 0, 1, 0, 2, 0, 1, 0] [0, 2, 0, 1, 0, 2, 0, 1] ![(-4), 0, 1, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 2) [2, 0, 1, 0, 2, 0, 1, 0] [0, 2, 0, 1, 0, 2, 0, 1] false 1 (sourceExponent 2) (by decide) (source_relation 2)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 0, 1, 0] [2, 0, 1, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 1, 0]
  have hb : Eqn alphabet [0, 2, 0, 1, 0, 2, 0, 1] [2, 0, 1, 0, 2, 0, 1, 0] ![(-4), 0, 1, 0, 0, 0, 0] :=
    eqn_change ![(-4), 0, 1, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 2, 0, 1, 0, 2, 0, 1]) (eqn_cast [0, 2, 0, 1, 0, 2, 0, 1] [2, 0, 1, 0, 2, 0, 1, 0] ![(-4), 0, 1, 0, 0, 0, 0] (eqn_context [] [] eq_5) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![(-8), 0, 2, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_7 : Eqn alphabet [0, 1, 0, 2, 0, 1, 0, 2] [1, 0, 2, 0, 1, 0, 2, 0] ![(-4), 0, 1, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 1, 0, 2, 0, 1, 0, 2] [1, 0, 2, 0, 1, 0, 2, 0] ![(-4), 0, 1, 0, 0, 0, 0] :=
    eqn_cast [0, 1, 0, 2, 0, 1, 0, 2] [1, 0, 2, 0, 1, 0, 2, 0] ![(-4), 0, 1, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 2) [0, 1, 0, 2, 0, 1, 0, 2] [1, 0, 2, 0, 1, 0, 2, 0] false 2 (sourceExponent 2) (by decide) (source_relation 2)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 0, 1, 0, 2] [0, 1, 0, 2, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 1, 0, 2]
  have hb : Eqn alphabet [1, 0, 2, 0, 1, 0, 2, 0] [1, 0, 2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 1, 0, 2, 0]
  exact eqn_change ![(-4), 0, 1, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_8 : Eqn alphabet [1, 0, 2, 0, 1, 0, 2, 0] [0, 1, 0, 2, 0, 1, 0, 2] ![4, 0, (-1), 0, 0, 0, 0] := by
  exact eqn_change ![4, 0, (-1), 0, 0, 0, 0] (eqn_symm eq_7) (by decide)

theorem eq_9 : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] ![(-7), 0, 0, 1, 0, 0, 0] := by
  have h : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] ![(-7), 0, 0, 1, 0, 0, 0] :=
    eqn_cast [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] ![(-7), 0, 0, 1, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 3) [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] false 0 (sourceExponent 3) (by decide) (source_relation 3)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0]
  have hb : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
  exact eqn_change ![(-7), 0, 0, 1, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_10 : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0] ![7, 0, 0, (-1), 0, 0, 0] := by
  exact eqn_change ![7, 0, 0, (-1), 0, 0, 0] (eqn_symm eq_9) (by decide)

theorem eq_11 : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] ![(-7), 0, 0, 1, 0, 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] ![(-7), 0, 0, 1, 0, 0, 0] :=
    eqn_cast [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] ![(-7), 0, 0, 1, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 3) [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] false 1 (sourceExponent 3) (by decide) (source_relation 3)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2]
  have hb : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
  exact eqn_change ![(-7), 0, 0, 1, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_12 : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] ![7, 0, 0, (-1), 0, 0, 0] := by
  exact eqn_change ![7, 0, 0, (-1), 0, 0, 0] (eqn_symm eq_11) (by decide)

theorem eq_25 : Eqn alphabet [2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] ![(-13), 0, 0, 0, 1, 0, 0] := by
  have h : Eqn alphabet [2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] ![(-13), 0, 0, 0, 1, 0, 0] :=
    eqn_cast [2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] ![(-13), 0, 0, 0, 1, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 4) [2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] false 7 (sourceExponent 4) (by decide) (source_relation 4)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0] [2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0]
  have hb : Eqn alphabet [0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] [0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1]
  exact eqn_change ![(-13), 0, 0, 0, 1, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_26 : Eqn alphabet [0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0] ![13, 0, 0, 0, (-1), 0, 0] := by
  exact eqn_change ![13, 0, 0, 0, (-1), 0, 0] (eqn_symm eq_25) (by decide)

theorem eq_27 : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] ![(-13), 0, 0, 0, 1, 0, 0] := by
  have h : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] ![(-13), 0, 0, 0, 1, 0, 0] :=
    eqn_cast [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] ![(-13), 0, 0, 0, 1, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 4) [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] false 8 (sourceExponent 4) (by decide) (source_relation 4)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2] [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2]
  have hb : Eqn alphabet [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0]
  exact eqn_change ![(-13), 0, 0, 0, 1, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_28 : Eqn alphabet [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2] ![13, 0, 0, 0, (-1), 0, 0] := by
  exact eqn_change ![13, 0, 0, 0, (-1), 0, 0] (eqn_symm eq_27) (by decide)

theorem eq_53 : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0] [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![(-13), 0, 0, 0, 1, 0, 0] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0] [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![(-13), 0, 0, 0, 1, 0, 0] :=
    eqn_cast [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0] [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![(-13), 0, 0, 0, 1, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 4) [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0] [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] false 25 (sourceExponent 4) (by decide) (source_relation 4)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0] [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0]
  have hb : Eqn alphabet [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1]
  exact eqn_change ![(-13), 0, 0, 0, 1, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_54 : Eqn alphabet [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0] ![13, 0, 0, 0, (-1), 0, 0] := by
  exact eqn_change ![13, 0, 0, 0, (-1), 0, 0] (eqn_symm eq_53) (by decide)

theorem eq_55 : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![(-14), 0, 0, 0, 0, 1, 0] := by
  have h : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![(-14), 0, 0, 0, 0, 1, 0] :=
    eqn_cast [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![(-14), 0, 0, 0, 0, 1, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 5) [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] false 0 (sourceExponent 5) (by decide) (source_relation 5)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2]
  have hb : Eqn alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0]
  exact eqn_change ![(-14), 0, 0, 0, 0, 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_57 : Eqn alphabet [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0] ![(-14), 0, 0, 0, 0, 1, 0] := by
  have h : Eqn alphabet [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0] ![(-14), 0, 0, 0, 0, 1, 0] :=
    eqn_cast [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0] ![(-14), 0, 0, 0, 0, 1, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 5) [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0] false 2 (sourceExponent 5) (by decide) (source_relation 5)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1]
  have hb : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0] [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0]
  exact eqn_change ![(-14), 0, 0, 0, 0, 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_65 : Eqn alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2] ![(-13), 0, 0, 0, 0, 1, 0] := by
  have h : Eqn alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2] ![(-13), 0, 0, 0, 0, 1, 0] :=
    eqn_cast [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2] ![(-13), 0, 0, 0, 0, 1, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 5) [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2] false 9 (sourceExponent 5) (by decide) (source_relation 5)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0]
  have hb : Eqn alphabet [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2] [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2]
  exact eqn_change ![(-13), 0, 0, 0, 0, 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_66 : Eqn alphabet [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2] [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![13, 0, 0, 0, 0, (-1), 0] := by
  exact eqn_change ![13, 0, 0, 0, 0, (-1), 0] (eqn_symm eq_65) (by decide)

theorem eq_84 : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] ![(-16), 0, 0, 0, 0, 0, 1] := by
  have h : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] ![(-16), 0, 0, 0, 0, 0, 1] :=
    eqn_cast [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] ![(-16), 0, 0, 0, 0, 0, 1] (seed_eqn alphabet alphabet_inverse (sourceWord 6) [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] false 4 (sourceExponent 6) (by decide) (source_relation 6)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1]
  have hb : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0]
  exact eqn_change ![(-16), 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_101 : Eqn alphabet [2, 0, 1, 0, 2, 0, 1, 0, 2] [0, 2, 0, 1, 0, 2, 0] ![4, 0, (-1), 0, 0, 0, 0] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 0, 1, 0, 2] [0, 2, 0, 1, 0, 2, 0] ![4, 0, (-1), 0, 0, 0, 0] :=
    eqn_cast [2, 0, 1, 0, 2, 0, 1, 0, 2] [0, 2, 0, 1, 0, 2, 0] ![4, 0, (-1), 0, 0, 0, 0] (eqn_overlap_checked [0, 2, 0, 1, 0, 2, 0] [1] [2] [2, 0, 1, 0, 2, 0, 1, 0] [] [0, 2, 0, 1, 0, 2, 0, 1] [1, 2] (by decide) (by decide) eq_5 eq_0) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 0, 1, 0, 2] [2, 0, 1, 0, 2, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 1, 0, 2]
  have hb : Eqn alphabet [0, 2, 0, 1, 0, 2, 0] [0, 2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 2, 0]
  exact eqn_change ![4, 0, (-1), 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_102 : Eqn alphabet [2, 0, 1, 0, 2, 0, 1, 0, 1] [0, 2, 0, 1, 0, 2, 0, 2] ![4, 1, (-1), 0, 0, 0, 0] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 0, 1, 0, 1] [0, 2, 0, 1, 0, 2, 0, 2] ![4, 1, (-1), 0, 0, 0, 0] :=
    eqn_cast [2, 0, 1, 0, 2, 0, 1, 0, 1] [0, 2, 0, 1, 0, 2, 0, 2] ![4, 1, (-1), 0, 0, 0, 0] (eqn_overlap_checked [0, 2, 0, 1, 0, 2, 0] [1] [1] [2, 0, 1, 0, 2, 0, 1, 0] [2] [0, 2, 0, 1, 0, 2, 0, 1] [1, 1] (by decide) (by decide) eq_5 eq_4) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 0, 1, 0, 1] [2, 0, 1, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 1, 0, 1]
  have hb : Eqn alphabet [0, 2, 0, 1, 0, 2, 0, 2] [0, 2, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 2, 0, 2]
  exact eqn_change ![4, 1, (-1), 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_103 : Eqn alphabet [2, 0, 2, 0, 1, 0, 2, 0] [1, 0, 1, 0, 2, 0, 1, 0, 2] ![4, (-1), (-1), 0, 0, 0, 0] := by
  have h : Eqn alphabet [2, 0, 2, 0, 1, 0, 2, 0] [1, 0, 1, 0, 2, 0, 1, 0, 2] ![4, (-1), (-1), 0, 0, 0, 0] :=
    eqn_cast [2, 0, 2, 0, 1, 0, 2, 0] [1, 0, 1, 0, 2, 0, 1, 0, 2] ![4, (-1), (-1), 0, 0, 0, 0] (eqn_overlap_checked [1] [1] [0, 2, 0, 1, 0, 2, 0] [2] [0, 1, 0, 2, 0, 1, 0, 2] [1, 1] [1, 0, 2, 0, 1, 0, 2, 0] (by decide) (by decide) eq_4 eq_8) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 2, 0, 1, 0, 2, 0] [2, 0, 2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 1, 0, 2, 0]
  have hb : Eqn alphabet [1, 0, 1, 0, 2, 0, 1, 0, 2] [1, 0, 1, 0, 2, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 2, 0, 1, 0, 2]
  exact eqn_change ![4, (-1), (-1), 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_104 : Eqn alphabet [1, 0, 1, 0, 2, 0, 1, 0, 2] [2, 0, 2, 0, 1, 0, 2, 0] ![(-4), 1, 1, 0, 0, 0, 0] := by
  exact eqn_change ![(-4), 1, 1, 0, 0, 0, 0] (eqn_symm eq_103) (by decide)

theorem eq_105 : Eqn alphabet [0, 0, 1, 0, 2, 0, 1, 0, 2] [1, 0, 2, 0, 1, 0, 2] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 1, 0, 2, 0, 1, 0, 2, 0] [2, 2, 0, 2, 0, 1, 0, 2] ![5, 1, (-1), 0, 0, 0, 0] :=
    eqn_cast [0, 1, 0, 2, 0, 1, 0, 2, 0] [2, 2, 0, 2, 0, 1, 0, 2] ![5, 1, (-1), 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0] [0, 1, 0, 2, 0, 1, 0, 2, 0] [2, 2, 0, 2, 0, 1, 0, 2] false 10 ![8, 1, (-1), 0, 0, 0, 0] (by decide) (eqn_cast [2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0] [] ![8, 1, (-1), 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_102) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 0, 1, 0, 2, 0] [0, 0, 1, 0, 2, 0, 1, 0, 2] ![4, 0, (-1), 0, 0, 0, 0] :=
    eqn_change ![4, 0, (-1), 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 1, 0, 2, 0, 1, 0, 2, 0]) (eqn_cast [0, 1, 0, 2, 0, 1, 0, 2, 0] [0, 0, 1, 0, 2, 0, 1, 0, 2] ![4, 0, (-1), 0, 0, 0, 0] (eqn_context [0] [] eq_8) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 2] [1, 0, 2, 0, 1, 0, 2] ![0, (-1), 0, 0, 0, 0, 0] :=
    eqn_change ![0, (-1), 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [2, 2, 0, 2, 0, 1, 0, 2]) (eqn_cast [2, 2, 0, 2, 0, 1, 0, 2] [1, 0, 2, 0, 1, 0, 2] ![0, (-1), 0, 0, 0, 0, 0] (eqn_context [] [0, 2, 0, 1, 0, 2] eq_3) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_106 : Eqn alphabet [1, 0, 2, 0, 1, 0] [0, 0, 1, 0, 2, 0, 1, 0] ![(-1), 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [1, 0, 2, 0, 1, 0, 2, 1] [0, 0, 1, 0, 2, 0, 1, 0] ![(-1), 0, 0, 0, 0, 0, 0] :=
    eqn_cast [1, 0, 2, 0, 1, 0, 2, 1] [0, 0, 1, 0, 2, 0, 1, 0] ![(-1), 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [0, 0, 1, 0, 2, 0, 1, 0] [2] [1] [1, 0, 2, 0, 1, 0, 2] [] [0, 0, 1, 0, 2, 0, 1, 0, 2] [2, 1] (by decide) (by decide) eq_105 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 1, 0, 2, 1] [1, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [1, 0, 2, 0, 1, 0, 2, 1]) (eqn_cast [1, 0, 2, 0, 1, 0, 2, 1] [1, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [1, 0, 2, 0, 1, 0] [] eq_1) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [0, 0, 1, 0, 2, 0, 1, 0] [0, 0, 1, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 1, 0, 2, 0, 1, 0]
  exact eqn_change ![(-1), 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_107 : Eqn alphabet [0, 0, 1, 0, 2, 0, 1, 0] [1, 0, 2, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_symm eq_106) (by decide)

theorem eq_108 : Eqn alphabet [0, 0, 1, 0, 2, 0, 1] [1, 0, 2, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0, 1, 0, 2, 0, 1] [1, 0, 2, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0, 1, 0, 2, 0, 1] [1, 0, 2, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 0, 1, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 2] [0, 0, 1, 0, 2, 0, 1] [1, 0, 2, 0, 1, 0, 0] false 0 ![4, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 0, 1, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 2] [] ![4, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_107) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0, 1, 0, 2, 0, 1] [0, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0, 1, 0, 2, 0, 1]
  have hb : Eqn alphabet [1, 0, 2, 0, 1, 0, 0] [1, 0, 2, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 1, 0, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)


end Rudvalis.Multiplier.TwoPrimary.LocalPresentation.CentralKernel.IdentityReplay.Certificate
