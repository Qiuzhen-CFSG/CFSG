module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.PowerIdentities.PowerChunk01

/-!
# Checked cyclic and power equations for the central presentation

The trace uses contextual rewriting, cyclic splitting, and powers of
previously proved equations. All word and exponent calculations are checked
by the kernel. No quotient finiteness or multiplier bound is assumed.

Source: Wilson–Nickerson–Bray, ATLAS `S62G1-P1.M`.
See `PowerIdentities/source/README.md` for the reproducible certificate.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay.PowerCertificate

theorem eq_102 : Eqn alphabet [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0] [1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 2] ![(-4), 0, 1, 0, 0, (-1), 0] := by
  have h : Eqn alphabet [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0] [1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 2] ![(-4), 0, 1, 0, 0, (-1), 0] :=
    eqn_cast [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0] [1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 2] ![(-4), 0, 1, 0, 0, (-1), 0] (eqn_overlap_checked [1, 0, 2] [0, 1, 0] [1, 0, 1, 0, 1, 0] [0, 1, 0, 2, 0, 1] [2, 0, 2, 0, 2, 0, 2, 0, 2] [1, 0, 2, 0, 1, 0] [0, 1, 0, 1, 0, 1, 0, 1, 0] (by decide) (by decide) eq_6 eq_15) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0] [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0]
  have hb : Eqn alphabet [1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 2] [1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 2]
  exact eqn_change ![(-4), 0, 1, 0, 0, (-1), 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_103 : Eqn alphabet [1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 2] [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0] ![4, 0, (-1), 0, 0, 1, 0] := by
  exact eqn_change ![4, 0, (-1), 0, 0, 1, 0] (eqn_symm eq_102) (by decide)

theorem eq_106 : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, (-1)] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, (-1)] :=
    eqn_cast [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, (-1)] (eqn_overlap_checked [2, 0, 1, 0] [2, 0, 1] [1, 0, 2, 0, 2, 0, 1] [0, 2, 0, 1, 0] [1, 0, 2, 0, 2, 0, 1, 0] [2, 0, 1, 0, 2, 0, 1] [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] (by decide) (by decide) eq_12 eq_60) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1]
  have hb : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_108 : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0] [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1] ![5, 0, (-1), 0, 0, 1, 0] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0] [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1] ![5, 0, (-1), 0, 0, 1, 0] :=
    eqn_cast [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0] [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1] ![5, 0, (-1), 0, 0, 1, 0] (seed_eqn alphabet alphabet_inverse [1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0] [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0] [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1] false 10 ![10, 0, (-1), 0, 0, 1, 0] (by decide) (eqn_cast [1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0] [] ![10, 0, (-1), 0, 0, 1, 0] (eqn_relator alphabet_inverse eq_103) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0] [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0]
  have hb : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1] [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1]
  exact eqn_change ![5, 0, (-1), 0, 0, 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_109 : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1] [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0] ![(-5), 0, 1, 0, 0, (-1), 0] := by
  exact eqn_change ![(-5), 0, 1, 0, 0, (-1), 0] (eqn_symm eq_108) (by decide)

theorem eq_112 : Eqn alphabet [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2] [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] ![4, 0, (-1), 0, 0, 1, 0] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2] [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] ![4, 0, (-1), 0, 0, 1, 0] :=
    eqn_cast [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2] [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] ![4, 0, (-1), 0, 0, 1, 0] (seed_eqn alphabet alphabet_inverse [1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0] [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2] [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] false 22 ![10, 0, (-1), 0, 0, 1, 0] (by decide) (eqn_cast [1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0] [] ![10, 0, (-1), 0, 0, 1, 0] (eqn_relator alphabet_inverse eq_103) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2] [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2]
  have hb : Eqn alphabet [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]
  exact eqn_change ![4, 0, (-1), 0, 0, 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_113 : Eqn alphabet [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2] ![(-4), 0, 1, 0, 0, (-1), 0] := by
  exact eqn_change ![(-4), 0, 1, 0, 0, (-1), 0] (eqn_symm eq_112) (by decide)

theorem eq_120 : Eqn alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1] [1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 0] := by
  have h : Eqn alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1] [1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 0] :=
    eqn_cast [2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1] [1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 0] (eqn_overlap_checked [1, 0, 2] [2, 0, 1] [0, 2, 0, 2, 0, 1, 1] [2, 0, 1, 1, 0, 2] [0, 2, 0, 2, 0, 1, 1, 0] [1, 0, 2, 2, 0, 1] [2, 0, 1, 0, 2, 0, 2, 0, 1, 1] (by decide) (by decide) eq_10 eq_63) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1] [2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1]
  have hb : Eqn alphabet [1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0] [1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_121 : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 2, (-1)] := by
  have h : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 2, (-1)] :=
    eqn_cast [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 2, (-1)] (eqn_overlap_checked [0] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] (by decide) (by decide) eq_106 eq_83) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1]
  have hb : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_124 : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] [2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 2, (-1)] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] [2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 2, (-1)] :=
    eqn_cast [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] [2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 2, (-1)] (seed_eqn alphabet alphabet_inverse [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0] [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] [2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] false 5 ![6, 0, 0, 0, 0, 2, (-1)] (by decide) (eqn_cast [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0] [] ![6, 0, 0, 0, 0, 2, (-1)] (eqn_relator alphabet_inverse eq_121) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2]
  have hb : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] [2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_125 : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2] [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0] ![5, 0, (-1), 0, 0, 1, 0] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2] [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0] ![5, 0, (-1), 0, 0, 1, 0] :=
    eqn_cast [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2] [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0] ![5, 0, (-1), 0, 0, 1, 0] (eqn_overlap_checked [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0] [1] [2] [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0] [] [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1] [1, 2] (by decide) (by decide) eq_109 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2] [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2]
  have hb : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0] [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0]
  exact eqn_change ![5, 0, (-1), 0, 0, 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_128 : Eqn alphabet [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0] [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1] ![5, 0, (-1), 0, 0, 1, 0] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0] [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1] ![5, 0, (-1), 0, 0, 1, 0] :=
    eqn_cast [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0] [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1] ![5, 0, (-1), 0, 0, 1, 0] (eqn_overlap_checked [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1] [0] [0] [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2] [] [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] [0, 0] (by decide) (by decide) eq_113 eq_0) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0] [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0]
  have hb : Eqn alphabet [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1] [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1]
  exact eqn_change ![5, 0, (-1), 0, 0, 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_129 : Eqn alphabet [0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![0, (-1), 0, 0, 0, 1, 1] := by
  have h : Eqn alphabet [0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![0, (-1), 0, 0, 0, 1, 1] :=
    eqn_cast [0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![0, (-1), 0, 0, 0, 1, 1] (eqn_overlap_checked [2, 2, 0, 1, 1, 0, 1] [1] [0, 2, 0, 1, 0] [0, 2, 2, 0, 2, 2, 2] [0, 1, 0, 2, 0, 1] [2, 2, 0, 1, 1, 0, 1, 1] [1, 0, 2, 0, 1, 0] (by decide) (by decide) eq_37 eq_6) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] [0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0]
  have hb : Eqn alphabet [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1] [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1]
  exact eqn_change ![0, (-1), 0, 0, 0, 1, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_130 : Eqn alphabet [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1] [0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 1, 0, 0, 0, (-1), (-1)] := by
  exact eqn_change ![0, 1, 0, 0, 0, (-1), (-1)] (eqn_symm eq_129) (by decide)

theorem eq_140 : Eqn alphabet [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, 0, 0] :=
    eqn_cast [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, 0, 0] (eqn_overlap_checked [0, 2] [2, 0, 1, 0, 1, 0, 2] [2, 0, 2, 2] [2, 2, 0, 1, 0, 1, 0, 2, 0] [0, 2, 0, 1, 0, 1, 0, 1, 1, 1] [0, 2, 2, 0, 1, 0, 1, 0, 2] [2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 2] (by decide) (by decide) eq_55 eq_72) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2]
  have hb : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 1] [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 1]
  exact eqn_change ![0, (-1), 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_155 : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, (-1), 1, 0] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, (-1), 1, 0] :=
    eqn_cast [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, (-1), 1, 0] (eqn_overlap_checked [1, 0, 1, 0, 2, 0, 2] [0, 2, 0, 1, 0] [2] [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2] [2, 0, 1, 0, 2, 0] [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] [0, 2, 0, 1, 0, 2] (by decide) (by decide) eq_22 eq_5) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2]
  have hb : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0] [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, (-1), 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_156 : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0] [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 1, (-1), 0] := by
  exact eqn_change ![0, 0, 0, 0, 1, (-1), 0] (eqn_symm eq_155) (by decide)

theorem eq_157 : Eqn alphabet [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 2, 0, 0, 0, 0, (-2)] := by
  have h : Eqn alphabet [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 2, 0, 0, 0, 0, (-2)] :=
    eqn_cast [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 2, 0, 0, 0, 0, (-2)] (eqn_overlap_checked [1, 0, 2, 2, 0, 2] [2, 2] [0, 1, 1, 0, 1, 1] [2, 0, 1, 1, 0, 1, 1] [0, 2, 2, 0, 2, 2, 2] [1, 0, 2, 2, 0, 2, 2, 2] [2, 2, 0, 1, 1, 0, 1, 1] (by decide) (by decide) eq_44 eq_37) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]
  have hb : Eqn alphabet [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2]
  exact eqn_change ![0, 2, 0, 0, 0, 0, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_158 : Eqn alphabet [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] ![0, (-2), 0, 0, 0, 0, 2] := by
  exact eqn_change ![0, (-2), 0, 0, 0, 0, 2] (eqn_symm eq_157) (by decide)

theorem eq_170 : Eqn alphabet [2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1] [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 1, (-1)] := by
  have h : Eqn alphabet [2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1] [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 1, (-1)] :=
    eqn_cast [2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1] [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 1, (-1)] (eqn_overlap_checked [1, 1, 1, 0, 1, 0, 1, 0, 2, 0] [1] [1, 1, 1] [2, 2, 0, 2, 2, 0, 1, 0, 1, 0] [2, 2, 2] [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1] [1, 1, 1, 1] (by decide) (by decide) eq_70 eq_3) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1] [2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1]
  have hb : Eqn alphabet [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 2] [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 2]
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_171 : Eqn alphabet [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 2] [2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-1), 1] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 1] (eqn_symm eq_170) (by decide)

theorem eq_172 : Eqn alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-1), 1] := by
  have h : Eqn alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-1), 1] :=
    eqn_cast [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-1), 1] (eqn_overlap_checked [2, 2, 2] [2] [0, 1, 0, 2, 0, 2, 0, 2, 2, 2] [1, 1, 1] [0, 2, 0, 2, 0, 1, 1, 0, 1, 1] [2, 2, 2, 2] [2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2] (by decide) (by decide) eq_4 eq_73) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2] [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2]
  have hb : Eqn alphabet [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1] [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_173 : Eqn alphabet [0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1] [2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, 0] := by
  have h : Eqn alphabet [0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1] [2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, 0] :=
    eqn_cast [0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1] [2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, 0] (eqn_overlap_checked [2, 2, 0] [1, 1, 0, 1, 1] [0, 2, 0, 2, 0, 1] [0, 2, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 0, 2, 0, 1, 0] [2, 2, 0, 1, 1, 0, 1, 1] [1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1] (by decide) (by decide) eq_37 eq_74) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1] [0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1]
  have hb : Eqn alphabet [2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 0] [2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_180 : Eqn alphabet [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0] [0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 1, (-1), 0] := by
  have h : Eqn alphabet [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0] [0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 1, (-1), 0] :=
    eqn_cast [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0] [0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 1, (-1), 0] (seed_eqn alphabet alphabet_inverse [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0] [0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] false 9 ![6, 0, 0, 0, 1, (-1), 0] (by decide) (eqn_cast [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] [] ![6, 0, 0, 0, 1, (-1), 0] (eqn_relator alphabet_inverse eq_156) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0] [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0]
  have hb : Eqn alphabet [0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] [0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 1, (-1), 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_187 : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1] [0, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 0] ![(-5), 0, 1, 0, 0, 0, 1] := by
  have h : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1] [0, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 0] ![(-5), 0, 1, 0, 0, 0, 1] :=
    eqn_cast [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1] [0, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 0] ![(-5), 0, 1, 0, 0, 0, 1] (eqn_overlap_checked [0, 2, 0, 2, 0, 2, 0, 2] [0, 2] [2, 0, 1, 1] [1, 0, 1, 0, 1, 0, 1, 0] [2, 2, 0, 1, 1, 0] [0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [0, 2, 2, 0, 1, 1] (by decide) (by decide) eq_18 eq_8) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1] [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1]
  have hb : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 0] [0, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 0]
  exact eqn_change ![(-5), 0, 1, 0, 0, 0, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_188 : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 0] [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1] ![5, 0, (-1), 0, 0, 0, (-1)] := by
  exact eqn_change ![5, 0, (-1), 0, 0, 0, (-1)] (eqn_symm eq_187) (by decide)

theorem eq_189 : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 1] [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2] ![0, (-2), 0, 0, 0, 0, 2] := by
  have h : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 1, 2, 2, 2, 0, 2, 2, 0, 1] [1, 1, 0, 1, 1, 0, 2, 1, 1, 0, 1, 1, 0, 2] ![0, (-2), 0, 0, 0, 0, 2] :=
    eqn_cast [2, 2, 2, 0, 2, 2, 0, 1, 2, 2, 2, 0, 2, 2, 0, 1] [1, 1, 0, 1, 1, 0, 2, 1, 1, 0, 1, 1, 0, 2] ![0, (-2), 0, 0, 0, 0, 2] (eqn_power eq_45 2) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 1, 2, 2, 2, 0, 2, 2, 0, 1] [2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_change ![0, (-1), 0, 0, 0, 0, 1] (eqn_trans (eqn_refl alphabet [2, 2, 2, 0, 2, 2, 0, 1, 2, 2, 2, 0, 2, 2, 0, 1]) (eqn_cast [2, 2, 2, 0, 2, 2, 0, 1, 2, 2, 2, 0, 2, 2, 0, 1] [1, 1, 0, 1, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 1] ![0, (-1), 0, 0, 0, 0, 1] (eqn_context [] [2, 2, 2, 0, 2, 2, 0, 1] eq_45) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 1, 0, 1, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 1] [2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 1] ![0, 1, 0, 0, 0, 0, (-1)] (eqn_context [] [2, 2, 0, 2, 2, 0, 1] eq_39) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [1, 1, 0, 1, 1, 0, 2, 1, 1, 0, 1, 1, 0, 2] [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [1, 1, 0, 1, 1, 0, 2, 1, 1, 0, 1, 1, 0, 2]) (eqn_cast [1, 1, 0, 1, 1, 0, 2, 1, 1, 0, 1, 1, 0, 2] [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [1, 1, 0, 1, 1, 0] [1, 0, 1, 1, 0, 2] eq_2) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, (-2), 0, 0, 0, 0, 2] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_196 : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0] [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] ![1, 0, 0, 0, (-1), 1, 0] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0] [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] ![1, 0, 0, 0, (-1), 1, 0] :=
    eqn_cast [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0] [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] ![1, 0, 0, 0, (-1), 1, 0] (eqn_overlap_checked [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] [0] [0] [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] [] [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0] [0, 0] (by decide) (by decide) eq_156 eq_0) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0] [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0]
  have hb : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2]
  exact eqn_change ![1, 0, 0, 0, (-1), 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_198 : Eqn alphabet [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0] [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 1, (-1), 0] := by
  have h : Eqn alphabet [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0] [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 1, (-1), 0] :=
    eqn_cast [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0] [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 1, (-1), 0] (eqn_overlap_checked [2] [1] [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0] [] [0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] [2, 1] [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0] (by decide) (by decide) eq_2 eq_180) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0] [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0]
  have hb : Eqn alphabet [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 1, (-1), 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_199 : Eqn alphabet [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1] [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, (-1), 1, 0] := by
  exact eqn_change ![0, 0, 0, 0, (-1), 1, 0] (eqn_symm eq_198) (by decide)

theorem eq_201 : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2] [1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 1, (-2)] := by
  have h : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 1, 0, 2, 2] [1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] ![0, 1, 0, 0, 0, 1, (-2)] :=
    eqn_cast [0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 1, 0, 2, 2] [1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] ![0, 1, 0, 0, 0, 1, (-2)] (eqn_overlap_checked [1, 0, 2, 0, 2, 0] [1, 1, 0] [1, 1, 0, 2, 2] [0, 1, 0, 2, 0, 2, 0, 1, 1] [2, 2, 2, 0, 2, 2, 0] [1, 0, 2, 0, 2, 0, 1, 1, 0] [1, 1, 0, 1, 1, 0, 2, 2] (by decide) (by decide) eq_57 eq_39) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 1, 0, 2, 2] [0, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2] ![0, 1, 0, 0, 0, 0, 0] :=
    eqn_change ![0, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 1, 0, 2, 2]) (eqn_cast [0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 1, 0, 2, 2] [0, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2] ![0, 1, 0, 0, 0, 0, 0] (eqn_context [0, 1, 0, 2, 0, 2, 0] [0, 2, 2] eq_3) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] [1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_202 : Eqn alphabet [1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] [0, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2] ![0, 0, 0, 0, 0, (-1), 2] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 2] (eqn_symm eq_201) (by decide)


end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay.PowerCertificate
