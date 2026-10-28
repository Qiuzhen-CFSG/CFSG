module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.PowerIdentities.PowerChunk00

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

theorem eq_45 : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 1] [1, 1, 0, 1, 1, 0, 2] ![0, (-1), 0, 0, 0, 0, 1] := by
  have h : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 1] [1, 1, 0, 1, 1, 0, 2] ![0, (-1), 0, 0, 0, 0, 1] :=
    eqn_cast [2, 2, 2, 0, 2, 2, 0, 1] [1, 1, 0, 1, 1, 0, 2] ![0, (-1), 0, 0, 0, 0, 1] (seed_eqn alphabet alphabet_inverse [2, 2, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0] [2, 2, 2, 0, 2, 2, 0, 1] [1, 1, 0, 1, 1, 0, 2] true 6 ![2, 1, 0, 0, 0, 0, (-1)] (by decide) (eqn_cast [2, 2, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0] [] ![2, 1, 0, 0, 0, 0, (-1)] (eqn_relator alphabet_inverse eq_37) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 1] [2, 2, 2, 0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 2, 0, 1]
  have hb : Eqn alphabet [1, 1, 0, 1, 1, 0, 2] [1, 1, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 1, 0, 2]
  exact eqn_change ![0, (-1), 0, 0, 0, 0, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_46 : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 2, 2] [0, 2, 0, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, (-1), 0] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 2, 2] [0, 2, 0, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, (-1), 0] :=
    eqn_cast [2, 0, 1, 0, 2, 0, 2, 2, 2] [0, 2, 0, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, (-1), 0] (eqn_overlap_checked [0, 2, 0, 1, 0] [2] [2, 2, 2] [2, 0, 1, 0, 2, 0] [1, 1, 1] [0, 2, 0, 1, 0, 2] [2, 2, 2, 2] (by decide) (by decide) eq_5 eq_4) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 2, 2] [2, 0, 1, 0, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 2, 2, 2]
  have hb : Eqn alphabet [0, 2, 0, 1, 0, 1, 1, 1] [0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 1, 1, 1]
  exact eqn_change ![0, (-1), 0, 0, 0, (-1), 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_47 : Eqn alphabet [2, 2, 2, 0, 2, 0, 1, 0] [1, 1, 1, 0, 1, 0, 2, 0, 1] ![0, (-1), 0, 0, 0, 1, 0] := by
  have h : Eqn alphabet [2, 2, 2, 0, 2, 0, 1, 0] [1, 1, 1, 0, 1, 0, 2, 0, 1] ![0, (-1), 0, 0, 0, 1, 0] :=
    eqn_cast [2, 2, 2, 0, 2, 0, 1, 0] [1, 1, 1, 0, 1, 0, 2, 0, 1] ![0, (-1), 0, 0, 0, 1, 0] (eqn_overlap_checked [1, 1, 1] [1] [0, 2, 0, 1, 0] [2, 2, 2] [0, 1, 0, 2, 0, 1] [1, 1, 1, 1] [1, 0, 2, 0, 1, 0] (by decide) (by decide) eq_3 eq_6) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 2, 0, 2, 0, 1, 0] [2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 0, 1, 0]
  have hb : Eqn alphabet [1, 1, 1, 0, 1, 0, 2, 0, 1] [1, 1, 1, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 1, 0, 2, 0, 1]
  exact eqn_change ![0, (-1), 0, 0, 0, 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_48 : Eqn alphabet [1, 1, 1, 0, 1, 0, 2, 0, 1] [2, 2, 2, 0, 2, 0, 1, 0] ![0, 1, 0, 0, 0, (-1), 0] := by
  exact eqn_change ![0, 1, 0, 0, 0, (-1), 0] (eqn_symm eq_47) (by decide)

theorem eq_49 : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1] [0, 2, 0, 2, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, (-1), 1] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1] [0, 2, 0, 2, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, (-1), 1] :=
    eqn_cast [2, 0, 1, 0, 2, 0, 2, 0, 1] [0, 2, 0, 2, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, (-1), 1] (eqn_overlap_checked [0, 2, 0] [1, 0, 2] [2, 0, 1] [2, 0, 1, 0, 2, 0] [2, 0, 1, 1, 0, 2] [0, 2, 0, 1, 0, 2] [1, 0, 2, 2, 0, 1] (by decide) (by decide) eq_5 eq_10) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1]
  have hb : Eqn alphabet [0, 2, 0, 2, 0, 1, 1, 0, 2] [0, 2, 0, 2, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 1, 1, 0, 2]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_50 : Eqn alphabet [0, 2, 0, 2, 0, 1, 1, 0, 2] [2, 0, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 1, (-1)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-1)] (eqn_symm eq_49) (by decide)

theorem eq_51 : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 2, 2] [2, 0, 1, 0, 1, 0, 2, 2, 0] ![0, 0, 0, 0, 0, (-1), 1] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 2, 2] [2, 0, 1, 0, 1, 0, 2, 2, 0] ![0, 0, 0, 0, 0, (-1), 1] :=
    eqn_cast [0, 2, 0, 1, 0, 1, 0, 2, 2] [2, 0, 1, 0, 1, 0, 2, 2, 0] ![0, 0, 0, 0, 0, (-1), 1] (eqn_overlap_checked [2, 0, 1, 0] [2, 0, 1] [1, 0, 2, 2] [0, 2, 0, 1, 0] [1, 0, 2, 2, 0] [2, 0, 1, 0, 2, 0, 1] [2, 0, 1, 1, 0, 2, 2] (by decide) (by decide) eq_12 eq_14) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 2, 2] [0, 2, 0, 1, 0, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 1, 0, 2, 2]
  have hb : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 2, 0] [2, 0, 1, 0, 1, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 0, 2, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_52 : Eqn alphabet [1, 1, 1, 0, 1, 1, 0, 1, 1] [2, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 2, 0, 0, 0, 0, (-1)] := by
  have h : Eqn alphabet [1, 1, 1, 0, 1, 1, 0, 1, 1] [2, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 2, 0, 0, 0, 0, (-1)] :=
    eqn_cast [1, 1, 1, 0, 1, 1, 0, 1, 1] [2, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 2, 0, 0, 0, 0, (-1)] (eqn_overlap_checked [2, 2] [2, 2] [0, 1, 1, 0, 1, 1] [1, 1, 1] [0, 2, 2, 0, 2, 2, 2] [2, 2, 2, 2] [2, 2, 0, 1, 1, 0, 1, 1] (by decide) (by decide) eq_4 eq_37) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1, 1, 0, 1, 1, 0, 1, 1] [1, 1, 1, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 1, 1, 0, 1, 1]
  have hb : Eqn alphabet [2, 2, 0, 2, 2, 0, 2, 2, 2] [2, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 2, 0, 2, 2, 2]
  exact eqn_change ![0, 2, 0, 0, 0, 0, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_55 : Eqn alphabet [0, 2, 2, 0, 1, 0, 1, 0, 2] [2, 2, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 1, (-1)] := by
  have h : Eqn alphabet [0, 2, 2, 0, 1, 0, 1, 0, 2] [2, 2, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 1, (-1)] :=
    eqn_cast [0, 2, 2, 0, 1, 0, 1, 0, 2] [2, 2, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 1, (-1)] (seed_eqn alphabet alphabet_inverse [0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 1] [0, 2, 2, 0, 1, 0, 1, 0, 2] [2, 2, 0, 1, 0, 1, 0, 2, 0] false 7 ![4, 0, 0, 0, 0, 1, (-1)] (by decide) (eqn_cast [0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 1] [] ![4, 0, 0, 0, 0, 1, (-1)] (eqn_relator alphabet_inverse eq_50) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 2, 0, 1, 0, 1, 0, 2] [0, 2, 2, 0, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 0, 1, 0, 1, 0, 2]
  have hb : Eqn alphabet [2, 2, 0, 1, 0, 1, 0, 2, 0] [2, 2, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 0, 1, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_56 : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1] [1, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 1, (-1)] := by
  have h : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1] [1, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 1, (-1)] :=
    eqn_cast [0, 1, 0, 2, 0, 2, 0, 1, 1] [1, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 1, (-1)] (seed_eqn alphabet alphabet_inverse [0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 1] [0, 1, 0, 2, 0, 2, 0, 1, 1] [1, 0, 2, 0, 2, 0, 1, 1, 0] false 16 ![4, 0, 0, 0, 0, 1, (-1)] (by decide) (eqn_cast [0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 1] [] ![4, 0, 0, 0, 0, 1, (-1)] (eqn_relator alphabet_inverse eq_50) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1] [0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1]
  have hb : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 1, 0] [1, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 1, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_57 : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 1, 0] [0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, (-1), 1] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 1] (eqn_symm eq_56) (by decide)

theorem eq_58 : Eqn alphabet [0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, (-1), 1] := by
  have h : Eqn alphabet [0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, (-1), 1] :=
    eqn_cast [0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, (-1), 1] (seed_eqn alphabet alphabet_inverse [0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1] [0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 1, 0, 2, 0, 2, 0, 1, 0] false 9 ![4, 0, 0, 0, 0, (-1), 1] (by decide) (eqn_cast [0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1] [] ![4, 0, 0, 0, 0, (-1), 1] (eqn_relator alphabet_inverse eq_51) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 1, 0, 2, 0, 2, 0, 1] [0, 1, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 0, 2, 0, 2, 0, 1]
  have hb : Eqn alphabet [1, 1, 0, 2, 0, 2, 0, 1, 0] [1, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_59 : Eqn alphabet [1, 1, 0, 2, 0, 2, 0, 1, 0] [0, 1, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 1, (-1)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-1)] (eqn_symm eq_58) (by decide)

theorem eq_60 : Eqn alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, (-1)] := by
  have h : Eqn alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, (-1)] :=
    eqn_cast [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, (-1)] (eqn_overlap_checked [1, 0, 2] [2, 0, 1] [0, 2, 0, 1] [2, 0, 1, 1, 0, 2] [0, 2, 0, 1, 0] [1, 0, 2, 2, 0, 1] [2, 0, 1, 0, 2, 0, 1] (by decide) (by decide) eq_10 eq_12) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 1]
  have hb : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 0] [1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_61 : Eqn alphabet [0, 2, 2, 0, 1, 0, 1, 0] [2, 2, 0, 1, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 1, (-1)] := by
  have h : Eqn alphabet [0, 2, 2, 0, 1, 0, 1, 0] [2, 2, 0, 1, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 1, (-1)] :=
    eqn_cast [0, 2, 2, 0, 1, 0, 1, 0] [2, 2, 0, 1, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 1, (-1)] (eqn_overlap_checked [2, 2, 0, 1] [1, 0, 2] [0, 1, 0] [0, 2, 2, 0, 1] [0, 1, 0, 2, 0, 1] [2, 2, 0, 1, 1, 0, 2] [1, 0, 2, 0, 1, 0] (by decide) (by decide) eq_13 eq_6) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 2, 0, 1, 0, 1, 0] [0, 2, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 0, 1, 0, 1, 0]
  have hb : Eqn alphabet [2, 2, 0, 1, 0, 1, 0, 2, 0, 1] [2, 2, 0, 1, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 0, 1, 0, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_62 : Eqn alphabet [2, 2, 0, 1, 0, 1, 0, 2, 0, 1] [0, 2, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, (-1), 1] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 1] (eqn_symm eq_61) (by decide)

theorem eq_63 : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1, 1] [0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 1] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1, 1] [0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 1] :=
    eqn_cast [2, 0, 1, 0, 2, 0, 2, 0, 1, 1] [0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 1] (eqn_overlap_checked [0, 2, 0, 2, 0, 1, 1, 0] [2] [1] [2, 0, 1, 0, 2, 0, 2, 0, 1] [] [0, 2, 0, 2, 0, 1, 1, 0, 2] [2, 1] (by decide) (by decide) eq_50 eq_2) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1, 1] [2, 0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1, 1]
  have hb : Eqn alphabet [0, 2, 0, 2, 0, 1, 1, 0] [0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 1, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_66 : Eqn alphabet [0, 2, 2, 0, 2, 2, 2, 0, 2, 2] [2, 2, 0, 2, 2, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 2, 2, 0, 2, 2, 2, 0, 2, 2] [2, 2, 0, 2, 2, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 2, 2, 0, 2, 2, 2, 0, 2, 2] [2, 2, 0, 2, 2, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [2, 2, 0] [1, 1, 0, 1, 1] [0, 2, 2] [0, 2, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 2, 0] [2, 2, 0, 1, 1, 0, 1, 1] [1, 1, 0, 1, 1, 0, 2, 2] (by decide) (by decide) eq_37 eq_39) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 2, 0, 2, 2, 2, 0, 2, 2] [0, 2, 2, 0, 2, 2, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 0, 2, 2, 2, 0, 2, 2]
  have hb : Eqn alphabet [2, 2, 0, 2, 2, 2, 0, 2, 2, 0] [2, 2, 0, 2, 2, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 2, 2, 0, 2, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_67 : Eqn alphabet [0, 1, 1, 0, 1, 1, 1, 0, 1, 1] [1, 1, 0, 1, 1, 1, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 1, 1, 0, 1, 1, 1, 0, 1, 1] [1, 1, 0, 1, 1, 1, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 1, 1, 0, 1, 1, 1, 0, 1, 1] [1, 1, 0, 1, 1, 1, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse [0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1] [0, 1, 1, 0, 1, 1, 1, 0, 1, 1] [1, 1, 0, 1, 1, 1, 0, 1, 1, 0] false 10 ![3, 0, 0, 0, 0, 0, 0] (by decide) (eqn_cast [0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1] [] ![3, 0, 0, 0, 0, 0, 0] (eqn_relator alphabet_inverse eq_66) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 1, 0, 1, 1, 1, 0, 1, 1] [0, 1, 1, 0, 1, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 0, 1, 1, 1, 0, 1, 1]
  have hb : Eqn alphabet [1, 1, 0, 1, 1, 1, 0, 1, 1, 0] [1, 1, 0, 1, 1, 1, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 1, 1, 0, 1, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_68 : Eqn alphabet [1, 1, 0, 1, 1, 1, 0, 1, 1, 0] [0, 1, 1, 0, 1, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_symm eq_67) (by decide)

theorem eq_69 : Eqn alphabet [2, 2, 0, 2, 2, 0, 1, 0, 1, 0] [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![0, (-1), 0, 0, 0, 1, (-1)] := by
  have h : Eqn alphabet [2, 2, 0, 2, 2, 0, 1, 0, 1, 0] [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![0, (-1), 0, 0, 0, 1, (-1)] :=
    eqn_cast [2, 2, 0, 2, 2, 0, 1, 0, 1, 0] [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![0, (-1), 0, 0, 0, 1, (-1)] (eqn_overlap_checked [1, 1, 1, 0, 1] [1, 0, 2] [0, 1, 0] [2, 2, 0, 2, 2, 0, 1] [0, 1, 0, 2, 0, 1] [1, 1, 1, 0, 1, 1, 0, 2] [1, 0, 2, 0, 1, 0] (by decide) (by decide) eq_40 eq_6) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 2, 2, 0, 1, 0, 1, 0] [2, 2, 0, 2, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 2, 0, 1, 0, 1, 0]
  have hb : Eqn alphabet [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1] [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1]
  exact eqn_change ![0, (-1), 0, 0, 0, 1, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_70 : Eqn alphabet [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1] [2, 2, 0, 2, 2, 0, 1, 0, 1, 0] ![0, 1, 0, 0, 0, (-1), 1] := by
  exact eqn_change ![0, 1, 0, 0, 0, (-1), 1] (eqn_symm eq_69) (by decide)

theorem eq_71 : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 1, 1, 1] [2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 2] ![0, 1, 0, 0, 0, (-1), 1] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 1, 1, 1] [2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 2] ![0, 1, 0, 0, 0, (-1), 1] :=
    eqn_cast [0, 2, 0, 1, 0, 1, 0, 1, 1, 1] [2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 2] ![0, 1, 0, 0, 0, (-1), 1] (eqn_overlap_checked [2, 0, 1, 0] [2, 0, 1] [1, 0, 1, 1, 1] [0, 2, 0, 1, 0] [1, 0, 2, 2, 0, 2, 2] [2, 0, 1, 0, 2, 0, 1] [2, 0, 1, 1, 0, 1, 1, 1] (by decide) (by decide) eq_12 eq_42) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 1, 1, 1] [0, 2, 0, 1, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 1, 0, 1, 1, 1]
  have hb : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 2] [2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 2]
  exact eqn_change ![0, 1, 0, 0, 0, (-1), 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_72 : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 2] [0, 2, 0, 1, 0, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, 1, (-1)] := by
  exact eqn_change ![0, (-1), 0, 0, 0, 1, (-1)] (eqn_symm eq_71) (by decide)

theorem eq_73 : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2] [0, 2, 0, 2, 0, 1, 1, 0, 1, 1] ![0, (-1), 0, 0, 0, (-1), 1] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2] [0, 2, 0, 2, 0, 1, 1, 0, 1, 1] ![0, (-1), 0, 0, 0, (-1), 1] :=
    eqn_cast [2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2] [0, 2, 0, 2, 0, 1, 1, 0, 1, 1] ![0, (-1), 0, 0, 0, (-1), 1] (eqn_overlap_checked [0, 2, 0] [1, 0, 2] [2, 0, 2, 2, 2] [2, 0, 1, 0, 2, 0] [2, 0, 1, 1, 0, 1, 1] [0, 2, 0, 1, 0, 2] [1, 0, 2, 2, 0, 2, 2, 2] (by decide) (by decide) eq_5 eq_44) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2] [2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2]
  have hb : Eqn alphabet [0, 2, 0, 2, 0, 1, 1, 0, 1, 1] [0, 2, 0, 2, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 1, 1, 0, 1, 1]
  exact eqn_change ![0, (-1), 0, 0, 0, (-1), 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_74 : Eqn alphabet [1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1] [2, 2, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 1, 0, 0, 0, 1, (-1)] := by
  have h : Eqn alphabet [1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1] [2, 2, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 1, 0, 0, 0, 1, (-1)] :=
    eqn_cast [1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1] [2, 2, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 1, 0, 0, 0, 1, (-1)] (eqn_overlap_checked [2, 2, 2, 0, 2] [2, 0, 1] [0, 2, 0, 1] [1, 1, 0, 1, 1, 0, 2] [0, 2, 0, 1, 0] [2, 2, 2, 0, 2, 2, 0, 1] [2, 0, 1, 0, 2, 0, 1] (by decide) (by decide) eq_45 eq_12) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1]
  have hb : Eqn alphabet [2, 2, 2, 0, 2, 0, 2, 0, 1, 0] [2, 2, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![0, 1, 0, 0, 0, 1, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_81 : Eqn alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-1), 0] := by
  have h : Eqn alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-1), 0] :=
    eqn_cast [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-1), 0] (eqn_overlap_checked [2, 2, 2] [2] [0, 1, 0, 2, 0, 2, 2, 2] [1, 1, 1] [0, 2, 0, 1, 0, 1, 1, 1] [2, 2, 2, 2] [2, 0, 1, 0, 2, 0, 2, 2, 2] (by decide) (by decide) eq_4 eq_46) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2]
  have hb : Eqn alphabet [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_82 : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 2] := by
  have h : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 2] :=
    eqn_cast [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 2] (eqn_overlap_checked [2, 0, 1] [1, 0, 2, 0, 2, 0, 1] [1, 0] [1, 0, 2, 0, 2, 0, 1, 0] [0, 1, 0, 2, 0, 2, 0, 1, 1] [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 0, 2, 0, 2, 0, 1, 1, 0] (by decide) (by decide) eq_60 eq_57) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 1, 0, 1, 0]
  have hb : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-2), 2] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_83 : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 2, (-2)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-2)] (eqn_symm eq_82) (by decide)

theorem eq_94 : Eqn alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2] [1, 0, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, (-1), (-1)] := by
  have h : Eqn alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2] [1, 0, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, (-1), (-1)] :=
    eqn_cast [2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2] [1, 0, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, (-1), (-1)] (eqn_overlap_checked [1, 0, 2] [2, 0, 1] [0, 2, 0, 2, 2, 2] [2, 0, 1, 1, 0, 2] [0, 2, 0, 1, 0, 1, 1, 1] [1, 0, 2, 2, 0, 1] [2, 0, 1, 0, 2, 0, 2, 2, 2] (by decide) (by decide) eq_10 eq_46) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2] [2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2]
  have hb : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 0, 1, 1, 1] [1, 0, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 1, 0, 1, 1, 1]
  exact eqn_change ![0, (-1), 0, 0, 0, (-1), (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_98 : Eqn alphabet [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0] [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, (-1), 0, 0, 0, (-1), 1] := by
  have h : Eqn alphabet [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0] [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, (-1), 0, 0, 0, (-1), 1] :=
    eqn_cast [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0] [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, (-1), 0, 0, 0, (-1), 1] (eqn_overlap_checked [1, 1, 1] [1] [0, 2, 0, 2, 0, 1, 1, 0] [2, 2, 2] [0, 1, 0, 2, 0, 2, 0, 1, 1] [1, 1, 1, 1] [1, 0, 2, 0, 2, 0, 1, 1, 0] (by decide) (by decide) eq_3 eq_57) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0] [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0]
  have hb : Eqn alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1]
  exact eqn_change ![0, (-1), 0, 0, 0, (-1), 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_99 : Eqn alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 1, 0, 0, 0, 1, (-1)] := by
  exact eqn_change ![0, 1, 0, 0, 0, 1, (-1)] (eqn_symm eq_98) (by decide)


end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay.PowerCertificate
