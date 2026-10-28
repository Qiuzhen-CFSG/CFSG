module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.PowerIdentities.PowerChunk06

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

theorem eq_642 : Eqn alphabet [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2] [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 2, (-4)] := by
  have h : Eqn alphabet [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2] [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 2, (-4)] :=
    eqn_cast [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2] [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 2, (-4)] (eqn_overlap_checked [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1] [1] [2] [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0] [] [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1] [1, 2] (by decide) (by decide) eq_641 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2] [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2]
  have hb : Eqn alphabet [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1] [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-4)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_643 : Eqn alphabet [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2] [2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] := by
  have h : Eqn alphabet [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2] [2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] :=
    eqn_cast [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2] [2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] (seed_eqn alphabet alphabet_inverse [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2] [2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1] false 11 ![5, 0, 0, 0, 0, (-2), 4] (by decide) (eqn_cast [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] [] ![5, 0, 0, 0, 0, (-2), 4] (eqn_relator alphabet_inverse eq_641) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2] [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2]
  have hb : Eqn alphabet [2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1] [2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-2), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_658 : Eqn alphabet [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 1, (-4)] := by
  have h : Eqn alphabet [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 1, (-4)] :=
    eqn_cast [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 1, (-4)] (eqn_overlap_checked [0] [2, 2, 0, 1, 1] [1, 0, 1, 0, 2, 0, 2, 0, 2] [2, 2, 0, 1, 1, 0] [1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1] [0, 2, 2, 0, 1, 1] [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2] (by decide) (by decide) eq_8 eq_599) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2]
  have hb : Eqn alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1] [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-4)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_659 : Eqn alphabet [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 1, (-4)] := by
  have h : Eqn alphabet [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 1, (-4)] :=
    eqn_cast [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 1, (-4)] (eqn_overlap_checked [1] [2] [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] [] [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1] [1, 2] [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] (by decide) (by decide) eq_1 eq_658) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2]
  have hb : Eqn alphabet [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1] [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-4)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_660 : Eqn alphabet [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1] [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, (-1), 4] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 4] (eqn_symm eq_659) (by decide)

theorem eq_661 : Eqn alphabet [0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 1, (-4)] := by
  have h : Eqn alphabet [0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 1, (-4)] :=
    eqn_cast [0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 1, (-4)] (seed_eqn alphabet alphabet_inverse [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0] [0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0] false 2 ![6, 0, 0, 0, 0, 1, (-4)] (by decide) (eqn_cast [2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0] [] ![6, 0, 0, 0, 0, 1, (-4)] (eqn_relator alphabet_inverse eq_658) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2]
  have hb : Eqn alphabet [1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0] [1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-4)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_662 : Eqn alphabet [1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0] [0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, (-1), 4] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 4] (eqn_symm eq_661) (by decide)

theorem eq_663 : Eqn alphabet [1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2] [2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] := by
  have h : Eqn alphabet [1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2] [2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] :=
    eqn_cast [1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2] [2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] (eqn_overlap_checked [2, 0] [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [2] [1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0] [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1] [2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 2] (by decide) (by decide) eq_613 eq_172) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2] [1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2]
  have hb : Eqn alphabet [2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1] [2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-2), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_664 : Eqn alphabet [2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1] [1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 2, (-4)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-4)] (eqn_symm eq_663) (by decide)

theorem eq_665 : Eqn alphabet [2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1] [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 2] := by
  have h : Eqn alphabet [2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1] [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 2] :=
    eqn_cast [2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1] [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 2] (eqn_overlap_checked [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] [2] [1] [2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0] [] [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 2] [2, 1] (by decide) (by decide) eq_627 eq_2) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1] [2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1]
  have hb : Eqn alphabet [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 2] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_667 : Eqn alphabet [0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 2] [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 2] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 2] [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 2] :=
    eqn_cast [0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 2] [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 2] (eqn_overlap_checked [2] [1] [0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 2] [] [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1] [2, 1] [1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 2] (by decide) (by decide) eq_2 eq_629) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 2] [0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 2]
  have hb : Eqn alphabet [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1] [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 2] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_668 : Eqn alphabet [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1] [0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, (-2)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, (-2)] (eqn_symm eq_667) (by decide)

theorem eq_670 : Eqn alphabet [2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1] [1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, (-2)] := by
  have h : Eqn alphabet [2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1] [1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, (-2)] :=
    eqn_cast [2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1] [1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, (-2)] (eqn_overlap_checked [1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2] [2] [1] [2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0] [] [1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] [2, 1] (by decide) (by decide) eq_633 eq_2) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1] [2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1]
  have hb : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2] [1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2]
  exact eqn_change ![0, 0, 0, 0, 0, 0, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_680 : Eqn alphabet [0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2] [2, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] := by
  have h : Eqn alphabet [0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2] [2, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] :=
    eqn_cast [0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2] [2, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] (eqn_overlap_checked [2] [1] [0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2] [] [2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1] [2, 1] [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2] (by decide) (by decide) eq_2 eq_643) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2] [0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2]
  have hb : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1] [2, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-2), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_681 : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1] [0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 2, (-4)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-4)] (eqn_symm eq_680) (by decide)

theorem eq_692 : Eqn alphabet [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 1, (-4)] := by
  have h : Eqn alphabet [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 1, (-4)] :=
    eqn_cast [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 1, (-4)] (eqn_overlap_checked [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0] [1] [2] [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] [] [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1] [1, 2] (by decide) (by decide) eq_660 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2]
  have hb : Eqn alphabet [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0] [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-4)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_696 : Eqn alphabet [2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] [1, 1, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0] ![0, (-1), 0, 0, 0, 2, (-4)] := by
  have h : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1] [1, 1, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 1, 0, 0, 0, 3, (-5)] :=
    eqn_cast [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1] [1, 1, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 1, 0, 0, 0, 3, (-5)] (eqn_overlap_checked [1, 1, 0] [1, 1, 1, 0, 1, 0, 2, 0, 2] [0, 1, 1] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1] [2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0] [1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] (by decide) (by decide) eq_535 eq_99) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1] [2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 2, 0, 0, 0, 1, (-1)] :=
    eqn_change ![0, 2, 0, 0, 0, 1, (-1)] (eqn_trans (eqn_change ![0, 2, 0, 0, 0, 0, (-1)] (eqn_trans (eqn_refl alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1]) (eqn_cast [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1] [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 2, 0, 0, 0, 0, (-1)] (eqn_context [2, 0, 2, 0, 1, 0] [] eq_52) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 2] [2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 1, 0] (eqn_context [2] [2, 0, 2, 2, 0, 2, 2, 2] eq_5) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [1, 1, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0] [1, 1, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 1, 0]
  exact eqn_change ![0, (-1), 0, 0, 0, 2, (-4)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_711 : Eqn alphabet [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1] [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2] ![0, 1, 0, 0, 0, (-1), 4] := by
  have h : Eqn alphabet [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1] [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2] ![0, 1, 0, 0, 0, (-1), 4] :=
    eqn_cast [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1] [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2] ![0, 1, 0, 0, 0, (-1), 4] (eqn_overlap_checked [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [1] [1, 1, 1] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] [2, 2, 2] [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] [1, 1, 1, 1] (by decide) (by decide) eq_579 eq_3) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1]
  have hb : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2] [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2]
  exact eqn_change ![0, 1, 0, 0, 0, (-1), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_725 : Eqn alphabet [2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1] ![0, (-1), 0, 0, 0, 2, (-4)] := by
  have h : Eqn alphabet [2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1] ![0, (-1), 0, 0, 0, 2, (-4)] :=
    eqn_cast [2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1] ![0, (-1), 0, 0, 0, 2, (-4)] (seed_eqn alphabet alphabet_inverse [2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1] false 14 ![5, (-1), 0, 0, 0, 2, (-4)] (by decide) (eqn_cast [2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [] ![5, (-1), 0, 0, 0, 2, (-4)] (eqn_relator alphabet_inverse eq_696) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 2, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2]
  have hb : Eqn alphabet [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1] [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1]
  exact eqn_change ![0, (-1), 0, 0, 0, 2, (-4)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_747 : Eqn alphabet [2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1] [1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 1, 1, (-2)] := by
  have h : Eqn alphabet [2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1] [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0] ![(-1), 0, 0, 0, 0, 1, (-2)] :=
    eqn_cast [2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1] [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0] ![(-1), 0, 0, 0, 0, 1, (-2)] (seed_eqn alphabet alphabet_inverse [0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 2, 2] [2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1] [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0] false 10 ![6, 0, 0, 0, 0, 1, (-2)] (by decide) (eqn_cast [0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 2, 2] [] ![6, 0, 0, 0, 0, 1, (-2)] (eqn_relator alphabet_inverse eq_526) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1]
  have hb : Eqn alphabet [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0] [1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2] ![1, 0, 0, 0, 1, 0, 0] :=
    eqn_change ![1, 0, 0, 0, 1, 0, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 1, 0, 0] (eqn_trans (eqn_refl alphabet [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0]) (eqn_cast [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0] [0, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 1, 0, 0] (eqn_context [0] [] eq_474) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2] [1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2] eq_0) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, 0, 0, 0, 1, 1, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_751 : Eqn alphabet [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1] [1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1, 0] ![0, 0, 0, 0, 1, 1, (-1)] := by
  have h : Eqn alphabet [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1] [0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0] ![(-1), 0, 0, 0, 1, 1, (-2)] :=
    eqn_cast [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1] [0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0] ![(-1), 0, 0, 0, 1, 1, (-2)] (seed_eqn alphabet alphabet_inverse [2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2] [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1] [0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0] false 2 ![5, 0, 0, 0, 1, 1, (-2)] (by decide) (eqn_cast [2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2] [] ![5, 0, 0, 0, 1, 1, (-2)] (eqn_relator alphabet_inverse eq_747) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1] [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1]
  have hb : Eqn alphabet [0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0] [1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1, 0] ![1, 0, 0, 0, 0, 0, 1] :=
    eqn_change ![1, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_refl alphabet [0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0]) (eqn_cast [0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1, 0] [0, 0, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 1] (eqn_context [0] [2, 0, 1, 0, 1, 1, 0] eq_9) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1, 0] [1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1, 0] eq_0) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, 0, 0, 0, 1, 1, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_756 : Eqn alphabet [0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2] [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] ![0, 0, 0, 0, 1, 1, (-2)] := by
  have h : Eqn alphabet [0, 2, 2, 2, 0, 1, 0, 1, 1, 0, 2, 2, 0] [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] ![1, 0, 0, 0, 1, 1, (-1)] :=
    eqn_cast [0, 2, 2, 2, 0, 1, 0, 1, 1, 0, 2, 2, 0] [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] ![1, 0, 0, 0, 1, 1, (-1)] (seed_eqn alphabet alphabet_inverse [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 1, 1, 0, 2, 2] [0, 2, 2, 2, 0, 1, 0, 1, 1, 0, 2, 2, 0] [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] false 5 ![4, 0, 0, 0, 1, 1, (-1)] (by decide) (eqn_cast [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 1, 1, 0, 2, 2] [] ![4, 0, 0, 0, 1, 1, (-1)] (eqn_relator alphabet_inverse eq_751) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 2, 2, 0, 1, 0, 1, 1, 0, 2, 2, 0] [0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2] ![1, 0, 0, 0, 0, 0, 1] :=
    eqn_change ![1, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_refl alphabet [0, 2, 2, 2, 0, 1, 0, 1, 1, 0, 2, 2, 0]) (eqn_cast [0, 2, 2, 2, 0, 1, 0, 1, 1, 0, 2, 2, 0] [0, 2, 2, 2, 0, 1, 0, 0, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 1] (eqn_context [0, 2, 2, 2, 0, 1, 0] [] eq_9) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 2, 2, 2, 0, 1, 0, 0, 1, 1, 0, 2, 2] [0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [0, 2, 2, 2, 0, 1] [1, 1, 0, 2, 2] eq_0) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 1, 1, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_757 : Eqn alphabet [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] [0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2] ![0, 0, 0, 0, (-1), (-1), 2] := by
  exact eqn_change ![0, 0, 0, 0, (-1), (-1), 2] (eqn_symm eq_756) (by decide)

theorem eq_758 : Eqn alphabet [0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2] [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 1, 1, (-2)] := by
  have h : Eqn alphabet [0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2] [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 1, 1, (-2)] :=
    eqn_cast [0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2] [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 1, 1, (-2)] (eqn_overlap_checked [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0] [1] [2] [0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2] [] [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] [1, 2] (by decide) (by decide) eq_757 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2] [0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2]
  have hb : Eqn alphabet [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0] [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 1, 1, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_759 : Eqn alphabet [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2] ![0, 0, 0, 0, (-1), (-1), 2] := by
  have h : Eqn alphabet [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2] ![0, 0, 0, 0, (-1), (-1), 2] :=
    eqn_cast [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2] ![0, 0, 0, 0, (-1), (-1), 2] (eqn_overlap_checked [1] [2] [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] [] [0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2] [1, 2] [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] (by decide) (by decide) eq_1 eq_757) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1]
  have hb : Eqn alphabet [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2] [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2]
  exact eqn_change ![0, 0, 0, 0, (-1), (-1), 2] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_760 : Eqn alphabet [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2] [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] ![0, 0, 0, 0, 1, 1, (-2)] := by
  exact eqn_change ![0, 0, 0, 0, 1, 1, (-2)] (eqn_symm eq_759) (by decide)

theorem eq_761 : Eqn alphabet [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1] [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2] ![0, 0, 0, 0, (-1), (-1), 2] := by
  have h : Eqn alphabet [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1] [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2] ![0, 0, 0, 0, (-1), (-1), 2] :=
    eqn_cast [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1] [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2] ![0, 0, 0, 0, (-1), (-1), 2] (seed_eqn alphabet alphabet_inverse [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1] [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2] false 2 ![3, 0, 0, 0, (-1), (-1), 2] (by decide) (eqn_cast [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] [] ![3, 0, 0, 0, (-1), (-1), 2] (eqn_relator alphabet_inverse eq_757) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1] [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1]
  have hb : Eqn alphabet [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2] [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2]
  exact eqn_change ![0, 0, 0, 0, (-1), (-1), 2] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_762 : Eqn alphabet [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2] [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1] ![0, 0, 0, 0, 1, 1, (-2)] := by
  exact eqn_change ![0, 0, 0, 0, 1, 1, (-2)] (eqn_symm eq_761) (by decide)

theorem eq_763 : Eqn alphabet [0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1] [1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, (-1), (-1), 2] := by
  have h : Eqn alphabet [0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1] [1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, (-1), (-1), 2] :=
    eqn_cast [0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1] [1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, (-1), (-1), 2] (seed_eqn alphabet alphabet_inverse [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] [0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1] [1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] false 3 ![3, 0, 0, 0, (-1), (-1), 2] (by decide) (eqn_cast [2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] [] ![3, 0, 0, 0, (-1), (-1), 2] (eqn_relator alphabet_inverse eq_757) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1] [0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1]
  have hb : Eqn alphabet [1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] [1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0]
  exact eqn_change ![0, 0, 0, 0, (-1), (-1), 2] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_764 : Eqn alphabet [1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] [0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1] ![0, 0, 0, 0, 1, 1, (-2)] := by
  exact eqn_change ![0, 0, 0, 0, 1, 1, (-2)] (eqn_symm eq_763) (by decide)

theorem eq_765 : Eqn alphabet [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1] [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2] ![0, 0, 0, 0, (-1), (-1), 2] := by
  have h : Eqn alphabet [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1] [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2] ![0, 0, 0, 0, (-1), (-1), 2] :=
    eqn_cast [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1] [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2] ![0, 0, 0, 0, (-1), (-1), 2] (eqn_overlap_checked [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2] [2] [1] [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1] [] [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2, 2] [2, 1] (by decide) (by decide) eq_760 eq_2) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1] [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1]
  have hb : Eqn alphabet [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2] [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2]
  exact eqn_change ![0, 0, 0, 0, (-1), (-1), 2] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_766 : Eqn alphabet [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1] [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, (-1), (-1), 2] := by
  have h : Eqn alphabet [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1] [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, (-1), (-1), 2] :=
    eqn_cast [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1] [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, (-1), (-1), 2] (eqn_overlap_checked [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] [2] [1] [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1] [] [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0, 2] [2, 1] (by decide) (by decide) eq_762 eq_2) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1] [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 1, 1]
  have hb : Eqn alphabet [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 2, 2, 2, 0, 1, 1, 1, 0]
  exact eqn_change ![0, 0, 0, 0, (-1), (-1), 2] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)


end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay.PowerCertificate
