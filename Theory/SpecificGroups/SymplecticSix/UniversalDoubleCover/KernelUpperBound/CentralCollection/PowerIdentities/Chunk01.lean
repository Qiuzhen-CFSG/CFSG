module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.PowerIdentities.Chunk00

/-!
# Checked central word equations

This is a dependency slice of untrusted Knuth–Bendix discovery. Each
equation is proved by the structural word calculus, with its exponent
vector checked separately to avoid unfolding the quotient group.

Source: Wilson–Nickerson–Bray, ATLAS `S62G1-P1.M`.
See `PowerIdentities/source/README.md` for the trace and conventions.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay

theorem eq_492 : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 2, 2] [1, 1, 0, 1, 1, 0, 1, 1, 1] ![0, (-2), 0, 0, 0, 0, 1] := by
  have h : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 2, 2] [1, 1, 0, 1, 1, 0, 1, 1, 1] ![0, (-2), 0, 0, 0, 0, 1] :=
    eqn_cast [2, 2, 2, 0, 2, 2, 0, 2, 2] [1, 1, 0, 1, 1, 0, 1, 1, 1] ![0, (-2), 0, 0, 0, 0, 1] (eqn_overlap_checked [1, 1, 0, 1, 1, 0] [2, 2] [2, 2] [2, 2, 2, 0, 2, 2, 0] [1, 1, 1] [1, 1, 0, 1, 1, 0, 2, 2] [2, 2, 2, 2] (by decide) (by decide) eq_460 eq_4) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 2, 2] [2, 2, 2, 0, 2, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 2, 0, 2, 2]
  have hb : Eqn alphabet [1, 1, 0, 1, 1, 0, 1, 1, 1] [1, 1, 0, 1, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 1, 0, 1, 1, 1]
  exact eqn_change ![0, (-2), 0, 0, 0, 0, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_493 : Eqn alphabet [1, 1, 0, 1, 1, 0, 1, 1, 1] [2, 2, 2, 0, 2, 2, 0, 2, 2] ![0, 2, 0, 0, 0, 0, (-1)] := by
  exact eqn_change ![0, 2, 0, 0, 0, 0, (-1)] (eqn_symm eq_492) (by decide)

theorem eq_496 : Eqn alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, (-1)] := by
  have h : Eqn alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, (-1)] :=
    eqn_cast [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, (-1)] (eqn_overlap_checked [1, 0, 2] [2, 0, 1] [0, 2, 0, 1] [2, 0, 1, 1, 0, 2] [0, 2, 0, 1, 0] [1, 0, 2, 2, 0, 1] [2, 0, 1, 0, 2, 0, 1] (by decide) (by decide) eq_15 eq_22) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 0, 2, 0, 2, 0, 1]
  have hb : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 0] [1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_498 : Eqn alphabet [0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, (-1)] := by
  have h : Eqn alphabet [0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, (-1)] :=
    eqn_cast [0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, (-1)] (eqn_overlap_checked [1] [2] [0, 1, 1, 0, 2, 0, 2, 0, 1] [] [1, 0, 2, 0, 2, 0, 1, 0] [1, 2] [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] (by decide) (by decide) eq_1 eq_496) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 1, 0, 2, 0, 2, 0, 1] [0, 1, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 0, 2, 0, 2, 0, 1]
  have hb : Eqn alphabet [1, 1, 0, 2, 0, 2, 0, 1, 0] [1, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_499 : Eqn alphabet [1, 1, 0, 2, 0, 2, 0, 1, 0] [0, 1, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, (-1), 1] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 1] (eqn_symm eq_498) (by decide)

theorem eq_506 : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1, 1] [0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 1] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1, 1] [0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 1] :=
    eqn_cast [2, 0, 1, 0, 2, 0, 2, 0, 1, 1] [0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 1] (eqn_overlap_checked [0, 2, 0, 2, 0, 1, 1, 0] [2] [1] [2, 0, 1, 0, 2, 0, 2, 0, 1] [] [0, 2, 0, 2, 0, 1, 1, 0, 2] [2, 1] (by decide) (by decide) eq_487 eq_2) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1, 1] [2, 0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1, 1]
  have hb : Eqn alphabet [0, 2, 0, 2, 0, 1, 1, 0] [0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 1, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_507 : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1] [1, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 1] := by
  have h : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1] [1, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 1] :=
    eqn_cast [0, 1, 0, 2, 0, 2, 0, 1, 1] [1, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 1] (eqn_overlap_checked [1] [2] [0, 1, 0, 2, 0, 2, 0, 1, 1] [] [0, 2, 0, 2, 0, 1, 1, 0] [1, 2] [2, 0, 1, 0, 2, 0, 2, 0, 1, 1] (by decide) (by decide) eq_1 eq_506) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1] [0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1]
  have hb : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 1, 0] [1, 0, 2, 0, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 1, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_508 : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 1, 0] [0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 1, (-1)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-1)] (eqn_symm eq_507) (by decide)

theorem eq_569 : Eqn alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-1), 0] := by
  have h : Eqn alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-1), 0] :=
    eqn_cast [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-1), 0] (eqn_overlap_checked [2, 2, 2] [2] [0, 1, 0, 2, 0, 2, 2, 2] [1, 1, 1] [0, 2, 0, 1, 0, 1, 1, 1] [2, 2, 2, 2] [2, 0, 1, 0, 2, 0, 2, 2, 2] (by decide) (by decide) eq_4 eq_475) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2]
  have hb : Eqn alphabet [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_588 : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [2, 0, 1] [1, 0, 2, 0, 2, 0, 1] [1, 0] [1, 0, 2, 0, 2, 0, 1, 0] [0, 1, 0, 2, 0, 2, 0, 1, 1] [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] [1, 0, 2, 0, 2, 0, 1, 1, 0] (by decide) (by decide) eq_496 eq_508) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 1, 0, 1, 0]
  have hb : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_589 : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_symm eq_588) (by decide)

theorem eq_590 : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [1] [2] [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] [1, 2] (by decide) (by decide) eq_589 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2] [1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2]
  have hb : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_599 : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 2] [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 2] [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 2, 0, 2, 0, 1, 0, 1, 0, 2] [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [2] [1] [0, 2, 0, 2, 0, 1, 0, 1, 0, 2] [] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [2, 1] [1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2] (by decide) (by decide) eq_2 eq_590) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 2] [0, 2, 0, 2, 0, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 2]
  have hb : Eqn alphabet [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_600 : Eqn alphabet [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [0, 2, 0, 2, 0, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_symm eq_599) (by decide)

theorem eq_602 : Eqn alphabet [2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 1] [1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0] ![(-5), (-1), 1, 0, 0, 0, 0] := by
  have h : Eqn alphabet [2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 1] [1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0] ![(-5), (-1), 1, 0, 0, 0, 0] :=
    eqn_cast [2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 1] [1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0] ![(-5), (-1), 1, 0, 0, 0, 0] (eqn_overlap_checked [1, 1, 1] [1] [0, 1, 0, 1, 0, 1, 0, 1] [2, 2, 2] [0, 2, 0, 2, 0, 2, 0, 2, 0] [1, 1, 1, 1] [1, 0, 1, 0, 1, 0, 1, 0, 1] (by decide) (by decide) eq_3 eq_98) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 1] [2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 1]
  have hb : Eqn alphabet [1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0] [1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0]
  exact eqn_change ![(-5), (-1), 1, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_603 : Eqn alphabet [1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0] [2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 1] ![5, 1, (-1), 0, 0, 0, 0] := by
  exact eqn_change ![5, 1, (-1), 0, 0, 0, 0] (eqn_symm eq_602) (by decide)

theorem eq_618 : Eqn alphabet [0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1] [2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2] ![0, 1, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1] [2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2] ![0, 1, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1] [2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2] ![0, 1, 0, 0, 0, 0, 0] (eqn_overlap_checked [2, 2, 0] [1, 1, 0, 1, 1] [0, 1, 1, 1] [0, 2, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 2, 0, 2, 2] [2, 2, 0, 1, 1, 0, 1, 1] [1, 1, 0, 1, 1, 0, 1, 1, 1] (by decide) (by decide) eq_458 eq_493) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1] [0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1]
  have hb : Eqn alphabet [2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2] [2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2]
  exact eqn_change ![0, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_619 : Eqn alphabet [2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 2] [0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, (-1), 0, 0, 0, 0, 0] (eqn_symm eq_618) (by decide)

theorem eq_663 : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, (-1)] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, (-1)] :=
    eqn_cast [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, (-1)] (eqn_overlap_checked [2, 0, 1, 0] [2, 0, 1] [1, 0, 2, 0, 2, 0, 1] [0, 2, 0, 1, 0] [1, 0, 2, 0, 2, 0, 1, 0] [2, 0, 1, 0, 2, 0, 1] [2, 0, 1, 1, 0, 2, 0, 2, 0, 1] (by decide) (by decide) eq_22 eq_496) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1]
  have hb : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_714 : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 1] := by
  have h : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 1] :=
    eqn_cast [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 1] (eqn_overlap_checked [0] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] [1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1] (by decide) (by decide) eq_663 eq_589) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1]
  have hb : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_715 : Eqn alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 1] := by
  have h : Eqn alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 1] :=
    eqn_cast [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 1] (eqn_overlap_checked [1] [2] [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] [] [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [1, 2] [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] (by decide) (by decide) eq_1 eq_714) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1]
  have hb : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_716 : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0] [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, (-1)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, (-1)] (eqn_symm eq_715) (by decide)

theorem eq_794 : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0] ![(-5), 0, 1, 0, 0, 1, 1] := by
  have h : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0] ![(-5), 0, 1, 0, 0, 0, 1] :=
    eqn_cast [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0] ![(-5), 0, 1, 0, 0, 0, 1] (eqn_overlap_checked [2, 0, 2, 0, 2, 0, 2, 0] [2, 0] [1, 1, 0, 2, 2] [0, 1, 0, 1, 0, 1, 0, 1] [1, 0, 2, 2, 0] [2, 0, 2, 0, 2, 0, 2, 0, 2, 0] [2, 0, 1, 1, 0, 2, 2] (by decide) (by decide) eq_123 eq_36) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2]
  have hb : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0] [2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 1, 0] :=
    eqn_change ![0, 0, 0, 0, 0, 1, 0] (eqn_trans (eqn_refl alphabet [2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0]) (eqn_cast [2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0] [2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 1, 0] (eqn_context [2, 0, 2, 0, 2] [2, 0] eq_5) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![(-5), 0, 1, 0, 0, 1, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_795 : Eqn alphabet [0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2] [2, 2, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0] ![5, 0, (-1), 0, 0, 0, (-1)] := by
  have h : Eqn alphabet [0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2] [2, 2, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0] ![5, 0, (-1), 0, 0, 0, (-1)] :=
    eqn_cast [0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2] [2, 2, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0] ![5, 0, (-1), 0, 0, 0, (-1)] (eqn_overlap_checked [2, 2, 0, 1, 1] [0, 2] [0, 2, 0, 2, 0, 2, 0, 2] [0, 2, 2, 0, 1] [1, 0, 1, 0, 1, 0, 1, 0] [2, 2, 0, 1, 1, 0, 2] [0, 2, 0, 2, 0, 2, 0, 2, 0, 2] (by decide) (by decide) eq_35 eq_124) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2] [0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2]
  have hb : Eqn alphabet [2, 2, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0] [2, 2, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0]
  exact eqn_change ![5, 0, (-1), 0, 0, 0, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_800 : Eqn alphabet [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 2, 0, 0, 0, 0, (-2)] := by
  have h : Eqn alphabet [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 2, 0, 0, 0, 0, (-2)] :=
    eqn_cast [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 2, 0, 0, 0, 0, (-2)] (eqn_overlap_checked [1, 0, 2, 2, 0, 2] [2, 2] [0, 1, 1, 0, 1, 1] [2, 0, 1, 1, 0, 1, 1] [0, 2, 2, 0, 2, 2, 2] [1, 0, 2, 2, 0, 2, 2, 2] [2, 2, 0, 1, 1, 0, 1, 1] (by decide) (by decide) eq_465 eq_458) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]
  have hb : Eqn alphabet [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2]
  exact eqn_change ![0, 2, 0, 0, 0, 0, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_801 : Eqn alphabet [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] ![0, (-2), 0, 0, 0, 0, 2] := by
  exact eqn_change ![0, (-2), 0, 0, 0, 0, 2] (eqn_symm eq_800) (by decide)

theorem eq_817 : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0] [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2] ![0, (-2), 0, 0, 0, 0, 2] := by
  have h : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0] [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2] ![0, (-2), 0, 0, 0, 0, 2] :=
    eqn_cast [2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0] [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2] ![0, (-2), 0, 0, 0, 0, 2] (eqn_overlap_checked [1, 1, 0, 1, 1, 0, 1] [1, 1] [0, 2, 2, 0] [2, 2, 2, 0, 2, 2, 0, 2, 2] [0, 1, 1, 0, 2, 2] [1, 1, 0, 1, 1, 0, 1, 1, 1] [1, 1, 0, 2, 2, 0] (by decide) (by decide) eq_493 eq_14) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0] [2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0]
  have hb : Eqn alphabet [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2] [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2]
  exact eqn_change ![0, (-2), 0, 0, 0, 0, 2] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_818 : Eqn alphabet [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2] [2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0] ![0, 2, 0, 0, 0, 0, (-2)] := by
  exact eqn_change ![0, 2, 0, 0, 0, 0, (-2)] (eqn_symm eq_817) (by decide)

theorem eq_892 : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] [2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 2, 1] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] [2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 1, 0] :=
    eqn_cast [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] [2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 1, 0] (eqn_overlap_checked [2, 2, 0, 1, 0, 1, 0, 2] [0, 2, 0, 1] [0, 2] [0, 2, 0, 2, 0, 1, 0, 1, 0, 2] [2, 0, 1, 0, 2, 0] [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [0, 2, 0, 1, 0, 2] (by decide) (by decide) eq_600 eq_5) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2]
  have hb : Eqn alphabet [2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0] [2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 1, 1] :=
    eqn_change ![0, 0, 0, 0, 0, 1, 1] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_refl alphabet [2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0]) (eqn_cast [2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0] [2, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 1] (eqn_context [2, 2, 0, 1, 0] [0, 2, 0] eq_15) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0] [2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 1, 0] (eqn_context [2] [1, 0, 2, 0, 2, 0] eq_22) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, 0, 0, 0, 0, 2, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_910 : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0] ![(-6), 0, 1, 0, 0, 1, 1] := by
  have h : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0] ![(-6), 0, 1, 0, 0, 1, 1] :=
    eqn_cast [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0] ![(-6), 0, 1, 0, 0, 1, 1] (eqn_overlap_checked [0] [0] [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [] [2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0] [0, 0] [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] (by decide) (by decide) eq_0 eq_794) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2]
  have hb : Eqn alphabet [0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0] [0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0]
  exact eqn_change ![(-6), 0, 1, 0, 0, 1, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_911 : Eqn alphabet [0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0] [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 2] ![6, 0, (-1), 0, 0, (-1), (-1)] := by
  exact eqn_change ![6, 0, (-1), 0, 0, (-1), (-1)] (eqn_symm eq_910) (by decide)

theorem eq_1020 : Eqn alphabet [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] ![(-1), 0, 0, 0, 1, (-1), 0] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0, 1] [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 1, (-1), 0] :=
    eqn_cast [2, 0, 1, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0, 1] [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 1, (-1), 0] (eqn_overlap_checked [0, 2] [0, 1, 0, 2] [0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 1, 0, 2, 0] [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] [0, 2, 0, 1, 0, 2] [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] (by decide) (by decide) eq_5 eq_177) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [2, 0, 1, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0, 1]) (eqn_cast [2, 0, 1, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2, 0, 1, 0, 2] [2, 0, 2, 0, 1, 0, 1] eq_0) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0]
  exact eqn_change ![(-1), 0, 0, 0, 1, (-1), 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)


end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay
