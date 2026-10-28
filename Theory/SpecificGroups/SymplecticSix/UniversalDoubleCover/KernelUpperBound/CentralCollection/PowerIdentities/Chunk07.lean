module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.PowerIdentities.Chunk06

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

theorem eq_4494 : Eqn alphabet [2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 2, (-2)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-2)] (eqn_symm eq_4493) (by decide)

theorem eq_4495 : Eqn alphabet [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 2, (-2)] := by
  have h : Eqn alphabet [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [1, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 2, (-2)] :=
    eqn_cast [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [1, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 2, (-2)] (eqn_overlap_checked [1] [2] [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [] [2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [1, 2] [2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] (by decide) (by decide) eq_1 eq_4494) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2]
  have hb : Eqn alphabet [1, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [1, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1]) (eqn_cast [1, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] eq_1) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4496 : Eqn alphabet [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 2, (-2)] := by
  have h : Eqn alphabet [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [0, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![(-1), 0, 0, 0, 0, 2, (-2)] :=
    eqn_cast [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [0, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![(-1), 0, 0, 0, 0, 2, (-2)] (eqn_overlap_checked [0] [0] [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [] [0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [0, 0] [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] (by decide) (by decide) eq_0 eq_4495) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2]
  have hb : Eqn alphabet [0, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1]) (eqn_cast [0, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] eq_0) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4497 : Eqn alphabet [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 2, (-2)] := by
  have h : Eqn alphabet [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [1, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 2, (-2)] :=
    eqn_cast [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [1, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 2, (-2)] (eqn_overlap_checked [1] [2] [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [] [2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [1, 2] [2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] (by decide) (by decide) eq_1 eq_4496) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2]
  have hb : Eqn alphabet [1, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [1, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1]) (eqn_cast [1, 2, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [] [0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] eq_1) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4498 : Eqn alphabet [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 2, (-2)] := by
  have h : Eqn alphabet [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [0, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![(-1), 0, 0, 0, 0, 2, (-2)] :=
    eqn_cast [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [0, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![(-1), 0, 0, 0, 0, 2, (-2)] (eqn_overlap_checked [0] [0] [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [] [0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [0, 0] [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] (by decide) (by decide) eq_0 eq_4497) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2]
  have hb : Eqn alphabet [0, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [0, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1]) (eqn_cast [0, 0, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] eq_0) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4499 : Eqn alphabet [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, (-2), 2] := by
  have h : Eqn alphabet [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, (-2), 2] :=
    eqn_cast [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, (-2), 2] (eqn_overlap_checked [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0] [2] [1] [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [] [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2] [2, 1] (by decide) (by decide) eq_4498 eq_2) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1]
  have hb : Eqn alphabet [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0] [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, (-2), 2] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4500 : Eqn alphabet [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, (-3), 2] := by
  have h : Eqn alphabet [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, (-2), 2] :=
    eqn_cast [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, (-2), 2] (eqn_overlap_checked [1] [2] [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [] [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0] [1, 2] [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] (by decide) (by decide) eq_1 eq_4499) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1]
  have hb : Eqn alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 0] :=
    eqn_change ![0, 0, 0, 0, 0, (-1), 0] (eqn_trans (eqn_refl alphabet [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0]) (eqn_cast [1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 0] (eqn_context [] [0] eq_569) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, 0, 0, 0, 0, (-3), 2] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4505 : Eqn alphabet [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [1] [2] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0] [] [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [1, 2] (by decide) (by decide) eq_4500 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2]
  have hb : Eqn alphabet [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4506 : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [1] [2] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [] [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [1, 2] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] (by decide) (by decide) eq_1 eq_4505) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2]
  have hb : Eqn alphabet [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4507 : Eqn alphabet [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] ![0, 0, 0, 0, 0, (-3), 2] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-3), 2] (eqn_symm eq_4506) (by decide)

theorem eq_4511 : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] [1] [2] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [1, 2] (by decide) (by decide) eq_4507 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2]
  have hb : Eqn alphabet [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4512 : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [1] [2] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] [1, 2] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] (by decide) (by decide) eq_1 eq_4511) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2]
  have hb : Eqn alphabet [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4513 : Eqn alphabet [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, (-3), 2] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-3), 2] (eqn_symm eq_4512) (by decide)

theorem eq_4517 : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0] [1] [2] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] [1, 2] (by decide) (by decide) eq_4513 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2]
  have hb : Eqn alphabet [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4518 : Eqn alphabet [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2] [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2] [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2] [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [1] [2] [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2] [] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0] [1, 2] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2] (by decide) (by decide) eq_1 eq_4517) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2] [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2]
  have hb : Eqn alphabet [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0] [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4519 : Eqn alphabet [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0] [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2] ![0, 0, 0, 0, 0, (-3), 2] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-3), 2] (eqn_symm eq_4518) (by decide)

theorem eq_4523 : Eqn alphabet [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] ![1, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] ![1, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] ![1, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] [0] [0] [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2] [] [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0] [0, 0] (by decide) (by decide) eq_4519 eq_0) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0]
  have hb : Eqn alphabet [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1]
  exact eqn_change ![1, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4524 : Eqn alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [0] [0] [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [] [1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] [0, 0] [0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] (by decide) (by decide) eq_0 eq_4523) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0]
  have hb : Eqn alphabet [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4525 : Eqn alphabet [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, (-3), 2] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-3), 2] (eqn_symm eq_4524) (by decide)

theorem eq_4527 : Eqn alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] [1] [2] [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] [1, 2] (by decide) (by decide) eq_4525 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2]
  have hb : Eqn alphabet [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4528 : Eqn alphabet [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [1] [2] [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] [1, 2] [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] (by decide) (by decide) eq_1 eq_4527) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2]
  have hb : Eqn alphabet [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4529 : Eqn alphabet [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, (-3), 2] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-3), 2] (eqn_symm eq_4528) (by decide)

theorem eq_4531 : Eqn alphabet [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1] [2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1] [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2] ![0, 1, 0, 0, 0, 2, (-2)] :=
    eqn_cast [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1] [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2] ![0, 1, 0, 0, 0, 2, (-2)] (eqn_overlap_checked [2, 0, 2, 2, 2, 0, 2, 0, 1, 0] [1, 1, 1] [1] [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0] [2, 2, 2] [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [1, 1, 1, 1] (by decide) (by decide) eq_4499 eq_3) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1] [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1]
  have hb : Eqn alphabet [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2] [2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2] ![0, (-1), 0, 0, 0, 1, 0] :=
    eqn_change ![0, (-1), 0, 0, 0, 1, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 1, 0] (eqn_trans (eqn_refl alphabet [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2]) (eqn_cast [2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2] [2, 0, 2, 2, 2, 2, 0, 1, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 1, 0] (eqn_context [2, 0, 2, 2, 2] [2, 2] eq_5) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 2, 2, 2, 2, 0, 1, 0, 2, 0, 2, 2] [2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2] ![0, (-1), 0, 0, 0, 0, 0] (eqn_context [2, 0] [0, 1, 0, 2, 0, 2, 2] eq_4) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4532 : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1] [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1] [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1] [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [2] [1] [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1] [] [2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2] [2, 1] [1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1] (by decide) (by decide) eq_2 eq_4531) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1] [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1]
  have hb : Eqn alphabet [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2] [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4533 : Eqn alphabet [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2] [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1] ![0, 0, 0, 0, 0, (-3), 2] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-3), 2] (eqn_symm eq_4532) (by decide)

theorem eq_4534 : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1] [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1] [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1] [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [2] [1] [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1] [] [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2] [2, 1] (by decide) (by decide) eq_4533 eq_2) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1] [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1]
  have hb : Eqn alphabet [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4535 : Eqn alphabet [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1] [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1] [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1] [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [2] [1] [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1] [] [2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [2, 1] [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1] (by decide) (by decide) eq_2 eq_4534) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1] [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1]
  have hb : Eqn alphabet [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4536 : Eqn alphabet [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1] ![0, 0, 0, 0, 0, (-3), 2] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-3), 2] (eqn_symm eq_4535) (by decide)

theorem eq_4537 : Eqn alphabet [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] [2] [1] [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1] [] [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [2, 1] (by decide) (by decide) eq_4536 eq_2) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1]
  have hb : Eqn alphabet [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4538 : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] ![(-1), 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] ![(-1), 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] ![(-1), 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [0] [0] [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [] [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] [0, 0] [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] (by decide) (by decide) eq_0 eq_4537) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1]
  have hb : Eqn alphabet [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0]
  exact eqn_change ![(-1), 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4539 : Eqn alphabet [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] ![1, 0, 0, 0, 0, (-3), 2] := by
  exact eqn_change ![1, 0, 0, 0, 0, (-3), 2] (eqn_symm eq_4538) (by decide)

theorem eq_4540 : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] [0] [0] [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] [0, 0] (by decide) (by decide) eq_4539 eq_0) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0]
  have hb : Eqn alphabet [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)


end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay
