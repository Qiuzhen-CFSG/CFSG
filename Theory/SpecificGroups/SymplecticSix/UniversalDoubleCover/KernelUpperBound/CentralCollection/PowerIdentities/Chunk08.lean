module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.PowerIdentities.Chunk07

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

theorem eq_4541 : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [2] [1] [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] [2, 1] [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] (by decide) (by decide) eq_2 eq_4540) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0]
  have hb : Eqn alphabet [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4542 : Eqn alphabet [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, (-3), 2] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-3), 2] (eqn_symm eq_4541) (by decide)

theorem eq_4543 : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 3, (-2)] := by
  have h : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 3, (-2)] :=
    eqn_cast [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_overlap_checked [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] [2] [1] [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] [2, 1] (by decide) (by decide) eq_4542 eq_2) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1]
  have hb : Eqn alphabet [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_5882 : Eqn alphabet [2, 0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] [2, 0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 1, 6, (-7)] := by
  have h : Eqn alphabet [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 1, 0] :=
    eqn_cast [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 1, 0] (eq_3820) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 2, 0, 2] [2, 0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] ![1, 0, 0, 0, (-1), (-2), 5] :=
    eqn_change ![1, 0, 0, 0, (-1), (-2), 5] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, (-3), 2] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, (-3), 2] (eqn_trans (eqn_refl alphabet [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 2, 0, 2]) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 2, 0, 2] [0, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2] ![0, 0, 0, 0, 0, (-3), 2] (eqn_context [0] [2, 0, 2] eq_4529) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2] [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2] eq_0) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2] [2, 0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, (-1), 1, 3] (eqn_context [] [] eq_2122) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] [2, 0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] ![1, 0, 0, 0, 0, 3, (-2)] :=
    eqn_change ![1, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 3, (-2)] (eqn_trans (eqn_refl alphabet [2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0]) (eqn_cast [2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] [2, 0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 3, (-2)] (eqn_context [2, 0, 2] [0] eq_4543) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 0] [2, 0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2, 0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] [] eq_0) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, 0, 0, 0, 1, 6, (-7)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_24427 : Eqn alphabet [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![15, 6, (-2), (-1), (-1), 0, (-6)] := by
  have h : Eqn alphabet [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 3, 0, 0, 0, 0, (-3)] :=
    eqn_cast [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 3, 0, 0, 0, 0, (-3)] (eqn_overlap_checked [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2] [2, 2] [0, 1, 1, 0, 1, 1] [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [0, 2, 2, 0, 2, 2, 2] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] [2, 2, 0, 1, 1, 0, 1, 1] (by decide) (by decide) eq_801 eq_458) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![(-15), (-3), 2, 1, 1, 0, 3] :=
    eqn_change ![(-15), (-3), 2, 1, 1, 0, 3] (eqn_trans (eqn_change ![(-6), (-3), 0, 1, 0, 0, 3] (eqn_trans (eqn_change ![(-6), (-3), 0, 1, 0, 0, 2] (eqn_trans (eqn_change ![(-6), 0, 0, 1, 0, 0, 0] (eqn_trans (eqn_refl alphabet [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]) (eqn_cast [2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0] ![(-6), 0, 0, 1, 0, 0, 0] (eqn_context [2] [] eq_340) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0] [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 0] ![0, (-3), 0, 0, 0, 0, 2] (eqn_context [] [0, 2, 2, 0] eq_1439) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 0] [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 1] (eqn_context [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1] [] eq_14) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![(-9), 0, 2, 0, 1, 0, 0] (eqn_context [1] [2, 2] eq_3796) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2]
  exact eqn_change ![15, 6, (-2), (-1), (-1), 0, (-6)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)


end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay
