module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.PowerIdentities.Inputs

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

theorem eq_0 : Eqn alphabet [0, 0] [] ![1, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 0] [] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [0, 0] [] ![1, 0, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 0) [0, 0] [] false 0 (sourceExponent 0) (by decide) (source_relation 0)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 0] [0, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 0]
  have hb : Eqn alphabet [] [] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet []
  exact eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_1 : Eqn alphabet [1, 2] [] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [1, 2] [] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [1, 2] [] ![0, 0, 0, 0, 0, 0, 0] ((show Eqn alphabet [1, 2] [] ![0, 0, 0, 0, 0, 0, 0] from by simp [Eqn, alphabet, readWord_cons, readWord_nil, collect])) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 2] [1, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 2]
  have hb : Eqn alphabet [] [] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet []
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_2 : Eqn alphabet [2, 1] [] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [2, 1] [] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [2, 1] [] ![0, 0, 0, 0, 0, 0, 0] ((show Eqn alphabet [2, 1] [] ![0, 0, 0, 0, 0, 0, 0] from by simp [Eqn, alphabet, readWord_cons, readWord_nil, collect])) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 1] [2, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 1]
  have hb : Eqn alphabet [] [] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet []
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_3 : Eqn alphabet [1, 1, 1, 1] [2, 2, 2] ![0, 1, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [1, 1, 1, 1] [2, 2, 2] ![0, 1, 0, 0, 0, 0, 0] :=
    eqn_cast [1, 1, 1, 1] [2, 2, 2] ![0, 1, 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 1) [1, 1, 1, 1] [2, 2, 2] false 0 (sourceExponent 1) (by decide) (source_relation 1)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1, 1, 1] [1, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 1]
  have hb : Eqn alphabet [2, 2, 2] [2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2]
  exact eqn_change ![0, 1, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_4 : Eqn alphabet [2, 2, 2, 2] [1, 1, 1] ![0, (-1), 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [2, 2, 2, 2] [1, 1, 1] ![0, (-1), 0, 0, 0, 0, 0] :=
    eqn_cast [2, 2, 2, 2] [1, 1, 1] ![0, (-1), 0, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 1) [2, 2, 2, 2] [1, 1, 1] true 0 (sourceExponent 1) (by decide) (source_relation 1)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 2, 2] [2, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 2]
  have hb : Eqn alphabet [1, 1, 1] [1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1]
  exact eqn_change ![0, (-1), 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_5 : Eqn alphabet [0, 2, 0, 1, 0, 2] [2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 1, 0] := by
  have h : Eqn alphabet [0, 2, 0, 1, 0, 2] [2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 1, 0] :=
    eqn_cast [0, 2, 0, 1, 0, 2] [2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 1, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 5) [0, 2, 0, 1, 0, 2] [2, 0, 1, 0, 2, 0] false 0 (sourceExponent 5) (by decide) (source_relation 5)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 1, 0, 2] [0, 2, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 2]
  have hb : Eqn alphabet [2, 0, 1, 0, 2, 0] [2, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_6 : Eqn alphabet [1, 0, 2, 0, 1, 0] [0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 1, 0] := by
  have h : Eqn alphabet [1, 0, 2, 0, 1, 0] [0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 1, 0] :=
    eqn_cast [1, 0, 2, 0, 1, 0] [0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 1, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 5) [1, 0, 2, 0, 1, 0] [0, 1, 0, 2, 0, 1] false 3 (sourceExponent 5) (by decide) (source_relation 5)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 1, 0] [1, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 1, 0]
  have hb : Eqn alphabet [0, 1, 0, 2, 0, 1] [0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_13 : Eqn alphabet [0, 2, 2, 0, 1, 1] [2, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 1] := by
  have h : Eqn alphabet [0, 2, 2, 0, 1, 1] [2, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 1] :=
    eqn_cast [0, 2, 2, 0, 1, 1] [2, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 1] (seed_eqn alphabet alphabet_inverse (sourceWord 6) [0, 2, 2, 0, 1, 1] [2, 2, 0, 1, 1, 0] false 0 (sourceExponent 6) (by decide) (source_relation 6)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 2, 0, 1, 1] [0, 2, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 0, 1, 1]
  have hb : Eqn alphabet [2, 2, 0, 1, 1, 0] [2, 2, 0, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_14 : Eqn alphabet [1, 1, 0, 2, 2, 0] [0, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 1] := by
  have h : Eqn alphabet [1, 1, 0, 2, 2, 0] [0, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 1] :=
    eqn_cast [1, 1, 0, 2, 2, 0] [0, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 1] (seed_eqn alphabet alphabet_inverse (sourceWord 6) [1, 1, 0, 2, 2, 0] [0, 1, 1, 0, 2, 2] false 4 (sourceExponent 6) (by decide) (source_relation 6)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1, 0, 2, 2, 0] [1, 1, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 2, 2, 0]
  have hb : Eqn alphabet [0, 1, 1, 0, 2, 2] [0, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 0, 2, 2]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_15 : Eqn alphabet [1, 0, 2, 2, 0, 1] [2, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 1] := by
  have h : Eqn alphabet [1, 0, 2, 2, 0, 1] [2, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 1] :=
    eqn_cast [1, 0, 2, 2, 0, 1] [2, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 1] (seed_eqn alphabet alphabet_inverse (sourceWord 6) [1, 0, 2, 2, 0, 1] [2, 0, 1, 1, 0, 2] false 5 (sourceExponent 6) (by decide) (source_relation 6)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 2, 0, 1] [1, 0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 2, 0, 1]
  have hb : Eqn alphabet [2, 0, 1, 1, 0, 2] [2, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 0, 2]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_22 : Eqn alphabet [2, 0, 1, 0, 2, 0, 1] [0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, 0] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 0, 1] [0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, 0] :=
    eqn_cast [2, 0, 1, 0, 2, 0, 1] [0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 1, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 5) [2, 0, 1, 0, 2, 0, 1] [0, 2, 0, 1, 0] false 1 (sourceExponent 5) (by decide) (source_relation 5)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 0, 1] [2, 0, 1, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 1]
  have hb : Eqn alphabet [0, 2, 0, 1, 0] [0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_35 : Eqn alphabet [2, 2, 0, 1, 1, 0, 2] [0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 1] := by
  have h : Eqn alphabet [2, 2, 0, 1, 1, 0, 2] [0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 1] :=
    eqn_cast [2, 2, 0, 1, 1, 0, 2] [0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 1] (seed_eqn alphabet alphabet_inverse (sourceWord 6) [2, 2, 0, 1, 1, 0, 2] [0, 2, 2, 0, 1] false 1 (sourceExponent 6) (by decide) (source_relation 6)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 1, 1, 0, 2] [2, 2, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 1, 0, 2]
  have hb : Eqn alphabet [0, 2, 2, 0, 1] [0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_36 : Eqn alphabet [2, 0, 1, 1, 0, 2, 2] [1, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 1] := by
  have h : Eqn alphabet [2, 0, 1, 1, 0, 2, 2] [1, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 1] :=
    eqn_cast [2, 0, 1, 1, 0, 2, 2] [1, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 1] (seed_eqn alphabet alphabet_inverse (sourceWord 6) [2, 0, 1, 1, 0, 2, 2] [1, 0, 2, 2, 0] false 2 (sourceExponent 6) (by decide) (source_relation 6)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 0, 2, 2] [2, 0, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 0, 2, 2]
  have hb : Eqn alphabet [1, 0, 2, 2, 0] [1, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_97 : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 1, 0] [2, 0, 2, 0, 2, 0, 2, 0, 2] ![(-4), 0, 1, 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 1, 0] [2, 0, 2, 0, 2, 0, 2, 0, 2] ![(-4), 0, 1, 0, 0, 0, 0] :=
    eqn_cast [0, 1, 0, 1, 0, 1, 0, 1, 0] [2, 0, 2, 0, 2, 0, 2, 0, 2] ![(-4), 0, 1, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 2) [0, 1, 0, 1, 0, 1, 0, 1, 0] [2, 0, 2, 0, 2, 0, 2, 0, 2] false 0 (sourceExponent 2) (by decide) (source_relation 2)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 1, 0] [0, 1, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 1, 0, 1, 0]
  have hb : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2]
  exact eqn_change ![(-4), 0, 1, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_98 : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 0, 1] [0, 2, 0, 2, 0, 2, 0, 2, 0] ![(-5), 0, 1, 0, 0, 0, 0] := by
  have h : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 0, 1] [0, 2, 0, 2, 0, 2, 0, 2, 0] ![(-5), 0, 1, 0, 0, 0, 0] :=
    eqn_cast [1, 0, 1, 0, 1, 0, 1, 0, 1] [0, 2, 0, 2, 0, 2, 0, 2, 0] ![(-5), 0, 1, 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 2) [1, 0, 1, 0, 1, 0, 1, 0, 1] [0, 2, 0, 2, 0, 2, 0, 2, 0] false 1 (sourceExponent 2) (by decide) (source_relation 2)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 0, 1] [1, 0, 1, 0, 1, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 0, 1, 0, 1]
  have hb : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 0] [0, 2, 0, 2, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 2, 0, 2, 0]
  exact eqn_change ![(-5), 0, 1, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_123 : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 1] ![5, 0, (-1), 0, 0, 0, 0] := by
  have h : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 1] ![5, 0, (-1), 0, 0, 0, 0] :=
    eqn_cast [2, 0, 2, 0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 1] ![5, 0, (-1), 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 2) [2, 0, 2, 0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 1] true 0 (sourceExponent 2) (by decide) (source_relation 2)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0] [2, 0, 2, 0, 2, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 2, 0, 2, 0, 2, 0]
  have hb : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 1] [0, 1, 0, 1, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 1, 0, 1]
  exact eqn_change ![5, 0, (-1), 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_124 : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 1, 0] ![5, 0, (-1), 0, 0, 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 1, 0] ![5, 0, (-1), 0, 0, 0, 0] :=
    eqn_cast [0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 1, 0] ![5, 0, (-1), 0, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 2) [0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 1, 0] true 1 (sourceExponent 2) (by decide) (source_relation 2)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [0, 2, 0, 2, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 2, 0, 2, 0, 2]
  have hb : Eqn alphabet [1, 0, 1, 0, 1, 0, 1, 0] [1, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 0, 1, 0]
  exact eqn_change ![5, 0, (-1), 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_173 : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1] [2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 1, 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1] [2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 1, 0, 0] :=
    eqn_cast [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1] [2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 1, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 4) [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1] [2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] false 0 (sourceExponent 4) (by decide) (source_relation 4)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1] [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1]
  have hb : Eqn alphabet [2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] [2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 1, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_174 : Eqn alphabet [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 1, 0, 0] := by
  have h : Eqn alphabet [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 1, 0, 0] :=
    eqn_cast [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 1, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 4) [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] false 7 (sourceExponent 4) (by decide) (source_relation 4)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0]
  have hb : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2]
  exact eqn_change ![0, 0, 0, 0, 1, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_177 : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 1, 0, 0] := by
  have h : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 1, 0, 0] :=
    eqn_cast [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 1, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 4) [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] false 10 (sourceExponent 4) (by decide) (source_relation 4)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1]
  have hb : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 1, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_178 : Eqn alphabet [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0] [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 1, 0, 0] := by
  have h : Eqn alphabet [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0] [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 1, 0, 0] :=
    eqn_cast [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0] [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 1, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 4) [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0] [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2] false 11 (sourceExponent 4) (by decide) (source_relation 4)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0] [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0]
  have hb : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2] [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2]
  exact eqn_change ![0, 0, 0, 0, 1, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_192 : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] ![1, 0, 0, 0, 1, 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] ![1, 0, 0, 0, 1, 0, 0] :=
    eqn_cast [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] ![1, 0, 0, 0, 1, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 4) [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] false 2 (sourceExponent 4) (by decide) (source_relation 4)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0]
  have hb : Eqn alphabet [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1]
  exact eqn_change ![1, 0, 0, 0, 1, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_340 : Eqn alphabet [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0] ![(-6), 0, 0, 1, 0, 0, 0] := by
  have h : Eqn alphabet [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0] ![(-6), 0, 0, 1, 0, 0, 0] :=
    eqn_cast [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0] ![(-6), 0, 0, 1, 0, 0, 0] (seed_eqn alphabet alphabet_inverse (sourceWord 3) [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0] false 0 (sourceExponent 3) (by decide) (source_relation 3)) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]
  have hb : Eqn alphabet [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0] [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0]
  exact eqn_change ![(-6), 0, 0, 1, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_458 : Eqn alphabet [2, 2, 0, 1, 1, 0, 1, 1] [0, 2, 2, 0, 2, 2, 2] ![0, 1, 0, 0, 0, 0, (-1)] := by
  have h : Eqn alphabet [2, 2, 0, 1, 1, 0, 1, 1] [0, 2, 2, 0, 2, 2, 2] ![0, 1, 0, 0, 0, 0, (-1)] :=
    eqn_cast [2, 2, 0, 1, 1, 0, 1, 1] [0, 2, 2, 0, 2, 2, 2] ![0, 1, 0, 0, 0, 0, (-1)] (eqn_overlap_checked [0, 2, 2, 0] [1, 1] [1, 1] [2, 2, 0, 1, 1, 0] [2, 2, 2] [0, 2, 2, 0, 1, 1] [1, 1, 1, 1] (by decide) (by decide) eq_13 eq_3) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 1, 1, 0, 1, 1] [2, 2, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 1, 0, 1, 1]
  have hb : Eqn alphabet [0, 2, 2, 0, 2, 2, 2] [0, 2, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 0, 2, 2, 2]
  exact eqn_change ![0, 1, 0, 0, 0, 0, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_459 : Eqn alphabet [2, 2, 2, 0, 2, 2, 0] [1, 1, 0, 1, 1, 0, 2, 2] ![0, (-1), 0, 0, 0, 0, 1] := by
  have h : Eqn alphabet [2, 2, 2, 0, 2, 2, 0] [1, 1, 0, 1, 1, 0, 2, 2] ![0, (-1), 0, 0, 0, 0, 1] :=
    eqn_cast [2, 2, 2, 0, 2, 2, 0] [1, 1, 0, 1, 1, 0, 2, 2] ![0, (-1), 0, 0, 0, 0, 1] (eqn_overlap_checked [1, 1] [1, 1] [0, 2, 2, 0] [2, 2, 2] [0, 1, 1, 0, 2, 2] [1, 1, 1, 1] [1, 1, 0, 2, 2, 0] (by decide) (by decide) eq_3 eq_14) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 2, 0, 2, 2, 0] [2, 2, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 2, 0]
  have hb : Eqn alphabet [1, 1, 0, 1, 1, 0, 2, 2] [1, 1, 0, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 1, 0, 2, 2]
  exact eqn_change ![0, (-1), 0, 0, 0, 0, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_460 : Eqn alphabet [1, 1, 0, 1, 1, 0, 2, 2] [2, 2, 2, 0, 2, 2, 0] ![0, 1, 0, 0, 0, 0, (-1)] := by
  exact eqn_change ![0, 1, 0, 0, 0, 0, (-1)] (eqn_symm eq_459) (by decide)

theorem eq_461 : Eqn alphabet [1, 1, 1, 0, 1, 1, 0, 2] [2, 2, 0, 2, 2, 0, 1] ![0, 1, 0, 0, 0, 0, 1] := by
  have h : Eqn alphabet [1, 1, 1, 0, 1, 1, 0, 2] [2, 2, 0, 2, 2, 0, 1] ![0, 1, 0, 0, 0, 0, 1] :=
    eqn_cast [1, 1, 1, 0, 1, 1, 0, 2] [2, 2, 0, 2, 2, 0, 1] ![0, 1, 0, 0, 0, 0, 1] (eqn_overlap_checked [2, 2] [2, 2] [0, 1, 1, 0, 2] [1, 1, 1] [0, 2, 2, 0, 1] [2, 2, 2, 2] [2, 2, 0, 1, 1, 0, 2] (by decide) (by decide) eq_4 eq_35) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1, 1, 0, 1, 1, 0, 2] [1, 1, 1, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 1, 1, 0, 2]
  have hb : Eqn alphabet [2, 2, 0, 2, 2, 0, 1] [2, 2, 0, 2, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 2, 0, 1]
  exact eqn_change ![0, 1, 0, 0, 0, 0, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_464 : Eqn alphabet [2, 0, 1, 1, 0, 1, 1] [1, 0, 2, 2, 0, 2, 2, 2] ![0, 1, 0, 0, 0, 0, (-1)] := by
  have h : Eqn alphabet [2, 0, 1, 1, 0, 1, 1] [1, 0, 2, 2, 0, 2, 2, 2] ![0, 1, 0, 0, 0, 0, (-1)] :=
    eqn_cast [2, 0, 1, 1, 0, 1, 1] [1, 0, 2, 2, 0, 2, 2, 2] ![0, 1, 0, 0, 0, 0, (-1)] (eqn_overlap_checked [1] [2] [2, 0, 1, 1, 0, 1, 1] [] [0, 2, 2, 0, 2, 2, 2] [1, 2] [2, 2, 0, 1, 1, 0, 1, 1] (by decide) (by decide) eq_1 eq_458) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 1, 0, 1, 1] [2, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 0, 1, 1]
  have hb : Eqn alphabet [1, 0, 2, 2, 0, 2, 2, 2] [1, 0, 2, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 2, 0, 2, 2, 2]
  exact eqn_change ![0, 1, 0, 0, 0, 0, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_465 : Eqn alphabet [1, 0, 2, 2, 0, 2, 2, 2] [2, 0, 1, 1, 0, 1, 1] ![0, (-1), 0, 0, 0, 0, 1] := by
  exact eqn_change ![0, (-1), 0, 0, 0, 0, 1] (eqn_symm eq_464) (by decide)

theorem eq_475 : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 2, 2] [0, 2, 0, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, (-1), 0] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 2, 2] [0, 2, 0, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, (-1), 0] :=
    eqn_cast [2, 0, 1, 0, 2, 0, 2, 2, 2] [0, 2, 0, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, (-1), 0] (eqn_overlap_checked [0, 2, 0, 1, 0] [2] [2, 2, 2] [2, 0, 1, 0, 2, 0] [1, 1, 1] [0, 2, 0, 1, 0, 2] [2, 2, 2, 2] (by decide) (by decide) eq_5 eq_4) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 2, 2] [2, 0, 1, 0, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 2, 2, 2]
  have hb : Eqn alphabet [0, 2, 0, 1, 0, 1, 1, 1] [0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 1, 1, 1]
  exact eqn_change ![0, (-1), 0, 0, 0, (-1), 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_486 : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1] [0, 2, 0, 2, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, (-1), 1] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1] [0, 2, 0, 2, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, (-1), 1] :=
    eqn_cast [2, 0, 1, 0, 2, 0, 2, 0, 1] [0, 2, 0, 2, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, (-1), 1] (eqn_overlap_checked [0, 2, 0] [1, 0, 2] [2, 0, 1] [2, 0, 1, 0, 2, 0] [2, 0, 1, 1, 0, 2] [0, 2, 0, 1, 0, 2] [1, 0, 2, 2, 0, 1] (by decide) (by decide) eq_5 eq_15) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1] [2, 0, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 2, 0, 2, 0, 1]
  have hb : Eqn alphabet [0, 2, 0, 2, 0, 1, 1, 0, 2] [0, 2, 0, 2, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 1, 1, 0, 2]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_487 : Eqn alphabet [0, 2, 0, 2, 0, 1, 1, 0, 2] [2, 0, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 1, (-1)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-1)] (eqn_symm eq_486) (by decide)


end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay
