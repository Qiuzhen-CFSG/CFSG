module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.PowerIdentities.PowerChunk02

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

theorem eq_203 : Eqn alphabet [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2] [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, (-1), 2] := by
  have h : Eqn alphabet [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2] [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, (-1), 2] :=
    eqn_cast [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2] [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, (-1), 2] (seed_eqn alphabet alphabet_inverse [1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2, 0] [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2] [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2, 0] false 12 ![5, 0, 0, 0, 0, (-1), 2] (by decide) (eqn_cast [1, 0, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2, 0] [] ![5, 0, 0, 0, 0, (-1), 2] (eqn_relator alphabet_inverse eq_202) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2] [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2]
  have hb : Eqn alphabet [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2, 0] [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 2] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_204 : Eqn alphabet [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2, 0] [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 1, (-2)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-2)] (eqn_symm eq_203) (by decide)

theorem eq_209 : Eqn alphabet [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] ![(-1), 0, 0, 0, 1, (-1), 0] := by
  have h : Eqn alphabet [2, 0, 1, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0, 1] [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 1, (-1), 0] :=
    eqn_cast [2, 0, 1, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0, 1] [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 1, (-1), 0] (eqn_overlap_checked [0, 2] [0, 1, 0, 2] [0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 1, 0, 2, 0] [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] [0, 2, 0, 1, 0, 2] [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1] (by decide) (by decide) eq_5 eq_23) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] ![1, 0, 0, 0, 0, 0, 0] :=
    eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [2, 0, 1, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0, 1]) (eqn_cast [2, 0, 1, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0, 1] [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [2, 0, 1, 0, 2] [2, 0, 2, 0, 1, 0, 1] eq_0) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0]
  exact eqn_change ![(-1), 0, 0, 0, 1, (-1), 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_210 : Eqn alphabet [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0] [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] ![1, 0, 0, 0, (-1), 1, 0] := by
  exact eqn_change ![1, 0, 0, 0, (-1), 1, 0] (eqn_symm eq_209) (by decide)

theorem eq_214 : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2] [2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0] ![0, 0, 0, 0, (-1), 1, 0] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2] [2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0] ![0, 0, 0, 0, (-1), 1, 0] :=
    eqn_cast [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2] [2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0] ![0, 0, 0, 0, (-1), 1, 0] (seed_eqn alphabet alphabet_inverse [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 1] [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2] [2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0] false 11 ![6, 0, 0, 0, (-1), 1, 0] (by decide) (eqn_cast [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 1] [] ![6, 0, 0, 0, (-1), 1, 0] (eqn_relator alphabet_inverse eq_210) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2] [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2]
  have hb : Eqn alphabet [2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0] [2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, (-1), 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_215 : Eqn alphabet [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1] [1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, (-1), 1, 0] := by
  have h : Eqn alphabet [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1] [1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, (-1), 1, 0] :=
    eqn_cast [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1] [1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, (-1), 1, 0] (seed_eqn alphabet alphabet_inverse [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 1] [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1] [1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] false 24 ![6, 0, 0, 0, (-1), 1, 0] (by decide) (eqn_cast [0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 1] [] ![6, 0, 0, 0, (-1), 1, 0] (eqn_relator alphabet_inverse eq_210) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1] [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1]
  have hb : Eqn alphabet [1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] [1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, (-1), 1, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_216 : Eqn alphabet [1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1] ![0, 0, 0, 0, 1, (-1), 0] := by
  exact eqn_change ![0, 0, 0, 0, 1, (-1), 0] (eqn_symm eq_215) (by decide)

theorem eq_220 : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 1, 0, 1, 1] [1, 1, 0, 1, 1, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 1, 0, 1, 1] [1, 1, 0, 1, 1, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 1, 0, 1, 1] [1, 1, 0, 1, 1, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [1, 1, 0, 1, 1, 0, 2] [2] [2, 0, 1, 1, 0, 1, 1] [2, 2, 2, 0, 2, 2, 0] [0, 2, 2, 0, 2, 2, 2] [1, 1, 0, 1, 1, 0, 2, 2] [2, 2, 0, 1, 1, 0, 1, 1] (by decide) (by decide) eq_39 eq_37) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 1, 0, 1, 1] [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 1, 0, 1, 1]
  have hb : Eqn alphabet [1, 1, 0, 1, 1, 0, 2, 0, 2, 2, 0, 2, 2, 2] [1, 1, 0, 1, 1, 0, 2, 0, 2, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 1, 0, 2, 0, 2, 2, 0, 2, 2, 2]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_221 : Eqn alphabet [1, 1, 0, 1, 1, 0, 2, 0, 2, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_symm eq_220) (by decide)

theorem eq_226 : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 2, 2] [1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, (-1), 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 2, 2] [1, 0, 2, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2, 0] ![0, 0, 0, 0, (-1), (-1), 1] :=
    eqn_cast [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 2, 2] [1, 0, 2, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2, 0] ![0, 0, 0, 0, (-1), (-1), 1] (eqn_overlap_checked [1, 0, 2, 0, 2] [0, 2, 0, 1, 0, 1, 0] [2, 2] [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2] [2, 0, 1, 0, 1, 0, 2, 2, 0] [1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0] [0, 2, 0, 1, 0, 1, 0, 2, 2] (by decide) (by decide) eq_24 eq_51) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 2, 2] [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 2, 2]
  have hb : Eqn alphabet [1, 0, 2, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2, 0] [1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 1, (-1)] :=
    eqn_change ![0, 0, 0, 0, 0, 1, (-1)] (eqn_trans (eqn_refl alphabet [1, 0, 2, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2, 0]) (eqn_cast [1, 0, 2, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2, 0] [1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 1, (-1)] (eqn_context [1, 0, 2] [2, 0] eq_55) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, 0, 0, 0, (-1), 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_227 : Eqn alphabet [1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 2, 2] ![0, 0, 0, 0, 1, 0, 0] := by
  exact eqn_change ![0, 0, 0, 0, 1, 0, 0] (eqn_symm eq_226) (by decide)

theorem eq_235 : Eqn alphabet [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] := by
  have h : Eqn alphabet [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_cast [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_overlap_checked [2, 2] [2, 2] [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [1, 1, 1] [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 1] [2, 2, 2, 2] [2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] (by decide) (by decide) eq_4 eq_140) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2]
  have hb : Eqn alphabet [2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 1] [2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_238 : Eqn alphabet [0, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0] [1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1] ![0, 0, 0, 0, 1, (-1), (-1)] := by
  have h : Eqn alphabet [0, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0] [1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1] ![0, 0, 0, 0, 1, (-1), (-1)] :=
    eqn_cast [0, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0] [1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1] ![0, 0, 0, 0, 1, (-1), (-1)] (eqn_overlap_checked [1] [1, 0, 2, 2, 0] [2, 0, 1, 0, 1, 0, 1, 0] [0, 1, 1, 0, 2, 2] [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1] [1, 1, 0, 2, 2, 0] [1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] (by decide) (by decide) eq_9 eq_216) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0] [0, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0]
  have hb : Eqn alphabet [1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1] [1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 1, (-1), (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_239 : Eqn alphabet [1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1] [0, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, (-1), 1, 1] := by
  exact eqn_change ![0, 0, 0, 0, (-1), 1, 1] (eqn_symm eq_238) (by decide)

theorem eq_241 : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] [2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 1, 0, 0] := by
  have h : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] [2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 1, 0, 0] :=
    eqn_cast [0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] [2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 1, 0, 0] (seed_eqn alphabet alphabet_inverse [1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0] [0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] [2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] false 7 ![6, 0, 0, 0, 1, 0, 0] (by decide) (eqn_cast [1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0] [] ![6, 0, 0, 0, 1, 0, 0] (eqn_relator alphabet_inverse eq_227) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] [0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2]
  have hb : Eqn alphabet [2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] [2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 1, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_252 : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] [0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, (-1), 1, 1] := by
  have h : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] [0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, (-1), 1, 1] :=
    eqn_cast [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] [0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, (-1), 1, 1] (seed_eqn alphabet alphabet_inverse [1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 0] [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] [0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1] false 11 ![6, 0, 0, 0, (-1), 1, 1] (by decide) (eqn_cast [1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 0] [] ![6, 0, 0, 0, (-1), 1, 1] (eqn_relator alphabet_inverse eq_239) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0]
  have hb : Eqn alphabet [0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1] [0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1]
  exact eqn_change ![0, 0, 0, 0, (-1), 1, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_253 : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2] [2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, (-1), 1, 1] := by
  have h : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2] [2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, (-1), 1, 1] :=
    eqn_cast [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2] [2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, (-1), 1, 1] (seed_eqn alphabet alphabet_inverse [1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 0] [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2] [2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1] false 12 ![6, 0, 0, 0, (-1), 1, 1] (by decide) (eqn_cast [1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 0] [] ![6, 0, 0, 0, (-1), 1, 1] (eqn_relator alphabet_inverse eq_239) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2] [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2]
  have hb : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1] [2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, (-1), 1, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_255 : Eqn alphabet [2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] [0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, (-1), 1, 1] := by
  have h : Eqn alphabet [2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] [0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, (-1), 1, 1] :=
    eqn_cast [2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] [0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, (-1), 1, 1] (seed_eqn alphabet alphabet_inverse [1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 0] [2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] [0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2] false 25 ![6, 0, 0, 0, (-1), 1, 1] (by decide) (eqn_cast [1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 0] [] ![6, 0, 0, 0, (-1), 1, 1] (eqn_relator alphabet_inverse eq_239) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] [2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0]
  have hb : Eqn alphabet [0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2] [0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2]
  exact eqn_change ![0, 0, 0, 0, (-1), 1, 1] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_256 : Eqn alphabet [0, 2, 2, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2] [2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 1, (-1), (-1)] := by
  exact eqn_change ![0, 0, 0, 0, 1, (-1), (-1)] (eqn_symm eq_255) (by decide)

theorem eq_261 : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] ![(-5), 0, 1, 0, 1, 0, 0] := by
  have h : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] ![(-5), 0, 1, 0, 1, 0, 0] :=
    eqn_cast [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] ![(-5), 0, 1, 0, 1, 0, 0] (eqn_overlap_checked [2, 0, 2] [0, 2, 0, 2, 0, 2, 0] [1, 0, 1, 0, 1] [0, 1, 0, 1, 0, 1, 0, 1] [2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] [2, 0, 2, 0, 2, 0, 2, 0, 2, 0] [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1] (by decide) (by decide) eq_17 eq_19) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1]
  have hb : Eqn alphabet [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0]
  exact eqn_change ![(-5), 0, 1, 0, 1, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_262 : Eqn alphabet [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0] [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] ![5, 0, (-1), 0, (-1), 0, 0] := by
  exact eqn_change ![5, 0, (-1), 0, (-1), 0, 0] (eqn_symm eq_261) (by decide)

theorem eq_264 : Eqn alphabet [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2] [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] ![4, 0, (-1), 0, (-1), 0, 0] := by
  have h : Eqn alphabet [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2] [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] ![4, 0, (-1), 0, (-1), 0, 0] :=
    eqn_cast [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2] [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] ![4, 0, (-1), 0, (-1), 0, 0] (seed_eqn alphabet alphabet_inverse [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0] [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2] [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] false 9 ![11, 0, (-1), 0, (-1), 0, 0] (by decide) (eqn_cast [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0] [] ![11, 0, (-1), 0, (-1), 0, 0] (eqn_relator alphabet_inverse eq_262) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2] [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2]
  have hb : Eqn alphabet [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]
  exact eqn_change ![4, 0, (-1), 0, (-1), 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_265 : Eqn alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0] [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] ![5, 0, (-1), 0, (-1), 0, 0] := by
  have h : Eqn alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0] [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] ![5, 0, (-1), 0, (-1), 0, 0] :=
    eqn_cast [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0] [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] ![5, 0, (-1), 0, (-1), 0, 0] (seed_eqn alphabet alphabet_inverse [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0] [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] false 10 ![11, 0, (-1), 0, (-1), 0, 0] (by decide) (eqn_cast [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0] [] ![11, 0, (-1), 0, (-1), 0, 0] (eqn_relator alphabet_inverse eq_262) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0] [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0]
  have hb : Eqn alphabet [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1]
  exact eqn_change ![5, 0, (-1), 0, (-1), 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_270 : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0] [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] ![5, 0, (-1), 0, (-1), 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0] [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] ![5, 0, (-1), 0, (-1), 0, 0] :=
    eqn_cast [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0] [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] ![5, 0, (-1), 0, (-1), 0, 0] (seed_eqn alphabet alphabet_inverse [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0] [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0] [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] false 23 ![11, 0, (-1), 0, (-1), 0, 0] (by decide) (eqn_cast [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0] [] ![11, 0, (-1), 0, (-1), 0, 0] (eqn_relator alphabet_inverse eq_262) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0] [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0]
  have hb : Eqn alphabet [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2]
  exact eqn_change ![5, 0, (-1), 0, (-1), 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_271 : Eqn alphabet [1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2] [0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0] ![(-5), 0, 1, 0, 1, 0, 0] := by
  exact eqn_change ![(-5), 0, 1, 0, 1, 0, 0] (eqn_symm eq_270) (by decide)

theorem eq_274 : Eqn alphabet [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0] [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2] ![5, 0, (-1), 0, (-1), 0, 0] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0] [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2] ![5, 0, (-1), 0, (-1), 0, 0] :=
    eqn_cast [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0] [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2] ![5, 0, (-1), 0, (-1), 0, 0] (seed_eqn alphabet alphabet_inverse [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0] [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0] [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2] false 25 ![11, 0, (-1), 0, (-1), 0, 0] (by decide) (eqn_cast [2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0] [] ![11, 0, (-1), 0, (-1), 0, 0] (eqn_relator alphabet_inverse eq_262) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0] [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0]
  have hb : Eqn alphabet [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2] [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2]
  exact eqn_change ![5, 0, (-1), 0, (-1), 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_275 : Eqn alphabet [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2] [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0] ![(-5), 0, 1, 0, 1, 0, 0] := by
  exact eqn_change ![(-5), 0, 1, 0, 1, 0, 0] (eqn_symm eq_274) (by decide)

theorem eq_283 : Eqn alphabet [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0] [1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] ![1, 0, 0, 0, (-1), 0, 0] := by
  have h : Eqn alphabet [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0] [1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] ![1, 0, 0, 0, (-1), 0, 0] :=
    eqn_cast [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0] [1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] ![1, 0, 0, 0, (-1), 0, 0] (eqn_overlap_checked [1] [0, 2, 0, 1, 0] [1, 0, 1, 0, 2, 0, 2, 2, 0] [0, 1, 0, 2, 0, 1] [1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] [1, 0, 2, 0, 1, 0] [0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0] (by decide) (by decide) eq_6 eq_196) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0] [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0]
  have hb : Eqn alphabet [1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] [1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2]
  exact eqn_change ![1, 0, 0, 0, (-1), 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_284 : Eqn alphabet [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0] [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] ![0, 0, 0, 0, (-1), 0, 0] := by
  have h : Eqn alphabet [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0] [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] ![0, 0, 0, 0, (-1), 0, 0] :=
    eqn_cast [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0] [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] ![0, 0, 0, 0, (-1), 0, 0] (eqn_overlap_checked [0] [0] [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0] [] [1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] [0, 0] [0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0] (by decide) (by decide) eq_0 eq_283) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0] [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0]
  have hb : Eqn alphabet [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2]
  exact eqn_change ![0, 0, 0, 0, (-1), 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_295 : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] [0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] ![(-1), 0, 0, 0, 1, 0, 0] := by
  have h : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] [0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] ![(-1), 0, 0, 0, 1, 0, 0] :=
    eqn_cast [1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] [0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] ![(-1), 0, 0, 0, 1, 0, 0] (eqn_overlap_checked [0] [0] [1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] [] [2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] [0, 0] [0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] (by decide) (by decide) eq_0 eq_241) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] [1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2]
  have hb : Eqn alphabet [0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] [0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![(-1), 0, 0, 0, 1, 0, 0] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_296 : Eqn alphabet [0, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] [1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] ![1, 0, 0, 0, (-1), 0, 0] := by
  exact eqn_change ![1, 0, 0, 0, (-1), 0, 0] (eqn_symm eq_295) (by decide)

theorem eq_297 : Eqn alphabet [0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2] [2, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 1, 1, (-1)] := by
  have h : Eqn alphabet [0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2] [2, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 1, 1, (-1)] :=
    eqn_cast [0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2] [2, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 1, 1, (-1)] (eqn_overlap_checked [2] [0, 1, 0, 2, 0, 2, 0, 1, 1] [1, 0, 2, 0, 2] [0, 2, 0, 2, 0, 1, 1, 0] [2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] [2, 0, 1, 0, 2, 0, 2, 0, 1, 1] [0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 0, 2] (by decide) (by decide) eq_63 eq_241) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2] [0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2]
  have hb : Eqn alphabet [2, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] [2, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 1, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 1, 1, (-1)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)


end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay.PowerCertificate
