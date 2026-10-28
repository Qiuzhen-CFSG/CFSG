module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.PowerIdentities.PowerChunk04

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

theorem eq_530 : Eqn alphabet [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-1), 2] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 2] (eqn_symm eq_529) (by decide)

private theorem reduce_531_a_0 : Eqn alphabet [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 1, 0] ![7, 1, (-1), 0, 0, 0, 1] :=
  eqn_change ![7, 1, (-1), 0, 0, 0, 1] (eqn_trans (eqn_change ![6, 1, (-1), 0, 0, 0, 1] (eqn_trans (eqn_change ![6, 1, (-1), 0, 0, 0, 1] (eqn_trans (eqn_change ![5, 1, (-1), 0, 0, 0, 1] (eqn_trans (eqn_change ![5, 1, (-1), 0, 0, (-1), 1] (eqn_trans (eqn_change ![5, 1, (-1), 0, 0, (-1), 1] (eqn_trans (eqn_change ![0, 1, 0, 0, 0, (-1), 2] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, (-1), 2] (eqn_trans (eqn_refl alphabet [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0]) (eqn_cast [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 2] (eqn_context [] [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] eq_530) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] ![0, 1, 0, 0, 0, 0, 0] (eqn_context [0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0] [0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] eq_3) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] ![5, 0, (-1), 0, 0, 0, (-1)] (eqn_context [0, 1, 0, 1, 1] [2, 0, 2, 0, 2, 0, 1, 1, 1, 0] eq_188) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [0, 2, 0, 2, 0, 1, 1, 1, 0] eq_1) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, 1, 0] (eqn_context [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0] [2, 0, 2, 0, 1, 1, 1, 0] eq_6) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 1, 1, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [0, 1, 0, 1, 1, 1, 0, 1, 0, 1] [1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 1, 1, 0] eq_0) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 0, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0] [0, 2, 0, 1, 1, 1, 0] eq_1) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 0, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 1, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2] [2, 0, 1, 1, 1, 0] eq_0) (by decide) (by decide) (by decide))) (by decide)

private theorem reduce_531_a_1 : Eqn alphabet [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] ![1, 0, 0, 0, 0, 0, 1] :=
  eqn_change ![1, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_refl alphabet [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 1, 0]) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 2, 2, 1, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 1] (eqn_context [0, 1, 0, 1, 1, 1, 0, 1, 0] [1, 1, 1, 0] eq_9) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 2, 2, 1, 1, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 2, 2, 1, 1, 1, 0] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [0, 1, 0, 1, 1, 1, 0, 1] [1, 1, 0, 2, 2, 1, 1, 1, 0] eq_0) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 2, 2, 1, 1, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 2, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 2] [1, 1, 0] eq_2) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 2, 1, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0] [1, 0] eq_2) (by decide) (by decide) (by decide))) (by decide)

private theorem reduce_531_b_0 : Eqn alphabet [0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 0, 2, 0, 1, 1, 1] ![7, 1, (-1), 0, 0, 0, 1] :=
  eqn_change ![7, 1, (-1), 0, 0, 0, 1] (eqn_trans (eqn_change ![7, 1, (-1), 0, 0, 0, 1] (eqn_trans (eqn_change ![6, 1, (-1), 0, 0, 0, 1] (eqn_trans (eqn_change ![6, 1, (-1), 0, 0, (-1), 1] (eqn_trans (eqn_change ![6, 1, (-1), 0, 0, (-1), 1] (eqn_trans (eqn_change ![1, 1, 0, 0, 0, (-1), 2] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, (-1), 2] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, (-1), 2] (eqn_trans (eqn_refl alphabet [0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1]) (eqn_cast [0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] [0, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-1), 2] (eqn_context [0] [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] eq_530) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [] [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] eq_0) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] ![0, 1, 0, 0, 0, 0, 0] (eqn_context [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0] [0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] eq_3) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] [1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1, 2, 0, 2, 0, 2, 0, 1, 1, 1] ![5, 0, (-1), 0, 0, 0, (-1)] (eqn_context [1, 0, 1, 1] [2, 0, 2, 0, 2, 0, 1, 1, 1] eq_188) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1, 2, 0, 2, 0, 2, 0, 1, 1, 1] [1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1] [0, 2, 0, 2, 0, 1, 1, 1] eq_1) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 1] [1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 1, 0] (eqn_context [1, 0, 1, 1, 1, 0, 1, 0, 1, 0] [2, 0, 2, 0, 1, 1, 1] eq_6) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 1, 1] [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 1, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [1, 0, 1, 1, 1, 0, 1, 0, 1] [1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 1, 1] eq_0) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 1, 1] [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 0, 2, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0] [0, 2, 0, 1, 1, 1] eq_1) (by decide) (by decide) (by decide))) (by decide)

private theorem reduce_531_b_1 : Eqn alphabet [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 0, 2, 0, 1, 1, 1] [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] ![2, 0, 0, 0, 0, 0, 1] :=
  eqn_change ![2, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_change ![2, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_change ![2, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 1] (eqn_trans (eqn_change ![1, 0, 0, 0, 0, 0, 0] (eqn_trans (eqn_refl alphabet [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 0, 2, 0, 1, 1, 1]) (eqn_cast [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 0, 2, 0, 1, 1, 1] [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2] [2, 0, 1, 1, 1] eq_0) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 1] [1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 2, 2, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 1] (eqn_context [1, 0, 1, 1, 1, 0, 1, 0] [1, 1, 1] eq_9) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 2, 2, 1, 1, 1] [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 2, 2, 1, 1, 1] ![1, 0, 0, 0, 0, 0, 0] (eqn_context [1, 0, 1, 1, 1, 0, 1] [1, 1, 0, 2, 2, 1, 1, 1] eq_0) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 2, 2, 1, 1, 1] [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 2, 1, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 2] [1, 1] eq_2) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 2, 1, 1] [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] (eqn_context [1, 0, 1, 1, 1, 0, 1, 1, 1, 0] [1] eq_2) (by decide) (by decide) (by decide))) (by decide)

theorem eq_531 : Eqn alphabet [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] ![1, 0, 0, 0, 0, (-2), 4] := by
  have h : Eqn alphabet [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] :=
    eqn_cast [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] (eqn_power eq_530 2) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] ![8, 1, (-1), 0, 0, 0, 2] :=
    eqn_change ![8, 1, (-1), 0, 0, 0, 2] (eqn_trans (eqn_change ![7, 1, (-1), 0, 0, 0, 1] (eqn_trans (eqn_refl alphabet [1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0]) reduce_531_a_0) (by decide)) reduce_531_a_1) (by decide)
  have hb : Eqn alphabet [0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1] [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] ![9, 1, (-1), 0, 0, 0, 2] :=
    eqn_change ![9, 1, (-1), 0, 0, 0, 2] (eqn_trans (eqn_change ![7, 1, (-1), 0, 0, 0, 1] (eqn_trans (eqn_refl alphabet [0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 1]) reduce_531_b_0) (by decide)) reduce_531_b_1) (by decide)
  exact eqn_change ![1, 0, 0, 0, 0, (-2), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_532 : Eqn alphabet [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 2, (-4)] := by
  have h : Eqn alphabet [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 2, (-4)] :=
    eqn_cast [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 2, (-4)] (eqn_overlap_checked [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] [0] [0] [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] [] [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] [0, 0] (by decide) (by decide) eq_531 eq_0) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0]
  have hb : Eqn alphabet [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-4)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_534 : Eqn alphabet [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0] [0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] := by
  have h : Eqn alphabet [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0] [0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] :=
    eqn_cast [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0] [0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] (seed_eqn alphabet alphabet_inverse [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0] [0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1] false 3 ![4, 0, 0, 0, 0, (-2), 4] (by decide) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [] ![4, 0, 0, 0, 0, (-2), 4] (eqn_relator alphabet_inverse eq_531) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0] [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0]
  have hb : Eqn alphabet [0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1] [0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-2), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_535 : Eqn alphabet [1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] := by
  have h : Eqn alphabet [1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] :=
    eqn_cast [1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] (seed_eqn alphabet alphabet_inverse [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1] false 4 ![4, 0, 0, 0, 0, (-2), 4] (by decide) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [] ![4, 0, 0, 0, 0, (-2), 4] (eqn_relator alphabet_inverse eq_531) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2]
  have hb : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-2), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_537 : Eqn alphabet [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, (-1), 4] := by
  have h : Eqn alphabet [0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, (-2), 4] :=
    eqn_cast [0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, (-2), 4] (seed_eqn alphabet alphabet_inverse [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0] false 6 ![4, 0, 0, 0, 0, (-2), 4] (by decide) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [] ![4, 0, 0, 0, 0, (-2), 4] (eqn_relator alphabet_inverse eq_531) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-1), 0] :=
    eqn_change ![0, 0, 0, 0, 0, (-1), 0] (eqn_trans (eqn_refl alphabet [0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2]) (eqn_cast [0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2] [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-1), 0] (eqn_context [0] [] eq_81) (by decide) (by decide) (by decide))) (by decide)
  have hb : Eqn alphabet [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0] [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_539 : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2] [2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, (-2), 4] := by
  have h : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2] [2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, (-2), 4] :=
    eqn_cast [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2] [2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, (-2), 4] (seed_eqn alphabet alphabet_inverse [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2] [2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] false 9 ![4, 0, 0, 0, 0, (-2), 4] (by decide) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [] ![4, 0, 0, 0, 0, (-2), 4] (eqn_relator alphabet_inverse eq_531) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2] [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2]
  have hb : Eqn alphabet [2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] [2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-2), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_540 : Eqn alphabet [0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, (-2), 4] := by
  have h : Eqn alphabet [0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, (-2), 4] :=
    eqn_cast [0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, (-2), 4] (seed_eqn alphabet alphabet_inverse [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] false 10 ![4, 0, 0, 0, 0, (-2), 4] (by decide) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [] ![4, 0, 0, 0, 0, (-2), 4] (eqn_relator alphabet_inverse eq_531) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2] [0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2]
  have hb : Eqn alphabet [2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] [2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, (-2), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_541 : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, (-2), 4] := by
  have h : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, (-2), 4] :=
    eqn_cast [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, (-2), 4] (seed_eqn alphabet alphabet_inverse [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1] false 11 ![4, 0, 0, 0, 0, (-2), 4] (by decide) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [] ![4, 0, 0, 0, 0, (-2), 4] (eqn_relator alphabet_inverse eq_531) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0]
  have hb : Eqn alphabet [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1] [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-2), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_542 : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, (-2), 4] := by
  have h : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, (-2), 4] :=
    eqn_cast [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, (-2), 4] (seed_eqn alphabet alphabet_inverse [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0] false 12 ![4, 0, 0, 0, 0, (-2), 4] (by decide) (eqn_cast [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [] ![4, 0, 0, 0, 0, (-2), 4] (eqn_relator alphabet_inverse eq_531) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2]
  have hb : Eqn alphabet [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0] [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, (-2), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_543 : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-1), 4] := by
  have h : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-1), 4] :=
    eqn_cast [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-1), 4] (seed_eqn alphabet alphabet_inverse [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] false 2 ![4, 0, 0, 0, 0, (-1), 4] (by decide) (eqn_cast [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [] ![4, 0, 0, 0, 0, (-1), 4] (eqn_relator alphabet_inverse eq_537) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2]
  have hb : Eqn alphabet [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_544 : Eqn alphabet [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] ![0, 0, 0, 0, 0, 1, (-4)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-4)] (eqn_symm eq_543) (by decide)

theorem eq_545 : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, (-1), 4] := by
  have h : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, (-1), 4] :=
    eqn_cast [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, (-1), 4] (seed_eqn alphabet alphabet_inverse [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] false 3 ![4, 0, 0, 0, 0, (-1), 4] (by decide) (eqn_cast [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [] ![4, 0, 0, 0, 0, (-1), 4] (eqn_relator alphabet_inverse eq_537) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2]
  have hb : Eqn alphabet [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_546 : Eqn alphabet [1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 1, (-4)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-4)] (eqn_symm eq_545) (by decide)

theorem eq_549 : Eqn alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, (-1), 4] := by
  have h : Eqn alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, (-1), 4] :=
    eqn_cast [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, (-1), 4] (seed_eqn alphabet alphabet_inverse [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] false 5 ![4, 0, 0, 0, 0, (-1), 4] (by decide) (eqn_cast [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [] ![4, 0, 0, 0, 0, (-1), 4] (eqn_relator alphabet_inverse eq_537) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0]
  have hb : Eqn alphabet [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_550 : Eqn alphabet [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, 1, (-4)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-4)] (eqn_symm eq_549) (by decide)

theorem eq_551 : Eqn alphabet [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, (-1), 4] := by
  have h : Eqn alphabet [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, (-1), 4] :=
    eqn_cast [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, (-1), 4] (seed_eqn alphabet alphabet_inverse [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] false 6 ![4, 0, 0, 0, 0, (-1), 4] (by decide) (eqn_cast [0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1, 1] [] ![4, 0, 0, 0, 0, (-1), 4] (eqn_relator alphabet_inverse eq_537) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2]
  have hb : Eqn alphabet [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_552 : Eqn alphabet [1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] [0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 1, (-4)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-4)] (eqn_symm eq_551) (by decide)

theorem eq_553 : Eqn alphabet [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] [2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 2, (-4)] := by
  have h : Eqn alphabet [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] [2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 2, (-4)] :=
    eqn_cast [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] [2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 2, (-4)] (eqn_overlap_checked [2] [1] [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] [] [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] [2, 1] [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] (by decide) (by decide) eq_2 eq_532) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0]
  have hb : Eqn alphabet [2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] [2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-4)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_554 : Eqn alphabet [2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] ![0, 0, 0, 0, 0, (-2), 4] := by
  exact eqn_change ![0, 0, 0, 0, 0, (-2), 4] (eqn_symm eq_553) (by decide)

theorem eq_559 : Eqn alphabet [1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] := by
  have h : Eqn alphabet [1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] :=
    eqn_cast [1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, (-2), 4] (eqn_overlap_checked [2] [1] [1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [] [2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1] [2, 1] [1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] (by decide) (by decide) eq_2 eq_535) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] [1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2]
  have hb : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-2), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_560 : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1] [1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2] ![0, 0, 0, 0, 0, 2, (-4)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-4)] (eqn_symm eq_559) (by decide)

theorem eq_568 : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2] [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![(-1), 0, 0, 0, 0, (-2), 4] := by
  have h : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2] [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![(-1), 0, 0, 0, 0, (-2), 4] :=
    eqn_cast [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2] [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![(-1), 0, 0, 0, 0, (-2), 4] (eqn_overlap_checked [0] [0] [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2] [] [2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] [0, 0] [0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2] (by decide) (by decide) eq_0 eq_540) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2] [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2]
  have hb : Eqn alphabet [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0]
  exact eqn_change ![(-1), 0, 0, 0, 0, (-2), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_569 : Eqn alphabet [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0] [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2] ![1, 0, 0, 0, 0, 2, (-4)] := by
  exact eqn_change ![1, 0, 0, 0, 0, 2, (-4)] (eqn_symm eq_568) (by decide)

theorem eq_570 : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, (-2), 4] := by
  have h : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, (-2), 4] :=
    eqn_cast [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, (-2), 4] (eqn_overlap_checked [2] [1] [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] [] [0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1] [2, 1] [1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] (by decide) (by decide) eq_2 eq_541) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0]
  have hb : Eqn alphabet [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1] [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-2), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_571 : Eqn alphabet [2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1] [0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0] ![0, 0, 0, 0, 0, 2, (-4)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 2, (-4)] (eqn_symm eq_570) (by decide)

theorem eq_572 : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, (-1), 4] := by
  have h : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, (-1), 4] :=
    eqn_cast [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, (-1), 4] (eqn_overlap_checked [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] [1] [2] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2] [] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1, 1] [1, 2] (by decide) (by decide) eq_544 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 0, 2, 0, 1, 0, 1, 1, 1, 0, 2, 2]
  have hb : Eqn alphabet [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 2, 2, 0, 2, 0, 1, 0, 1]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_575 : Eqn alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, (-1), 4] := by
  have h : Eqn alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, (-1), 4] :=
    eqn_cast [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, (-1), 4] (eqn_overlap_checked [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] [1] [2] [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0] [] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1] [1, 2] (by decide) (by decide) eq_550 eq_1) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2]
  have hb : Eqn alphabet [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 0]
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_576 : Eqn alphabet [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] ![0, 0, 0, 0, 0, (-1), 4] := by
  have h : Eqn alphabet [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] [1, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, (-2), 4] :=
    eqn_cast [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] [1, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1] ![0, (-1), 0, 0, 0, (-2), 4] (eqn_overlap_checked [1] [1, 1, 1] [0, 1, 1, 1, 0, 1, 0, 2, 0] [2, 2, 2] [0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1] [1, 1, 1, 1] [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0] (by decide) (by decide) eq_3 eq_534) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0]
  have hb : Eqn alphabet [1, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1] [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] ![0, 1, 0, 0, 0, 1, 0] :=
    eqn_change ![0, 1, 0, 0, 0, 1, 0] (eqn_trans (eqn_change ![0, 0, 0, 0, 0, 1, 0] (eqn_trans (eqn_refl alphabet [1, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]) (eqn_cast [1, 0, 2, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1] [0, 1, 0, 2, 0, 1, 1, 1, 1, 0, 1, 1, 1] ![0, 0, 0, 0, 0, 1, 0] (eqn_context [] [1, 1, 1, 0, 1, 1, 1] eq_6) (by decide) (by decide) (by decide))) (by decide)) (eqn_cast [0, 1, 0, 2, 0, 1, 1, 1, 1, 0, 1, 1, 1] [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] ![0, 1, 0, 0, 0, 0, 0] (eqn_context [0, 1, 0, 2, 0] [0, 1, 1, 1] eq_3) (by decide) (by decide) (by decide))) (by decide)
  exact eqn_change ![0, 0, 0, 0, 0, (-1), 4] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_577 : Eqn alphabet [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0] ![0, 0, 0, 0, 0, 1, (-4)] := by
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-4)] (eqn_symm eq_576) (by decide)

theorem eq_578 : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 1, (-4)] := by
  have h : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 1, (-4)] :=
    eqn_cast [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 1, (-4)] (seed_eqn alphabet alphabet_inverse [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] false 1 ![4, 0, 0, 0, 0, 1, (-4)] (by decide) (eqn_cast [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [] ![4, 0, 0, 0, 0, 1, (-4)] (eqn_relator alphabet_inverse eq_577) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0]
  have hb : Eqn alphabet [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2]
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-4)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)

theorem eq_579 : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 1, (-4)] := by
  have h : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 1, (-4)] :=
    eqn_cast [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 1, (-4)] (seed_eqn alphabet alphabet_inverse [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] false 2 ![4, 0, 0, 0, 0, 1, (-4)] (by decide) (eqn_cast [0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0, 2, 0, 2, 2, 2, 0, 1, 1, 1] [] ![4, 0, 0, 0, 0, 1, (-4)] (eqn_relator alphabet_inverse eq_577) (by decide) (by decide) (by decide))) (by decide) (by decide) (by decide)
  have ha : Eqn alphabet [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [0, 2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1]
  have hb : Eqn alphabet [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0] ![0, 0, 0, 0, 0, 0, 0] :=
    eqn_refl alphabet [2, 0, 2, 2, 2, 0, 1, 1, 1, 0, 1, 0]
  exact eqn_change ![0, 0, 0, 0, 0, 1, (-4)] (eqn_trans (eqn_trans (eqn_symm ha) h) hb) (by decide)


end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay.PowerCertificate
