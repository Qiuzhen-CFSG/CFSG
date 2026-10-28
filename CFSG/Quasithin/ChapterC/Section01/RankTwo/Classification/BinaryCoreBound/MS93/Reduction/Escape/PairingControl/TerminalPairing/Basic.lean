module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Paths

/-!
# The comparison subgroup for the last dual pairing

At a terminal path, critical minimality makes Z_alpha centralize every
Z-layer incident to t = alpha'-3, hence V_t. The actor Vcirc_(alpha'-2)
normalizes Z_alpha because it is in G_alpha. Its noncontainment in Q_alpha
and the genuine local centralizer equality show that their commutator is
nontrivial. This is the comparison subgroup used to identify the common
value in the final (1.7)(ii) application.

These deductions use only the terminal geometry and the earlier local
centralizer theorem, with no LocalControl or later escape conclusion.

Source: Meierfrankenfeld--Stellmacher (1993), (2.2), pp.856--857,
and the final paragraph of (4.3.2), pp.885--886.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.TerminalPairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

theorem start_Z_centralizes_edge (p : Counterexample geometry) (seed : TerminalSeed p) :
    ⁅Z R p.a, V R seed.t⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mpr
  apply Geometry.V_le_of_h_neighbors p.before_color seed.adjacent
  intro d hdt
  have hdc : color R d = false := by
    have ht := adjacent_color_ne R seed.adjacent
    have hd := adjacent_color_ne R hdt
    rw [p.before_color] at ht
    cases hh : color R d <;> cases hh' : color R seed.t <;> simp_all
  have hZd : Z R p.a ≤ Q R d := by
    apply Z_le_Q_of_dist_lt R p.a (geometry.exists_critical p.a p.color_a)
    rw [geometry.distance_constant p.a p.color_a]
    change (cosetGraph R).dist p.a d < geometry.b R
    have hdist := seed.before.2
    rw [p.distance_eq_b] at hdist
    have htri := (cosetGraph_connected R).dist_triangle
      (u := p.a) (v := seed.t) (w := d)
    have hone := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hdt))
    omega
  exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hdc)).trans
    (centralizer_le hZd)

theorem start_Z_pairing_ne_bot (source : LocalSource L R)
    (p : Counterexample geometry) (seed : TerminalSeed p) :
    ⁅Z R p.a, Vcirc R p.c⁆ ≠ ⊥ := by
  intro he
  apply seed.actor_not_le
  rw [← source.C_eq_Q geometry.radical_ne_bot p.a p.color_a]
  exact le_inf seed.actor_local
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))

omit [Finite M] in
theorem start_Z_pairing_le (p : Counterexample geometry) (seed : TerminalSeed p) :
    ⁅Z R p.a, Vcirc R p.c⁆ ≤ Z R p.a :=
  le_normalizer_iff_commutator_le_left.mp
    (seed.actor_local.trans (Z_normalized R p.a))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.TerminalPairing
