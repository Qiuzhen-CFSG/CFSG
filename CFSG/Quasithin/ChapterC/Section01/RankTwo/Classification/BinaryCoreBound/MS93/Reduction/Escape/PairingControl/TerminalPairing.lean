module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.TerminalPairing.Application
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.TerminalPairing.Basic

/-!
# Assembly of the last pairing in MS93 (4.3.2)

The pairing is applied inside the finite stabilizer at c = alpha'-2,
with W = Q_c. Both Vcirc_alpha and Z_alpha lie in W and centralize the
selected seed in V_t. The earlier local-centralizer theorem makes the
Z_alpha pairing nonzero. Thus (1.7)(ii) identifies its value with the
fixed subgroup and bounds the Vcirc_alpha pairing by the same subgroup.
Mapping out of the finite stabilizer gives precisely the source chain
[Vcirc_alpha,Vcirc_c] <= [Z_alpha,Vcirc_c] <= Z_alpha.

`terminal_pairing_chain_of_pairing` performs this application and transport.
The geometric `EdgeSeedAt` and finite `CorePairing` constructors remain
explicit obligations. Until both are constructed from the task's original
inputs, this module does not assert the unconditional terminal bound.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(ii), pp.847--848,
and the last paragraph of (4.3.2), pp.885--886.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl
open RankOnePairing TerminalPairing

private theorem subgroupOf_centralizes_seed {G : Type*} [Group G]
    (S A E : Subgroup G) (X : Subgroup S) (hX : X ≤ E.subgroupOf S)
    (hc : ⁅A, E⁆ = ⊥) : A.subgroupOf S ≤ centralizer (X : Set S) := by
  intro a ha x hx
  apply Subtype.ext
  exact (commutator_eq_bot_iff_le_centralizer.mp hc ha) (x : G) (hX hx)

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- The exact printed chain, conditional on the two remaining constructions.
All uses of (1.7)(ii), the comparison element, and ambient transport are proved. -/
theorem terminal_pairing_chain_of_pairing (source : LocalSource L R)
    (p : Counterexample geometry) (seed : TerminalSeed p)
    (edge : EdgeSeedAt source p.c seed.t p.before_color) (pairing : edge.Pairing) :
    ⁅Vcirc R p.a, Vcirc R p.c⁆ ≤ ⁅Z R p.a, Vcirc R p.c⁆ ∧
      ⁅Z R p.a, Vcirc R p.c⁆ ≤ Z R p.a := by
  let S := stabilizer R p.c
  let : Finite S := finite_stabilizer R p.c
  have hQc : Q R p.c ≤ S := fun _ hx => hx.1
  have hA : Vcirc R p.a ≤ Q R p.c := (Geometry.Vcirc_le_V p.a).trans p.trapped
  have hB : Z R p.a ≤ Q R p.c := (Z_le_VBall R p.a 2).trans p.trapped
  have hJ : Vcirc R p.c ≤ S := ((Geometry.Vcirc_le_V p.c).trans
    (geometry.V_le_Q (by have := seed.six_lt; omega) p.c p.before_color)).trans hQc
  have hcore : extensionCore edge.extension.projection = (Q R p.c).subgroupOf S :=
    vertexExtension_core source p.c p.before_color edge.opposite edge.flag edge.weakBN
  have hAc : (Vcirc R p.a).subgroupOf S ≤ extensionCore edge.extension.projection ⊓
      centralizer (canonicalSeed edge.extension edge.opposite.dual edge.side : Set S) := by
    refine le_inf ?_ (subgroupOf_centralizes_seed S _ _ _ edge.seed_le_edge seed.edge_centralizes)
    rw [hcore]
    exact fun _ hx => hA hx
  have hBc : (Z R p.a).subgroupOf S ≤ extensionCore edge.extension.projection ⊓
      centralizer (canonicalSeed edge.extension edge.opposite.dual edge.side : Set S) := by
    refine le_inf ?_ (subgroupOf_centralizes_seed S _ _ _ edge.seed_le_edge
      (start_Z_centralizes_edge p seed))
    rw [hcore]
    exact fun _ hx => hB hx
  have hn : ⁅generated (canonicalSeed edge.extension edge.opposite.dual edge.side),
      (Z R p.a).subgroupOf S⁆ ≠ ⊥ := by
    intro he
    have hm := congrArg (Subgroup.map S.subtype) he
    rw [pairing.generated_eq, map_commutator, map_subgroupOf_eq_of_le hJ,
      map_subgroupOf_eq_of_le (hB.trans hQc), Subgroup.map_bot, commutator_comm] at hm
    exact start_Z_pairing_ne_bot source p seed hm
  have hp := subgroup_comparison pairing.data edge.fixed_bot pairing.natural_quotient hAc hBc hn
  rw [pairing.generated_eq] at hp
  have hm := map_mono (f := S.subtype) hp
  rw [map_commutator, map_commutator, map_subgroupOf_eq_of_le hJ,
    map_subgroupOf_eq_of_le (hA.trans hQc), map_subgroupOf_eq_of_le (hB.trans hQc),
    commutator_comm (Vcirc R p.c) (Vcirc R p.a),
    commutator_comm (Vcirc R p.c) (Z R p.a)] at hm
  exact ⟨hm, start_Z_pairing_le p seed⟩

/-- The bound needed by `terminal_contradiction`, after the actual seed and
pairing inputs have been constructed. -/
theorem terminal_pairing_bound_of_pairing (source : LocalSource L R)
    (p : Counterexample geometry) (seed : TerminalSeed p)
    (edge : EdgeSeedAt source p.c seed.t p.before_color) (pairing : edge.Pairing) :
    ⁅Vcirc R p.a, Vcirc R p.c⁆ ≤ Z R p.a := by
  obtain ⟨h₁, h₂⟩ := terminal_pairing_chain_of_pairing source p seed edge pairing
  exact h₁.trans h₂

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl
