module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Basic

/-!
# Intermediate conclusions for the contradiction in MS93 (4.3.2)

The first pairing excludes the same natural-module orientation for U and
the moving section of V. Under the contrary commutator assumption, step (3)
identifies H with U, determines the order of Vcirc, and gives symmetry and
edge displacement identities for moving neighbors. `ContraryLocalFacts`
records precisely these intermediate conclusions, including actual dual
coordinates on Vcirc/U relative to natural coordinates on U.

Steps (4)--(6) change the critical path and bound the subgroup generated
under the chosen local normalizer. Their final geometric output is a
predecessor t at distance three from the endpoint, whose V-layer commutes
with Vcirc at the start. The endpoint-side Vcirc is an actor in the start
stabilizer, but is outside its two-core. This is `TerminalSeed`.
The geometric producer may select a new contrary critical configuration;
it need not preserve the original endpoint or silently identify its path.

Neither structure is constructed here, and neither is a new hypothesis of
the source theorem. The final pairing must still be constructed and applied
to this seed. Its commutator bound, together with the faithful natural
section, gives the contradiction. These definitions allow the independent
source branches to be proved with explicit intermediate inputs.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2), printed pp.883--886.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl
variable {M : Type*} [Group M] {R : Subgroup M}

/-- Actual opposite natural sections inside one finite vertex stabilizer.
The coordinates on Vcirc have kernel exactly U, and their action is dual
to the coordinates on U for the same marked SL3 quotient. -/
structure OppositeSectionAt (a : Vertex R) where
  projection : stabilizer R a →* SL
  surjective : Function.Surjective projection
  kernel : projection.ker = (Q R a).subgroupOf (stabilizer R a)
  naturalU : RankOnePairing.NaturalFactor projection ⊤
    ((U R a).subgroupOf (stabilizer R a)) ⊥
  dual : RankOnePairing.DualFactor projection ⊤
    ((Vcirc R a).subgroupOf (stabilizer R a))
    ((U R a).subgroupOf (stabilizer R a))
    ((U R a).subgroupOf (stabilizer R a)) naturalU

/-- The conclusions of the first pairing and step (3), transported to
arbitrary vertices and incident edges using the actual amalgam action. -/
structure ContraryLocalFacts (geometry : Geometry R) : Prop where
  opposite : ∀ a, color R a = false → Nonempty (OppositeSectionAt a)
  H_eq_U : ∀ a, color R a = false → H R a = U R a
  moving_card : ∀ a, color R a = false → Nat.card (Vcirc R a) = 64
  edge_eq : ∀ a t d, color R a = false → Adjacent R a t → Adjacent R d t →
    d ∈ movingNeighbors geometry a → edgeDisplacement d t = edgeDisplacement a t
  moving_symmetric : ∀ a d, color R a = false →
    d ∈ movingNeighbors geometry a → a ∈ movingNeighbors geometry d

/-- The geometric input to the last (1.7)(ii) application, at the endpoint's
distance-two predecessor. The noncontainment is essential for the final
faithfulness contradiction; no final commutator bound is assumed. -/
structure TerminalSeed {geometry : Geometry R} (p : Counterexample geometry) where
  t : Vertex R
  before : Before p.a p.a' t 3
  adjacent : Adjacent R p.c t
  six_lt : 6 < geometry.b R
  edge_centralizes : ⁅Vcirc R p.a, V R t⁆ = ⊥
  actor_local : Vcirc R p.c ≤ stabilizer R p.a
  actor_not_le : ¬ Vcirc R p.c ≤ Q R p.a

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl
