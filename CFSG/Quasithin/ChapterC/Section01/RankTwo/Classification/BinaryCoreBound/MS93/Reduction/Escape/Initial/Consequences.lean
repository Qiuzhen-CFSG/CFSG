module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Bounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.DistanceFour

/-!
# The final three initial escape consequences

The uniform preceding stages of (4.3.1) imply all of (v)--(vii): critical
distance at least six, the order-four radius--moving commutator lower bound,
and the exact edge commutator identity. DistanceFour excludes b = 4 using
the source class-two assertion; Bounds uses the two faithful natural layers;
Edges selects genuine conjugate critical endpoints and applies the radius
order supplied by the preceding stage. Every transported application retains
an actual contrary configuration.

This is the complete conditional tail stage. Its only additional inputs are
the uniform order-four and SectionFacts conclusions from (i)--(iv), to be
discharged by the initial-stage assembly. The H order bound is already
provided separately by Initial.H_card_of_radius_moving.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(v)--(vii), p.883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- All remaining clauses of (4.3.1), conditional exactly on the two uniform
preceding stages. No later escape or pairing conclusion is assumed. -/
theorem tailFacts_of_uniform_stages (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (hfour : ∀ q : Counterexample geometry, Nat.card (radiusCommutator q.a q.a') = 4)
    (hsections : ∀ q : Counterexample geometry, Nonempty (SectionFacts q))
    (p : Counterexample geometry) : TailFacts p where
  six_le := Consequences.six_le source hb modules p hsections
  radius_moving_card := Consequences.radius_moving_card source hb modules p hsections
  edge_commutator := fun t ht d hdt hd =>
    Consequences.moving_commutator_eq_edge source hb modules p hfour hsections
      p.a t d p.color_a ht.endpoint_adjacent hdt hd

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial
