module

public import Stellmacher.Recognition.Parrott.SylowOuterSeed

/-!
# Intermediate contracts for the last Sylow coordinate choices

The middle stage imposes (16)–(18) on an actual seed. The last stage determines
(19), leaving at most the central factor in [x,d] that x↦xt removes. Both
contracts use y=x²z literally, so a change of x also changes the prescribed y.
These predicates assert no existence; the completion owner must discharge both.

Source: Parrott (1972), §3, printed p.680, equations (16)–(19).
-/

namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- Equations (16)–(18), on the supplied actual seed subgroups. -/
public structure OuterMiddleRelations (f : ParrottSylowSeedData n false) : Prop where
  eq16_ax : Tits.parrottCommutator f.a f.x = 1
  comm_by : Commute f.b (f.x^2*z)
  eq17_yd : Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w
  eq18_bx : Tits.parrottCommutator f.b f.x = f.a

/-- Equation (19), before the harmless final correction x↦xt. -/
public structure OuterLastRelations (f : ParrottSylowSeedData n false) : Prop where
  eq19_yc : Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t*z
  eq19_xc : Tits.parrottCommutator f.x f.c = f.a*f.b*f.u*n.v
  eq19_xd : Tits.parrottCommutator f.x f.d = f.a*f.b*f.c*f.u*n.v ∨
    Tits.parrottCommutator f.x f.d = (f.a*f.b*f.c*f.u*n.v)*z

end Stellmacher.Recognition.ParrottSylowSeedData
