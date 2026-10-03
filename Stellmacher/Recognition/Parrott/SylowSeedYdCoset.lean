module

public import Stellmacher.Recognition.Parrott.SylowSeedOuterGeometry
public import Stellmacher.Recognition.Parrott.DerivedCentralizer
public import Theory.SpecificGroups.Tits.RecognitionSylowYdCoset

/-!
# The initial d-commutator coset for an actual Sylow seed

For y=x²z, the seed geometry establishes that y is an involution. Comparing
its d-commutator with b gives a discrepancy in C_G(E), where E is the actual
ambient derived two-core. The equality C_G(E)=E puts this discrepancy in
the supplied elementary coordinates. If b commutes with y, the word
calculation then gives [y,d] in bw⟨v,z⟩. The seed already forces y to
centralize a, so this conclusion also holds before imposing [a,x]=1.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed p.680, immediately before equation (17).
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- Once b commutes with the prescribed y, its d-commutator lies in bw⟨v,z⟩.
This applies in particular to seeds normalized by [a,x]=1. -/
public theorem yd_cases [Finite G] (f : ParrottSylowSeedData n false)
    (h : ParrottCentralizerHypotheses z) (hby : Commute f.b (f.x^2*z)) :
    Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w ∨
    Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*z ∨
    Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*n.v ∨
    Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*n.v*z := by
  have hc : centralizer (closure ({z,n.t,n.v,f.u,f.w} : Set G) : Set G) =
      closure ({z,n.t,n.v,f.u,f.w} : Set G) := by
    rw [f.derived_basis]
    exact parrott_derived_centralizer z h
  have hz : z ≠ 1 := (orderOf_eq_prime_iff.mp h.involution).2
  exact f.relations.yd_cases_of_discrepancy_mem (f.square_mul_z_order h) hby hz
    (hc ▸ f.relations.yd_discrepancy_centralizes)

/-- The initial commutator bound for a seed satisfying (16), in the global
recognition setting. The stronger local result `yd_cases` shows that neither
the global hypotheses nor (16) are needed for this bound. -/
public theorem yd_commutator_cases [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (_hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) (f : ParrottSylowSeedData n false)
    (_hax : Tits.parrottCommutator f.a f.x = 1) (hby : Commute f.b (f.x^2*z)) :
    Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w ∨
    Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*z ∨
    Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*n.v ∨
    Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*n.v*z :=
  f.yd_cases h hby

end Stellmacher.Recognition.ParrottSylowSeedData
