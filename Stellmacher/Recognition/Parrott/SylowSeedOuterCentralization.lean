module

public import Stellmacher.Recognition.Parrott.SylowOuterSeed
public import Theory.SpecificGroups.Tits.RecognitionSylowOuterCosets
public import Theory.SpecificGroups.Tits.RecognitionSylowOuterParameters
public import Theory.SpecificGroups.Tits.RecognitionSylowOuterFourthPower
public import Stellmacher.Recognition.Parrott.DerivedCentralizer

/-!
# Outer-image bounds for the supplied Sylow seed

The unprimed seed determines the right x-conjugates of b,c,d modulo the
actual elementary derived subgroup E. The scalar calculation compares their
actions on E, and the already proved equality C_G(E)=E makes the resulting
bounds intrinsic to the supplied coordinates. No compatibility of the seed's
b with the original three-subgroup is assumed.

These bounds prepare the order-four calculation needed for the centralization
assertion immediately after equation (16).

Source: Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–680, especially p.679 after (10) and p.680 after (16).
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- The three right-conjugate errors belong to the supplied elementary derived
subgroup. The representatives agree with the final outer equations, but the
errors have not yet been removed or restricted. -/
public theorem outer_discrepancies_mem_derived [Finite G]
    (f : ParrottSylowSeedData n false) (h : ParrottCentralizerHypotheses z) :
    f.x⁻¹*f.b*f.x*(f.b*f.a)⁻¹ ∈ closure ({z,n.t,n.v,f.u,f.w} : Set G) ∧
    f.x⁻¹*f.c*f.x*(f.c*(f.a*f.b*f.u*n.v)⁻¹)⁻¹ ∈
      closure ({z,n.t,n.v,f.u,f.w} : Set G) ∧
    f.x⁻¹*f.d*f.x*(f.d*(f.a*f.b*f.c*f.u*n.v)⁻¹)⁻¹ ∈
      closure ({z,n.t,n.v,f.u,f.w} : Set G) := by
  have hc : centralizer (closure ({z,n.t,n.v,f.u,f.w} : Set G) : Set G) =
      closure ({z,n.t,n.v,f.u,f.w} : Set G) := by
    rw [f.derived_basis]
    exact parrott_derived_centralizer z h
  simpa only [hc] using f.relations.outer_discrepancies_centralize

/-- The square of the supplied outer generator, multiplied by `z`,
centralizes the supplied seed element `b`. -/
public theorem b_comm_square_mul_z [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (_hN : IsNTwoGroup G)
    (f : ParrottSylowSeedData n false) (h : ParrottCentralizerHypotheses z)
    (hax : Tits.parrottCommutator f.a f.x = 1) :
    Commute f.b (f.x^2*z) := by
  have hz : z ≠ 1 := (orderOf_eq_prime_iff.mp h.involution).2
  obtain ⟨hb, hc, hd⟩ := f.outer_discrepancies_mem_derived h
  obtain ⟨⟨bi, bj, bk, hb⟩, ⟨ci, cj, ck, hc⟩, ⟨di, dj, dk, hd⟩⟩ :=
    Tits.ParrottSylowSeedRelations.outer_image_parameters f.relations hz hax hb hc hd
  exact Tits.ParrottSylowSeedRelations.b_comm_square_mul_z_of_parameters
    f.relations hz hax bi bj bk ci cj ck di dj dk hb hc hd

end Stellmacher.Recognition.ParrottSylowSeedData
