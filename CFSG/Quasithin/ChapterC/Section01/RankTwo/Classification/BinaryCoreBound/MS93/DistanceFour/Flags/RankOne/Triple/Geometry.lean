module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Actors

/-!
# The literal local flag layers in the (4.6.8) argument

Represent a vertex of the local coset geometry by its parabolic color and
an element of M. Incidence means that the two left cosets have a common
representative. Conjugation uses that same element through the original
amalgam embedding. The first-color U-layer is the conjugate of V_beta.
The second-color layer is the span of the neighboring fixed preimages in
V_alpha/Z_alpha. The use of commutatorPreimage keeps the quotient condition
literal without assuming normality in the infinite ambient amalgam.

`FlagNaturalSection` is exactly the natural quotient claimed in (1) on
p.905. `FlagPreparatoryData` records the chosen configuration and conclusions
(2)--(4) on p.906. Neither has a constructor in this module. They separate
two intermediate proof obligations; the binary auxiliary-layer argument
on pp.907--908 and the FlagControl assembly remain subsequent obligations.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.905--908.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- Conjugation by an actual element of the M-vertex group. -/
def localConjugate (H : Subgroup (FreeAmalgam R)) (g : M) :
    Subgroup (FreeAmalgam R) := H.map (MulAut.conj (embedM R g)).toMonoidHom

@[simp] theorem localConjugate_one (H : Subgroup (FreeAmalgam R)) :
    localConjugate H (1 : M) = H := by
  unfold localConjugate
  rw [map_one]
  have he : (MulAut.conj (1 : FreeAmalgam R)).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    change 1 * x * 1⁻¹ = x
    simp only [one_mul, inv_one, mul_one]
  rw [he, map_id]

/-- Incidence of the two actual left parabolic cosets, with first color i. -/
def flagIncident (source : LocalSource L R) (i : Bool) (g h : M) : Prop :=
  ∃ m : M, g⁻¹ * m ∈ parabolic source.projection source.flag i ∧
    h⁻¹ * m ∈ parabolic source.projection source.flag (!i)

/-- Source Q_delta at the coset represented by g. -/
def localFlagKernel (source : LocalSource L R) (j : Bool) (g : M) :
    Subgroup (FreeAmalgam R) := localConjugate (flagKernel source j) g

/-- Source untilded L_delta, which is the full binary parabolic. -/
def localFlagActor (source : LocalSource L R) (j : Bool) (g : M) :
    Subgroup (FreeAmalgam R) := localConjugate (flagParabolic source j) g

/-- Source tilded L_delta, retaining the order of the residual operations. -/
def localFlagResidual (source : LocalSource L R) (j : Bool) (g : M) :
    Subgroup (FreeAmalgam R) := localConjugate (flagResidual source j) g

/-- Source Z_delta = C_(Z_alpha)(Q_delta). -/
noncomputable def localFlagZ (source : LocalSource L R) (j : Bool) (g : M) :
    Subgroup (FreeAmalgam R) :=
  Z R (alpha R) ⊓ centralizer (localFlagKernel source j g : Set (FreeAmalgam R))

/-- The first-color source U_delta, with U_delta1 = V_beta. -/
noncomputable def firstFlagLayer (g : M) : Subgroup (FreeAmalgam R) :=
  localConjugate (V R (beta R)) g

/-- The second-color fixed span, lifted from the actual quotient by Z_alpha. -/
noncomputable def secondFlagLayer (source : LocalSource L R) (i : Bool) (h : M) :
    Subgroup (FreeAmalgam R) :=
  ⨆ g : M, ⨆ (_ : flagIncident source i g h),
    commutatorPreimage (firstFlagLayer (R := R) g)
      (localFlagKernel source (!i) h) (Z R (alpha R))

/-- The actual natural rank-one quotient in numbered claim (1), p.905. -/
def FlagNaturalSection (source : LocalSource L R) (i : Bool) : Type _ :=
  RankOnePairing.RankOneFactor (flagParabolic source i) (V R (beta R))
    (commutatorPreimage (V R (beta R)) (flagResidual source i) (Z R (alpha R)))

/-- The configuration at the end of p.906, before the binary auxiliary layers.
These are intermediate conclusions to be proved, not source assumptions. -/
structure FlagPreparatoryData (source : LocalSource L R) (geometry : Geometry R)
    (i : Bool) where
  middle : Vertex R
  endpoint : Vertex R
  critical : CriticalPair R (alpha R) endpoint (geometry.exists_critical (alpha R) rfl)
  middle_neighbor : Adjacent R (beta R) middle
  first_distance : (cosetGraph R).dist (alpha R) middle = 2
  second_distance : (cosetGraph R).dist middle endpoint = 2
  middle_triple : ¬ ⁅⁅Z R middle, flagResidual source i⁆, V R (alpha R)⁆ ≤
    (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype
  delta2 : M
  delta2_neighbor : flagIncident source i 1 delta2
  endpoint_crosses : ¬ Z R endpoint ⊓ localFlagKernel source (!i) delta2 ≤ Q R (alpha R)
  propagation : ⁅Z R middle, Q R (alpha R)⁆ ≤ U R (alpha R) →
    ∀ t, nu R geometry (alpha R) t → ⁅Z R t, Q R (alpha R)⁆ ≤ U R (alpha R)
  second_triple : ¬ ⁅⁅V R (beta R), localFlagKernel source (!i) delta2⁆,
    localFlagResidual source (!i) delta2⁆ ≤ Z R (alpha R)
  delta0 : M
  delta0_neighbor : flagIncident source i 1 delta0
  endpoint_not_le : ¬ Z R endpoint ≤ localFlagKernel source (!i) delta0
  intersection_commutator :
    ⁅Z R middle ⊓ secondFlagLayer source i delta0, localFlagActor source (!i) delta0⁆ ≤
      localFlagZ source (!i) delta0
  middle_not_le : ¬ Z R middle ≤ secondFlagLayer source i delta0
  displacement : 2 ≤ (Q R middle).relIndex (secondFlagLayer source i delta0)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
