module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Prerequisites
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Centrality.Offender
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Centrality.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Centrality.Escape

/-!
# Assembly of the initial distance-four factorization argument

The center containment (4.6.1) and actual quotient-offender obstruction
(4.6.2) are proved in the imported modules. Failure of radius-kernel centrality
selects a genuine critical pair of radius generators. The source index-four
calculation and small displacement for its endpoint actor force
V_delta' = U_delta by the marked natural action. The intersection bound
from the same calculation is retained for the escape argument.
The final conjugate-escape contradiction then gives (4.6.3).

The conditional constructor keeps the two local steps visible. The final
`initialFacts` theorem discharges both with their proved geometric arguments,
constructing all three initial clauses from LocalSource, Geometry, CommonFacts
and critical distance four alone. The last theorem combines centrality with
the three-subgroup and omega-center argument to give both clauses of (4.6.3).
The later EarlyFacts assembly remains with the parent argument.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.1)--(4.6.3), pp.900--902.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
open Early Early.Initial
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Conditional assembly of the three initial clauses. Both remaining source
steps refer to the actual noncentral radius-generator pair; the existing
center and offender theorems discharge all their own extra premises here. -/
theorem initialFacts_of_noncentral_pair_steps
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (displacement : ∀ a d e, NoncentralPair R a d e →
      (Q R e).relIndex (Z R d) = 4 ∧
      ⁅V R d ⊓ Q R a,Z R e⁆ ≤ Z R d ∧
      (radiusFixed geometry d (Z R e)).relIndex (V R d) ≤ (Q R d).relIndex (Z R e))
    (escape : ∀ a d e, NoncentralPair R a d e →
      (Q R e).relIndex (Z R d) = 4 →
      ⁅V R d ⊓ Q R a,Z R e⁆ ≤ Z R d →
      ⁅V R d,V R d⁆ = U R d → False) : InitialFacts R geometry := by
  refine {
    center_le_B := radius_center_le_B source geometry common hb
    offender_derived_le := radius_offender_obstruction common hb
      (radius_center_le_B source geometry common hb)
    commutator_central := ?_ }
  intro a ha
  by_contra hnot
  obtain ⟨d,e,h⟩ := exists_noncentralPair common hb a ha hnot
  obtain ⟨hindex,hintersection,hsmall⟩ := displacement a d e h
  exact escape a d e h hindex hintersection
    (h.derived_eq_U_of_small_displacement common hb hsmall)

/-- The binary initial factorization argument, MS93 (4.6.1)--(4.6.3), with
the source displacement and simultaneous-escape premises discharged. -/
theorem initialFacts
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4) :
    InitialFacts R geometry :=
  initialFacts_of_noncentral_pair_steps source geometry common hb
    (fun _ _ _ h => h.displacement common hb)
    (fun _ _ _ h => h.false_of_index_intersection_derived common hb)

/-- Both conclusions of MS93 (4.6.3) for the radius-two group. -/
theorem radius_commutator_central_and_derived_le_Z
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false) :
    ⁅V R a, Q R a⁆ ≤ (center (V R a)).map (V R a).subtype ∧
      ⁅V R a, V R a⁆ ≤ Z R a := by
  have hc := (initialFacts source geometry common hb).commutator_central a ha
  exact ⟨hc, derived_le_Z_of_commutator_central common a ha hc⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
