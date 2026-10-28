module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.RankReduction.SourceInputs
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
/-!
# Full-catalogue source application of reduction 13.3.14(b)

The completed simultaneous A/C theorem discharges the universal catalogue
inputs of SourceInputs. The remaining genuine preceding source statements
are structural 12.2.2, point escape 13.3.6 and the marked cubic parabolic.
The original Y, point normalizer and all quotient maps are preserved.
The last theorem supplies the literal moving residual used in (d).
Source: Aschbacher–Smith, printed pp.891–892.
-/
@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
/-- Reduction (b) on the original natural configuration, with full-catalogue A and C discharged. -/
theorem natural_reduction_b_knownSimple
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Chapter12.Section02.Structural1222.{u} KnownSimple.IsKnownSimple)
    (hescape : ¬ H ≤ M)
    (X : Subgroup G) (hXL : X ≤ L)
    (hx : letI := Section05.AmbientSource.source_plane_isKleinFour d
      Nat.card ((X.subgroupOf (normalizer (E : Set G))).map
        (Section05.AmbientSource.planeAction E)) = 3) :
    let Y := centralizingResidual (conjugateSpanBy U H)
    Group.IsSolvable Y ∧ ∀ p : ℕ, p.Prime → Odd p → primeRank p Y ≤ 1 :=
  natural_reduction_b_of_earlier_source d
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) h structural hescape X hXL hx

/-- The actual rank-two odd star subgroup supplies the moving source residual in (d). -/
theorem natural_starResidual_moves_knownSimple
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Chapter12.Section02.Structural1222.{u} KnownSimple.IsKnownSimple)
    (hescape : ¬ H ≤ M)
    (X : Subgroup G) (hXL : X ≤ L)
    (hx : letI := Section05.AmbientSource.source_plane_isKleinFour d
      Nat.card ((X.subgroupOf (normalizer (E : Set G))).map
        (Section05.AmbientSource.planeAction E)) = 3)
    (D : Subgroup (Star H)) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hD : IsPGroup p D) (hr : 1 < primeRank p D) :
    ⁅conjugateSpanBy U H,(starResidual H D).map H.subtype⁆ ≠ ⊥ :=
  starResidual_moves_of_rank H (conjugateSpanBy U H) D hp hD hr
    ((natural_reduction_b_knownSimple d h structural hescape X hXL hx).2 p Fact.out hp)

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
