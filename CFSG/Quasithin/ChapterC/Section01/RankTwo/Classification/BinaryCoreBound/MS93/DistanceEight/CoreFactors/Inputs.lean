module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Extension
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Source

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Basic

/-!
# Preceding source inputs for the core-factor argument

`Earlier` contains only the conclusions of (4.4), its regular critical-path
replacement (4.4.4), and its extended-path construction (4.4.5). Each field
names its source clause. It contains no statement about the center, order
or shape of the commutator core or its fixed factor.

The natural-section type spells out the meaning of c(V_a/Z_a)=1 given on
printed p.881. Reusing that type does not construct its witness: the
contrary-assumption section proved during (4.3) cannot supply this field.
The replacement field retains the standing regularity convention after
(4.4.2), printed p.893. Its quantification is restricted accordingly.

The parent distance-eight assembly must construct these inputs from
LocalSource, CommonFacts and b>4. The final core-factor theorem remains
here as an assembly obligation; `factor_inclusions` exports only the
proved inclusions and disjointness, not the missing equalities or order.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.881, 890, 893--895.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors
variable {M : Type*} [Group M] (R : Subgroup M)

/-- Exact preceding source outputs, with no core-factor conclusion as a premise. -/
structure Earlier (geometry : Geometry R) where
  /-- (4.4): the critical distance is eight. -/
  distance : geometry.b R = 8
  /-- (4.4): c(V_a/Z_a)=1, on the actual stabilizer quotient action. -/
  natural_section : ∀ a, color R a = false →
    Nonempty (Escape.NaturalSectionAt a (V R a) (Z R a))
  /-- (4.4): the radius-two commutator with Q_a is central in G_a. -/
  centrality : ∀ a, color R a = false →
    ⁅V R a, Q R a⁆ ≤ (center (stabilizer R a)).map (stabilizer R a).subtype
  /-- (4.4): |Z_a:Z_t|=q, here q=2, on an incident edge. -/
  edge_Z_index : ∀ a t, color R a = false → Adjacent R a t →
    (Z R t).relIndex (Z R a) = 2
  /-- (4.4): |T_t:Q_a|=q², here q=2, on an incident edge. -/
  edge_Q_index : ∀ a t, color R a = false → Adjacent R a t →
    (Q R a).relIndex (Q R t) = 4
  /-- The finite path constructed at the start of (4.4.5), printed p.894. -/
  extended : ∀ a, color R a = false →
    Nonempty (PathCentrality.RegularPaths.ExtendedPath geometry a)
  /-- (4.4.4), under the standing regularity convention following (4.4.2). -/
  replacement : ∀ a a' (p : PathCentrality.CriticalPath R geometry a a'),
    PathCentrality.HasTurnConjugators R p → PathCentrality.PrescribedReplacement R p

/-- Apply the preceding centrality clause to the literal core factors.
The equality and cardinality assertions of (4.5) are not claimed. -/
theorem Earlier.factor_inclusions [Finite M] {R L : Subgroup M}
    {geometry : Geometry R} {source : LocalSource L R}
    (earlier : Earlier R geometry) (common : CommonFacts R source geometry) :
    H R (alpha R) ≤ core R (alpha R) ⊓
        centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) ∧
      U R (alpha R) ⊔ H R (alpha R) ≤
        (center (core R (alpha R))).map (core R (alpha R)).subtype ∧
      Disjoint (U R (alpha R)) (H R (alpha R)) := by
  have hc := earlier.centrality (alpha R) rfl
  exact ⟨H_le_fixedFactor_of_central rfl common.large_distance hc,
    U_join_H_le_coreCenter_of_central common hc, U_disjoint_H_of_central common hc⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors
