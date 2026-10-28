module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition.SourceBounds

/-!
# Unconditional action bounds on the four source windows

The first-kernel and critical-endpoint proof does not use the contrary
hat-identity assumption. These exports retain the original quotient actions
while exposing that stronger contract to the actual smaller fixed-seed split.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), printed p.897.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
private theorem forward_kernel_index (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i) (hi6 : i ≤ 6) :
    (Q R (p.walk.getVert (i + 6))).relIndex (V R (p.walk.getVert i)) ≤ 2 := by
  have ha := p.even_color hi (by omega)
  have he := p.even_color (hi.add (by decide : Even 6)) (by omega)
  exact First.Kernel.Detection.radius_kernel_index_le_two common earlier ha he
    (show Adjacent R (p.walk.getVert (i + 6)) (p.walk.getVert (i + 5)) from
      adjacent_symm R (by simpa only [Nat.add_assoc] using p.adjacent (i := i + 5) (by omega)))
    (show (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert (i + 5)) = 5 by
      rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega)
    (show (cosetGraph R).dist (p.walk.getVert (i + 6)) (p.walk.getVert (i + 4)) ≤ 2 by
      rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega)
    (p.first_commutator source common earlier hi hi2 (by omega)).2

private theorem backward_kernel_index (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi8 : 8 ≤ i) (hi12 : i ≤ 12) :
    (Q R (p.walk.getVert (i - 6))).relIndex (V R (p.walk.getVert i)) ≤ 2 := by
  have hi6 : Even (i - 6) := by rw [Nat.even_iff] at hi ⊢; omega
  have ha := p.even_color hi (by omega)
  have he := p.even_color hi6 (by omega)
  exact First.Kernel.Detection.radius_kernel_index_le_two common earlier ha he
    (show Adjacent R (p.walk.getVert (i - 6)) (p.walk.getVert (i - 5)) from
      by simpa only [show i - 6 + 1 = i - 5 by omega] using
        p.adjacent (i := i - 6) (by omega))
    (show (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert (i - 5)) = 5 by
      rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega)
    (show (cosetGraph R).dist (p.walk.getVert (i - 6)) (p.walk.getVert (i - 4)) ≤ 2 by
      rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega)
    (p.first_commutator_backward source common earlier hi hi8 hi12).2

/-- The actual forward quotient action, without a contrary-case assumption. -/
theorem actionBounds_forward (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6) :
    ActionBounds common earlier (forwardWindow common earlier p hi hi4 hi6) := by
  have hib : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  apply actionBounds_of_critical_kernel common earlier (forwardWindow common earlier p hi hi4 hi6)
    (p.critical_pair earlier hib (by omega))
    (forward_kernel_index common earlier p hib (by omega) (by omega))
  exact ((firstFactsOnPath source common earlier p).forward (i - 2) hib (by omega) (by omega)).intersection_product_le

/-- The actual reflected quotient action, without a contrary-case assumption. -/
theorem actionBounds_backward (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a)
    {i : ℕ} (hi : Even i) (hi8 : 8 ≤ i) (hi10 : i ≤ 10) :
    ActionBounds common earlier (backwardWindow common earlier p hi hi8 hi10) := by
  have hib : Even (i + 2) := hi.add (by decide)
  have hif : Even (i - 6) := by rw [Nat.even_iff] at hi ⊢; omega
  have hc := p.critical_pair earlier hif (by omega)
  rw [show i - 6 + 8 = i + 2 by omega] at hc
  have hr := common.critical_reverse _ (p.even_color hif (by omega)) _
    (p.even_color hib (by omega)) hc
  apply actionBounds_of_critical_kernel common earlier (backwardWindow common earlier p hi hi8 hi10) hr
  · simpa only [show i + 2 - 6 = i - 4 by omega] using
      backward_kernel_index common earlier p hib (by omega) (by omega)
  · simpa only [show i + 2 - 6 = i - 4 by omega,
      show i + 2 - 8 = i - 6 by omega] using
      ((firstFactsOnPath source common earlier p).backward (i + 2) hib (by omega) (by omega)).intersection_product_le

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition
