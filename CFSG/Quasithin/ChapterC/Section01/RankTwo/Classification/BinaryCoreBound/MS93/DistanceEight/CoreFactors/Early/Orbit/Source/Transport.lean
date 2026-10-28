module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Statements

/-!
# Same-path transport and setwise products of the first hat identity

The turn at an interior even vertex identifies its two seed orbits under
that vertex stabilizer. This supplies reflected identities on the same
walk. Normalization of Z converts the subgroup identity into its literal
ordered setwise product. The lower inclusion is proved from the existing
moving-span calculation, without assuming the remaining upper inclusion.

Source: Meierfrankenfeld--Stellmacher (1993), standing path convention on
pp.895--896 and (4.5.3)(i), pp.897--898.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source
open PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Both neighboring seeds give the same orbit span under the stated turn. -/
theorem backward_hatV_eq_forward {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi2 : 2 ≤ i) (hi12 : i ≤ 12) :
    hatV R (p.walk.getVert i) (p.walk.getVert (i - 2)) =
      hatV R (p.walk.getVert i) (p.walk.getVert (i + 2)) := by
  obtain ⟨g, hg, ht⟩ := p.turns i hi hi2 hi12
  change localZSpan R (p.walk.getVert (i - 2)) (p.walk.getVert i) = _
  rw [← ht]
  exact LocalCommutator.CriticalCase.span_eq_of_local_conjugator hg

/-- The lower half of every forward identity follows from actual moving generation. -/
theorem moving_join_Z_le_hatV [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi2 : 2 ≤ i) (hi12 : i ≤ 12) :
    Vcirc R (p.walk.getVert i) ⊔ Z R (p.walk.getVert i) ≤
      hatV R (p.walk.getVert i) (p.walk.getVert (i + 2)) := by
  exact sup_le (p.moving_spans source common earlier hi hi2 hi12).2
    (Z_le_hatV (p.even_color hi (by omega)) (by
      rw [p.distance (geometry := geometry) (by omega) (by omega)]
      omega))

/-- Reflection keeps the same center and uses its supplied turn, not a new path. -/
theorem HatIdentitiesOnPath.backward {a : Vertex R} {p : SourcePath R a}
    (identity : HatIdentitiesOnPath R p) {i : ℕ}
    (hi : Even i) (hi2 : 2 ≤ i) (hi12 : i ≤ 12) :
    hatV R (p.walk.getVert i) (p.walk.getVert (i - 2)) =
      Vcirc R (p.walk.getVert i) ⊔ Z R (p.walk.getVert i) := by
  rw [backward_hatV_eq_forward p hi hi2 hi12]
  exact identity.forward i hi hi2 hi12

/-- The central first-hat identity retains the exact indexed vertex six. -/
theorem HatIdentitiesOnPath.center {a : Vertex R} {p : SourcePath R a}
    (identity : HatIdentitiesOnPath R p) :
    hatV R a (p.walk.getVert 6) = Vcirc R a ⊔ Z R a := by
  simpa only [p.center_eq] using identity.forward 4 (by decide) (by decide) (by decide)

/-- Normalization converts the subgroup equality into the ordered setwise product. -/
theorem hatV_product_of_eq (common : CommonFacts R source geometry)
    {a c : Vertex R} (ha : color R a = false)
    (heq : hatV R a c = Vcirc R a ⊔ Z R a) :
    (hatV R a c : Set (FreeAmalgam R)) =
      (Vcirc R a : Set (FreeAmalgam R)) * (Z R a : Set (FreeAmalgam R)) := by
  rw [heq]
  exact coe_mul_of_left_le_normalizer_right _ _
    ((((DistanceEight.Vcirc_le_V R a).trans (V_le_Q R ha common.large_distance)).trans
      (fun _ hx => hx.1)).trans (Z_normalized R a))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source
