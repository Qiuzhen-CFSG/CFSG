module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.P1Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.P1Character
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.CentralizerCharacter
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.OppositeFixed

/-!
# The original full-Sylow distance-two field restriction

Every original critical pair has field-sized images in the full Sylow
branch. Its actual natural cover and full fixed quotient construct the
marked opposite sections. The commutator character, opposite fixed-core
disjointness and strict point-core movement force the original field to
have four elements, hence the original degree is two.

All premises come from the original short, inner, Sylow distance-two
hypotheses. Source: MS93 (3.7), printed pp.872--877.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
open DistanceTwoRecognition Theory.SpecificGroups.SymplecticFour OriginalStar OriginalStar.P1Comparison
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
variable (hsyl : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include h hshort hinner hsyl

/-- The genuine original field-critical configuration forces degree two.
The quotient marking and relative-centralizer character are constructed,
and the entire fixed attachment is retained until the final lift. -/
theorem original_field_critical_degree_two
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) : n=2 ∧ Nat.card F=4 := by
  let : Finite (stabilizer R a) := finite_stabilizer R a
  let : Finite (FixedQuotient R a) :=
    inferInstanceAs (Finite (stabilizer R a ⧸ fixedAttachment R a))
  obtain ⟨cv,u,⟨s⟩⟩ := exists_original_marked_pair h hshort hinner hsyl
    g hb path hat hzt
  obtain ⟨φ,hφA,hφker⟩ := exists_relativeCentralizer_character s
  apply original_degree_two_of_character h hshort hinner hsyl path hb hat hzt
    (coverQuotient h hinner cv) (coverQuotient_kernel h hinner cv) u
    (cv.field.card_eq.trans (congrArg (2^·) cv.degree)) s φ hφA
  · rw [original_relativeCentralizer_eq path]
    exact hφker
  · exact original_field_critical_opposite_fixed_disjoint h hshort hinner hsyl
      g hb path hat hzt

/-- Source (3.7) has degree two on every original short inner Sylow
star of critical distance two. No critical pair or endgame data is assumed. -/
theorem original_sylow_distance_two_degree_two
    (g : Geometry R) (hb : g.b R=2) : n=2 ∧ Nat.card F=4 := by
  let a := mVertex R 1
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := R) (geometry := g)
    (a := a) (show color R a=false from rfl)
  have hd : (cosetGraph R).dist a z=2 :=
    path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two R a z hd
  exact original_field_critical_degree_two h hshort hinner hsyl g hb path hat hzt

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
