module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.CentralizerCharacter
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.OppositeFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceSixCentralizer

/-!
# The original nonsylow distance-two field restriction

Source (6) supplies a field-sized critical pair on the original star.
Its full fixed quotient has a natural kernel, and the chosen natural cover
selects one compatible long-root orientation. The point-parabolic action
constructs a scalar commutator character whose kernel is the source
relative centralizer. The square/inverse comparison, opposite fixed-core
disjointness, and strict original point-core movement force the field to
have four elements, hence the original degree is two.

All geometric, natural-action, centralizer-order and movement premises are
proved from the original short, inner, nonsylow distance-two hypotheses.
Source: Meierfrankenfeld--Stellmacher (1993), (3.7), printed pp.876--877.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition Theory.SpecificGroups.SymplecticFour P1Comparison
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
variable (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include h hshort hinner hnsyl

/-- The genuine original field-critical configuration forces degree two.
The quotient marking and relative-centralizer character are constructed,
and the entire fixed attachment is retained until the final lift. -/
theorem original_field_critical_degree_two
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n) : n=2 ∧ Nat.card F=4 := by
  let : Finite (stabilizer R a) := finite_stabilizer R a
  let : Finite (FixedQuotient R a) :=
    inferInstanceAs (Finite (stabilizer R a ⧸ fixedAttachment R a))
  obtain ⟨cv,u,⟨s⟩⟩ := exists_original_marked_pair h hshort hinner hnsyl
    g hb path hat hzt hcritical
  obtain ⟨φ,hφA,hφker⟩ := exists_relativeCentralizer_character s
  apply original_degree_two_of_character h hshort hinner hnsyl path hb hat hzt hcritical
    (coverQuotient h hinner cv) (coverQuotient_kernel h hinner cv) u
    (cv.field.card_eq.trans (congrArg (2^·) cv.degree)) s φ hφA
  · rw [original_relativeCentralizer_eq path]
    exact hφker
  · exact original_field_critical_opposite_fixed_disjoint h hshort hinner hnsyl
      g hb path hat hzt hcritical

/-- Source (3.7) has degree two on every original short inner nonsylow
star of critical distance two. No critical pair or endgame data is assumed. -/
theorem original_nonsylow_distance_two_degree_two
    (g : Geometry R) (hb : g.b R=2) : n=2 ∧ Nat.card F=4 := by
  obtain ⟨a,z,⟨path⟩,hcritical⟩ :=
    original_source_six_exists_field_critical_pair h hshort hinner hnsyl g hb
  have hd : (cosetGraph R).dist a z=2 :=
    path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two R a z hd
  exact original_field_critical_degree_two h hshort hinner hnsyl g hb path hat hzt hcritical

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
