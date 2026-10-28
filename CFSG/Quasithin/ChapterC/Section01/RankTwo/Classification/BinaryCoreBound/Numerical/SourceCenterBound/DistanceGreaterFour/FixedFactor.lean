module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Generation

/-!
# An upper bound for the distance-eight fixed factor

If the moving radius group lies in one actual local Z-span and the radius
commutator is central in the local stabilizer, its commutator H lies in the
initial displacement of that span. Centrality makes the local normal closure
of this displacement equal to itself, and the existing two-step calculation
bounds its order by four.

The second theorem applies the proved moving-generation theorem to a genuine
radius natural section and moving neighbor. The section and local centrality
remain explicit source inputs. In particular, no section from the contrary
assumption in (4.3) is used to manufacture the actual (4.4) section.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4), p.890,
(4.4.1)--(4.4.5), pp.890--895, and the upper bound in (4.5.1)(v), p.896.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.Numerical.SourceCenterBound.DistanceGreaterFour
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open MS93 MS93.DistanceEight
open MS93.DistanceEight.PathCentrality MS93.DistanceEight.PathCentrality.LocalCommutator
open scoped commutatorElement

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- A local span containing the moving radius group gives the needed H bound,
once the genuine (4.4) radius commutator is central. -/
theorem H_card_le_four_of_moving_span
    (common : CommonFacts R source geometry) {a d : Vertex R}
    (ha : color R a = false) (hd : (cosetGraph R).dist d a = 2)
    (hspan : Vcirc R a ≤ localZSpan R d a)
    (hc : ⁅V R a, Q R a⁆ ≤
      (center (stabilizer R a)).map (stabilizer R a).subtype) :
    Nat.card (H R a) ≤ 4 := by
  let K := ⁅Z R d, Q R a⁆
  have hKC : K ≤ (center (stabilizer R a)).map (stabilizer R a).subtype :=
    (commutator_mono
      ((Z_le_localZSpan R d a).trans (localZSpan_le_V R hd.le)) le_rfl).trans hc
  have hKcentral : K ≤ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
    intro x hx y hy
    obtain ⟨z, hz, rfl⟩ := hKC hx
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)
  have hKn : stabilizer R a ≤ normalizer (K : Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp hKcentral).trans (Subgroup.centralizer_le_normalizer _)
  have hlocal : ⁅localZSpan R d a, Q R a⁆ = K := by
    rw [span_commutator_eq_conjugates (geometry := geometry) ha hd.le common.large_distance]
    exact Escape.PairingControl.conjugatesIn_eq_of_normalized K (stabilizer R a) hKn
  have hHK : H R a ≤ K := (commutator_mono hspan le_rfl).trans hlocal.le
  have hdcolor : color R d = false :=
    (color_eq_of_dist_even R d a (by rw [hd]; decide)).trans ha
  let : Finite (stabilizer R a) := finite_stabilizer R a
  have hKS : K ≤ stabilizer R a := hKC.trans (map_subtype_le _)
  let : Finite K := Finite.of_injective (inclusion hKS) (inclusion_injective hKS)
  exact (card_le_of_le hHK).trans (displacement_card_le_four common hdcolor hd)

/-- The public natural-section API provides the exact moving-span containment.
This witness must come from actual (4.4), not from (4.3)'s contrary assumption. -/
theorem H_alpha_card_le_four_of_natural_section
    (common : CommonFacts R source geometry)
    (s : Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R)))
    (d : Vertex R) (hd : d ∈ Escape.movingNeighbors geometry (alpha R))
    (hc : ⁅V R (alpha R), Q R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    Nat.card (H R (alpha R)) ≤ 4 := by
  have hspan := Escape.Initial.Natural.moving_generation_of_naturalSection
    source geometry common.large_distance (alpha R) rfl s d hd
  rw [← span_eq_conjugates] at hspan
  exact H_card_le_four_of_moving_span common rfl
    (by rw [SimpleGraph.dist_comm]; exact hd.1) hspan hc

end CFSG.Quasithin.ChapterC.BinaryMS.Numerical.SourceCenterBound.DistanceGreaterFour
