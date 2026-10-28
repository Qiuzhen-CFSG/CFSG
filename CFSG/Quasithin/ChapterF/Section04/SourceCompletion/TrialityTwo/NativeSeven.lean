module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.Basic
public import Theory.GroupAction.RankTwoCosetGeometry.AlternatingSeven
public import Theory.GroupAction.RankTwoCosetGeometry.Valence
public import Theory.GroupAction.RankTwoCosetGeometry.PathCardinality
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount

/-!
# Seven-path transitivity in the genuine triality group at q = 2

The canonical alternating seven-walk has fixer in the intersection of opposite
Borels, hence in the torus of order seven. The two valences are nine and three,
so the rooted nonbacktracking seven-walk counts are 36864 and 12288. Multiplying
by seven gives exactly the endpoint orders. Orbit--stabilizer therefore proves
transitivity at both types using the original D4 graph-field carrier.

Source: Aschbacher--Smith F.4.6(1), pp.276--277; the concrete opposition
calculation retains the GLS3 references in the imported triality development.
-/

@[expose] public noncomputable section
open Theory.GroupTheory Subgroup
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.NativeSeven
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat

def node : Bool → Node | false => .arms | true => .central
def family (i : Bool) : Subgroup Model := parabolic parameters (node i)
def first (i : Bool) : Model := weylRepresentative parameters parameters_prime (relativeReflection (node i))
def second (i : Bool) : Model := first (!i)

theorem completion_family : modelCompletion.family = family := by
  funext i
  cases i
  · exact model_left_range
  · exact model_right_range

theorem first_mem (i : Bool) : first i ∈ family i := by
  rw [first,weylRepresentative_simple]
  exact simpleRepresentative_mem_parabolic _ rfl _
theorem second_mem (i : Bool) : second i ∈ family (!i) := first_mem (!i)

theorem family_intersection (i : Bool) : family i ⊓ family (!i) = borel parameters := by
  cases i
  · exact parabolic_inf_binary _ rfl
  · exact (inf_comm _ _).trans (parabolic_inf_binary _ rfl)

theorem first_not_mem (i : Bool) : first i ∉ family (!i) := by
  intro h
  have hb : first i ∈ borel parameters := family_intersection i ▸ ⟨first_mem i,h⟩
  exact (relativeReflection_involution (node i)).1
    ((RelativeNormalizer.representative_mem_borel_iff 1 Nat.zero_lt_one _).mp hb)
theorem second_not_mem (i : Bool) : second i ∉ family i := by
  simpa only [second,Bool.not_not] using first_not_mem (!i)

theorem longest (i : Bool) : second i * first i * second i * first i * second i * first i =
    weylRepresentative parameters parameters_prime (.r 3) := by
  simp only [first,second,←weylRepresentative_mul]
  congr 1
  cases i <;> decide

def path (i : Bool) : BasedWalk (graph family) 7 (RankTwo.base family i) :=
  alternatingSeven family i (first i) (second i) (first_mem i) (second_mem i)

theorem path_nonbacktracking (i : Bool) : (path i).Nonbacktracking :=
  alternatingSeven_nonbacktracking family i (first i) (second i)
    (first_mem i) (second_mem i) (first_not_mem i) (second_not_mem i)

theorem path_fixer_le (i : Bool) : pathStabilizer family (path i) ≤ torus parameters := by
  have h := alternatingSeven_fixer_le family i (first i) (second i) (first_mem i) (second_mem i)
  rw [family_intersection,longest] at h
  intro x hx
  have hb := h hx
  apply TwoLocalGeometry.ApartmentStabilizer.borel_opposition_intersection
    1 Nat.zero_lt_one hb.1
  have hb2 := hb.2
  change (weylRepresentative parameters parameters_prime (.r 3))⁻¹ * x *
    ((weylRepresentative parameters parameters_prime (.r 3))⁻¹)⁻¹ ∈ borel parameters at hb2
  simpa only [inv_inv] using hb2

theorem path_fixer_card_le (i : Bool) : Nat.card (pathStabilizer family (path i)) ≤ 7 := by
  have h := Nat.card_le_card_of_injective (inclusion (path_fixer_le i)) (inclusion_injective _)
  have ht : Nat.card (torus parameters) = 7 := by
    simpa [parameters,Parameters.q,binaryParameters] using TorusCoordinates.card_torus parameters parameters_prime
  rwa [ht] at h

theorem family_card (i : Bool) : Nat.card (family i) = if i then 86016 else 258048 := by
  cases i
  · simpa only [family,node,Bool.false_eq_true,↓reduceIte,if_pos rfl] using parabolic_card .arms
  · simpa only [family,node,↓reduceIte,if_neg (by decide : Node.central ≠ Node.arms)] using parabolic_card .central

def degree (i : Bool) : ℕ := if i then 3 else 9

theorem degree_pos (i : Bool) : 0 < degree i := by cases i <;> decide

theorem base_neighbor_card (i : Bool) :
    Nat.card ((graph family).neighborSet (RankTwo.base family i)) = degree i := by
  rw [card_neighbor_base]
  have hidx := ((family (!i)).subgroupOf (family i)).card_mul_index
  have hmid : Nat.card ((family (!i)).subgroupOf (family i)) = Nat.card (borel parameters) := by
    rw [←inf_subgroupOf_right,
      Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv,inf_comm,family_intersection]
  rw [hmid,borel_card,family_card] at hidx
  cases i <;> simp only [Bool.false_eq_true,↓reduceIte,degree] at hidx ⊢ <;> omega

theorem neighbor_card (v : RankTwo.Vertex family) :
    Nat.card ((graph family).neighborSet v) = degree v.type := by
  obtain ⟨g,hg⟩ := exists_smul_base family v
  have hh := Nat.card_congr ((translationGraphIso family g).mapNeighborSet (RankTwo.base family v.type))
  change Nat.card ((graph family).neighborSet (RankTwo.base family v.type)) =
    Nat.card ((graph family).neighborSet (g • RankTwo.base family v.type)) at hh
  rw [hg] at hh
  exact hh.symm.trans (base_neighbor_card v.type)

theorem seven_path_card (i : Bool) :
    Nat.card {p : BasedWalk (graph family) 7 (RankTwo.base family i) // p.Nonbacktracking} =
      if i then 12288 else 36864 := by
  have (x : RankTwo.Vertex family) : Finite ((graph family).neighborSet x) :=
    Nat.finite_of_card_ne_zero (by rw [neighbor_card]; exact Nat.ne_of_gt (degree_pos x.type))
  have hf : ∀ {x y : RankTwo.Vertex family}, (graph family).Adj x y → y.type = !x.type := by
    intro x y h
    exact Bool.eq_not_iff.mpr h.1.symm
  have hc := BasedWalk.card_nonbacktracking_succ (graph family)
    (fun x : RankTwo.Vertex family => x.type) degree hf neighbor_card 6 (RankTwo.base family i)
  change _ = degree i * BasedWalk.forwardCount degree 6 (!i) at hc
  have hn (j : Bool) : degree j * BasedWalk.forwardCount degree 6 (!j) =
      if j then 12288 else 36864 := by cases j <;> decide
  exact hc.trans (hn i)

theorem seven_path_transitive (i : Bool) :
    RootPathTransitive (graph family) Model (RankTwo.base family i) 7 := by
  have : Finite {p : BasedWalk (graph family) 7 (RankTwo.base family i) // p.Nonbacktracking} :=
    Nat.finite_of_card_ne_zero (by rw [seven_path_card]; cases i <;> decide)
  apply rootPathTransitive_of_pathStabilizer_card_le family (path i)
    (path_nonbacktracking i) (by decide : 0 < 7) (path_fixer_card_le i)
  rw [stabilizer,stabilizer_base,family_card,seven_path_card]
  cases i <;> decide
end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.NativeSeven
