module
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.SimpleRecognition.ParabolicIntersections
public import Theory.SpecificGroups.Triality.TwoLocalCover.ApartmentStabilizer.Opposition
public import Theory.GroupAction.RankTwoCosetGeometry.AlternatingSeven
public import Theory.GroupAction.RankTwoCosetGeometry.Valence
public import Theory.GroupAction.RankTwoCosetGeometry.PathCardinality
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount

/-!
# Seven-path action of binary triality

The literal alternating seven-path has fixer in the opposite-Borel
intersection, hence in the Cartan subgroup. The unequal valences are q³+1
and q+1. Their seven-path counts, multiplied by the Cartan order, give
exactly the two parabolic orders; orbit--stabilizer proves transitivity.
All positive binary exponents are included.

Source: Aschbacher--Smith F.4.6(1), pp.276--277, and the native opposition
calculation from GLS3 2.3.8. This generalizes the q=2 calculation without
changing its specialized interface.
-/

@[expose] public noncomputable section
namespace Triality.Standard.SmallCompletion
open Subgroup Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Parabolics ConcreteBruhat

variable (m : ℕ) (hm : 0 < m)
local notation "P" => binaryParameters m hm
local notation "q" => Parameters.q (binaryParameters m hm)

theorem parameters_prime : (P).prime = 2 := rfl

def node : Bool → Node | false => .arms | true => .central
def family (i : Bool) : Subgroup (Carrier P) := parabolic P (node i)
def first (i : Bool) : Carrier P := weylRepresentative P (parameters_prime m hm) (relativeReflection (node i))
def second (i : Bool) : Carrier P := first m hm (!i)

theorem first_mem (i : Bool) : first m hm i ∈ family m hm i := by
  rw [first, weylRepresentative_simple]
  exact simpleRepresentative_mem_parabolic _ (parameters_prime m hm) _
theorem second_mem (i : Bool) : second m hm i ∈ family m hm (!i) := first_mem m hm (!i)

theorem family_intersection (i : Bool) : family m hm i ⊓ family m hm (!i) = borel P := by
  cases i
  · exact parabolic_inf_binary _ rfl
  · exact (inf_comm _ _).trans (parabolic_inf_binary _ rfl)

theorem first_not_mem (i : Bool) : first m hm i ∉ family m hm (!i) := by
  intro h
  have hb : first m hm i ∈ borel P := family_intersection m hm i ▸ ⟨first_mem m hm i, h⟩
  exact (relativeReflection_involution (node i)).1
    ((RelativeNormalizer.representative_mem_borel_iff m hm _).mp hb)
theorem second_not_mem (i : Bool) : second m hm i ∉ family m hm i := by
  simpa only [second, Bool.not_not] using first_not_mem m hm (!i)

theorem longest (i : Bool) : second m hm i * first m hm i * second m hm i *
    first m hm i * second m hm i * first m hm i = weylRepresentative P (parameters_prime m hm) (.r 3) := by
  simp only [first, second, ← weylRepresentative_mul]
  congr 1
  cases i <;> decide

def path (i : Bool) : BasedWalk (graph (family m hm)) 7 (RankTwo.base (family m hm) i) :=
  alternatingSeven (family m hm) i (first m hm i) (second m hm i)
    (first_mem m hm i) (second_mem m hm i)

theorem path_nonbacktracking (i : Bool) : (path m hm i).Nonbacktracking :=
  alternatingSeven_nonbacktracking (family m hm) i (first m hm i) (second m hm i)
    (first_mem m hm i) (second_mem m hm i) (first_not_mem m hm i) (second_not_mem m hm i)

theorem path_fixer_le (i : Bool) : pathStabilizer (family m hm) (path m hm i) ≤ torus P := by
  have h := alternatingSeven_fixer_le (family m hm) i (first m hm i) (second m hm i)
    (first_mem m hm i) (second_mem m hm i)
  rw [family_intersection, longest] at h
  intro x hx
  have hb := h hx
  apply TwoLocalGeometry.ApartmentStabilizer.borel_opposition_intersection m hm hb.1
  have hb2 := hb.2
  change (weylRepresentative P (parameters_prime m hm) (.r 3))⁻¹ * x *
    ((weylRepresentative P (parameters_prime m hm) (.r 3))⁻¹)⁻¹ ∈ borel P at hb2
  simpa only [inv_inv] using hb2

theorem path_fixer_card_le (i : Bool) :
    Nat.card (pathStabilizer (family m hm) (path m hm i)) ≤ (q^3-1)*(q-1) := by
  have h := Nat.card_le_card_of_injective (inclusion (path_fixer_le m hm i)) (inclusion_injective _)
  rwa [TorusCoordinates.card_torus P rfl] at h

def degree (i : Bool) : ℕ := (if i then q else q^3) + 1

theorem degree_pos (i : Bool) : 0 < degree m hm i := by unfold degree; omega

theorem family_card (i : Bool) :
    Nat.card (family m hm i) = q^12 * ((q^3-1)*(q-1)) * degree m hm i := by
  have h := ((borel P).subgroupOf (parabolic P (node i))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (borel_le_parabolic P (node i))).toEquiv] at h
  change Nat.card (borel P) * (borel P).relIndex (parabolic P (node i)) = _ at h
  rw [FixedCellCount.card_borel,
    OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic] at h
  cases i <;> simpa only [family, node, degree, Bool.false_eq_true, ↓reduceIte] using h.symm

theorem base_neighbor_card (i : Bool) :
    Nat.card ((graph (family m hm)).neighborSet (RankTwo.base (family m hm) i)) = degree m hm i := by
  rw [card_neighbor_base]
  rw [← inf_subgroupOf_right, inf_comm, family_intersection]
  change (borel P).relIndex (parabolic P (node i)) = _
  rw [OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic]
  cases i <;> rfl

theorem neighbor_card (v : RankTwo.Vertex (family m hm)) :
    Nat.card ((graph (family m hm)).neighborSet v) = degree m hm v.type := by
  obtain ⟨g,hg⟩ := exists_smul_base (family m hm) v
  have hh := Nat.card_congr ((translationGraphIso (family m hm) g).mapNeighborSet
    (RankTwo.base (family m hm) v.type))
  change Nat.card ((graph (family m hm)).neighborSet (RankTwo.base (family m hm) v.type)) =
    Nat.card ((graph (family m hm)).neighborSet (g • RankTwo.base (family m hm) v.type)) at hh
  rw [hg] at hh
  exact hh.symm.trans (base_neighbor_card m hm v.type)

theorem seven_path_card (i : Bool) :
    Nat.card {p : BasedWalk (graph (family m hm)) 7 (RankTwo.base (family m hm) i) //
      p.Nonbacktracking} = degree m hm i * q^12 := by
  have (x : RankTwo.Vertex (family m hm)) : Finite ((graph (family m hm)).neighborSet x) :=
    Nat.finite_of_card_ne_zero (by rw [neighbor_card]; exact Nat.ne_of_gt (degree_pos m hm x.type))
  have hf : ∀ {x y : RankTwo.Vertex (family m hm)}, (graph (family m hm)).Adj x y → y.type = !x.type := by
    intro x y h
    exact Bool.eq_not_iff.mpr h.1.symm
  have hc := BasedWalk.card_nonbacktracking_succ (graph (family m hm))
    (fun x => x.type) (degree m hm) hf (neighbor_card m hm) 6 (RankTwo.base (family m hm) i)
  rw [hc]
  cases i <;> simp [degree, BasedWalk.forwardCount] <;> ring

theorem seven_path_transitive (i : Bool) :
    RootPathTransitive (graph (family m hm)) (Carrier P) (RankTwo.base (family m hm) i) 7 := by
  have : Finite {p : BasedWalk (graph (family m hm)) 7 (RankTwo.base (family m hm) i) //
      p.Nonbacktracking} := Nat.finite_of_card_ne_zero (by
        rw [seven_path_card]
        exact Nat.ne_of_gt (Nat.mul_pos (degree_pos m hm i) (by rw [binaryParameters_q]; positivity)))
  apply rootPathTransitive_of_pathStabilizer_card_le (family m hm) (path m hm i)
    (path_nonbacktracking m hm i) (by
      rw [← TorusCoordinates.card_torus P rfl]
      exact Nat.card_pos) (path_fixer_card_le m hm i)
  rw [stabilizer, stabilizer_base, family_card, seven_path_card]
  ring

/-- The two native vertex counts, with the original arms/central labels. -/
def cosetCount (i : Bool) : ℕ := degree m hm (!i) * (q^8+q^4+1)

theorem card_coset (i : Bool) : Nat.card (Carrier P ⧸ family m hm i) = cosetCount m hm i := by
  have h := (family m hm i).index_mul_card
  rw [family_card, FixedCellCount.card_carrier, FixedCellCount.card_borel] at h
  have hb : 0 < q^12 * ((q^3-1)*(q-1)) := by
    rw [← FixedCellCount.card_borel m hm]
    exact Nat.card_pos
  have hd := degree_pos m hm i
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hb hd)
  change (family m hm i).index * _ = _
  rw [h]
  cases i <;> simp only [cosetCount, degree, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte] <;> ring

end Triality.Standard.SmallCompletion
