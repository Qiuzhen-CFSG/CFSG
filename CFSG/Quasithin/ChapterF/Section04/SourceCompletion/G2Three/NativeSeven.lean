module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.G2Three.CommonCover
public import Theory.AtlasPort.LinearGroups.G2.ParabolicApartment
public import Theory.AtlasPort.LinearGroups.G2.ParabolicLocalOrder
public import Theory.GroupAction.RankTwoCosetGeometry.AlternatingSeven
public import Theory.GroupAction.RankTwoCosetGeometry.Valence
public import Theory.GroupAction.RankTwoCosetGeometry.PathCardinality
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount

/-!
# Seven-path transitivity in the native ternary G₂ model

The alternating Weyl seven-walk has a fixer inside the two opposite Borels.
The coordinate calculation places their intersection in the split torus, of
order four. Each endpoint has order 11664 and each vertex has four neighbors,
so there are 2916 nonbacktracking seven-walks from either root. Orbit–stabilizer
therefore gives transitivity at both types, with no geometry certificate.

Source: Aschbacher–Smith F.4.6(1), printed pp.276–277. The native coordinates
retain the ATLAS attribution and license in the imported model modules.
-/

open Theory.GroupTheory Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.SplitOctonion
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.NativeSeven
abbrev MG := Model (ZMod 3)
def family : Bool → Subgroup MG := fun i => if i then parabolic₂ else parabolic₁
theorem completion_family : modelCompletion.family = family := by
  funext i
  cases i
  · exact model_left_range
  · exact model_right_range

def first (i : Bool) : MG := if i then weylR else weylS
def second (i : Bool) : MG := if i then weylS else weylR

theorem first_mem (i : Bool) : first i ∈ family i := by
  cases i
  · exact mem_sup_right (subset_closure (by simp [first]))
  · exact weylR_mem_parabolic

theorem second_mem (i : Bool) : second i ∈ family (!i) := by
  cases i
  · exact weylR_mem_parabolic
  · exact mem_sup_right (subset_closure (by simp [second]))

private theorem weylS_not_mem : (weylS : MG) ∉ parabolic₂ := by
  intro h
  obtain ⟨a,ha⟩ := (mem_pointStabilizer_iff _).mp (parabolic_le_pointStabilizer h)
  have hh := congrFun ha 1
  norm_num [weylS,weylSEquiv,weylSLinear,weylSApply,basisVector,Units.smul_def] at hh
private theorem weylR_not_mem : (weylR : MG) ∉ parabolic₁ := by
  intro h
  have hh := (parabolic₁_le_shortPlaneStabilizer h).1 (basisVector 1)
    (basis_mem_shortPlane 1 (by decide)) 2 (by decide)
  change (-1 : ZMod 3) = 0 at hh
  norm_num at hh

theorem first_not_mem (i : Bool) : first i ∉ family (!i) := by
  cases i
  · exact weylS_not_mem
  · exact weylR_not_mem

theorem second_not_mem (i : Bool) : second i ∉ family i := by
  cases i
  · exact weylR_not_mem
  · exact weylS_not_mem

theorem longest (i : Bool) : second i * first i * second i * first i * second i * first i =
    ParabolicApartment.longest := by
  cases i
  · simp only [first,second,Bool.false_eq_true,↓reduceIte,ParabolicApartment.longest,pow_succ,
      pow_zero,one_mul,mul_assoc]
  · have hr : (weylR : MG)⁻¹=weylR := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using (weylR_sq (K := ZMod 3)))
    have hs : (weylS : MG)⁻¹=weylS := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using (weylS_sq (K := ZMod 3)))
    rw [←ParabolicApartment.longest_inv]
    simp only [first,second,↓reduceIte,ParabolicApartment.longest,
      mul_inv_rev,hr,hs,pow_succ,pow_zero,one_mul,mul_assoc]

theorem family_intersection (i : Bool) : family i ⊓ family (!i) = borel := by
  cases i
  · exact parabolics_intersection
  · exact (inf_comm _ _).trans parabolics_intersection

def path (i : Bool) : BasedWalk (graph family) 7 (RankTwo.base family i) :=
  alternatingSeven family i (first i) (second i) (first_mem i) (second_mem i)

theorem path_nonbacktracking (i : Bool) : (path i).Nonbacktracking :=
  alternatingSeven_nonbacktracking family i (first i) (second i)
    (first_mem i) (second_mem i) (first_not_mem i) (second_not_mem i)

theorem path_fixer_le (i : Bool) : pathStabilizer family (path i) ≤ splitTorus := by
  have h := alternatingSeven_fixer_le family i (first i) (second i)
    (first_mem i) (second_mem i)
  rw [family_intersection,longest,ParabolicApartment.longest_inv] at h
  exact h.trans ParabolicApartment.opposite_borel_le_torus

theorem path_fixer_card_le (i : Bool) : Nat.card (pathStabilizer family (path i)) ≤ 4 := by
  have h := Nat.card_le_card_of_injective (Subgroup.inclusion (path_fixer_le i))
    (Subgroup.inclusion_injective (path_fixer_le i))
  rw [card_splitTorus] at h
  norm_num [Nat.card_eq_fintype_card] at h
  exact h

theorem family_card (i : Bool) : Nat.card (family i) = 11664 := by
  cases i
  · change Nat.card (parabolic₁ (F := ZMod 3)) = _
    rw [ParabolicCells.short_card,card_borel]
    norm_num [Nat.card_eq_fintype_card]
  · change Nat.card (parabolic₂ (F := ZMod 3)) = _
    rw [card_parabolic]
    norm_num [Nat.card_eq_fintype_card]

theorem base_neighbor_card (i : Bool) :
    Nat.card ((graph family).neighborSet (RankTwo.base family i)) = 4 := by
  rw [card_neighbor_base]
  have hidx := ((family (!i)).subgroupOf (family i)).card_mul_index
  have hmid : Nat.card ((family (!i)).subgroupOf (family i)) = Nat.card (borel (K := ZMod 3)) := by
    rw [←Subgroup.inf_subgroupOf_right]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,inf_comm,
      family_intersection]
  rw [hmid,card_borel,family_card] at hidx
  norm_num [Nat.card_eq_fintype_card] at hidx
  omega

theorem neighbor_card (v : RankTwo.Vertex family) : Nat.card ((graph family).neighborSet v) = 4 := by
  obtain ⟨g,hg⟩ := exists_smul_base family v
  have hh := Nat.card_congr ((translationGraphIso family g).mapNeighborSet (RankTwo.base family v.type))
  change Nat.card ((graph family).neighborSet (RankTwo.base family v.type)) =
    Nat.card ((graph family).neighborSet (g • RankTwo.base family v.type)) at hh
  rw [hg] at hh
  rw [←hh]
  exact base_neighbor_card v.type

theorem seven_path_card (i : Bool) :
    Nat.card {p : BasedWalk (graph family) 7 (RankTwo.base family i) // p.Nonbacktracking} = 2916 := by
  have (x : RankTwo.Vertex family) : Finite ((graph family).neighborSet x) :=
    Nat.finite_of_card_ne_zero (by rw [neighbor_card]; decide)
  have hf : ∀ {x y : RankTwo.Vertex family}, (graph family).Adj x y → y.type = !x.type := by
    intro x y h
    have hxy := h.1
    cases hx : x.type <;> cases hy : y.type <;> simp_all
  have hc := BasedWalk.card_nonbacktracking_succ (graph family)
    (fun x : RankTwo.Vertex family => x.type) (fun _ => 4) hf neighbor_card 6 (RankTwo.base family i)
  simpa only [BasedWalk.forwardCount] using hc

theorem seven_path_transitive (i : Bool) :
    RootPathTransitive (graph family) MG (RankTwo.base family i) 7 := by
  have : Finite {p : BasedWalk (graph family) 7 (RankTwo.base family i) // p.Nonbacktracking} :=
    Nat.finite_of_card_ne_zero (by rw [seven_path_card]; decide)
  apply rootPathTransitive_of_pathStabilizer_card_le family (path i)
    (path_nonbacktracking i) (by decide : 0 < 4) (path_fixer_card_le i)
  rw [stabilizer,stabilizer_base,family_card,seven_path_card]
end CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.NativeSeven
