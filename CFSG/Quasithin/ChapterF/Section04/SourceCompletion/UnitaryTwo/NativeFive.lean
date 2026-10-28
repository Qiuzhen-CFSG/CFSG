module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.CommonCover
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourApartment
public import Theory.GroupAction.RankTwoCosetGeometry.AlternatingFive
public import Theory.GroupAction.RankTwoCosetGeometry.PathCardinality
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount

/-!
# Five-edge transitivity in the binary unitary-four model

The literal opposite-flag five-walk is nonbacktracking. Its pointwise fixer
lies in the intersection of the standard and opposite Borels. The diagonal
torus character is injective on this intersection and has order three over
GF(4), so the fixer has order at most three. The endpoint orders and
nonbacktracking path counts are 576, 960 and 192, 320 respectively; orbit–
stabilizer therefore gives transitivity at both marked types.

This is the model path input for Aschbacher–Smith F.4.6 and F.4.24,
printed pp.276–288. It establishes path transitivity only; no generalized
quadrangle recognition or completion marking equivalence is assumed.
-/
@[expose] public noncomputable section
open Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGeneration
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.NativeFive
open GreenBook.LieModels.UnitaryFour
noncomputable section
local notation "h1" => (Nat.le_refl 1)
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 h1
abbrev MG := MatrixGroup 1 h1

def matrixCompletion : RankTwoAmalgam.FaithfulCompletion (matrixAmalgam 1 h1) (G := MG) :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups _ _ _ inf_le_left inf_le_right
    (matrix_parabolics_generate 1 h1)

def completion : Completion MG := matrixCompletion.comapIso (projectIso 1 h1).symm

def family : Bool → Subgroup MG := fun i => if i then planeParabolicMatrix 1 h1
  else pointParabolicMatrix 1 h1

theorem completion_family : completion.family = family := by
  funext i
  cases i
  · change (completion.left.range) = pointParabolicMatrix 1 h1
    change (matrixCompletion.comapIso (projectIso 1 h1).symm).left.range = _
    rw [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range]
    exact RankTwoAmalgam.FaithfulCompletion.ofSubgroups_left_range _ _ _ _ _ _
  · change (completion.right.range) = planeParabolicMatrix 1 h1
    change (matrixCompletion.comapIso (projectIso 1 h1).symm).right.range = _
    rw [RankTwoAmalgam.FaithfulCompletion.comapIso_right_range]
    exact RankTwoAmalgam.FaithfulCompletion.ofSubgroups_right_range _ _ _ _ _ _

def first (i : Bool) : MG := if i then pairSwap F σ hσ else middleSwap F σ hσ
def second (i : Bool) : MG := if i then middleSwap F σ hσ else pairSwap F σ hσ

theorem first_mem (i : Bool) : first i ∈ family i := by
  cases i
  · exact middleSwap_mem_point F σ hσ
  · exact pairSwap_mem_plane F σ hσ

theorem second_mem (i : Bool) : second i ∈ family (!i) := by
  cases i
  · exact pairSwap_mem_plane F σ hσ
  · exact middleSwap_mem_point F σ hσ

theorem first_not_mem (i : Bool) : first i ∉ family (!i) := by
  cases i
  · exact middleSwap_not_mem_plane F σ hσ
  · exact pairSwap_not_mem_point F σ hσ

theorem second_not_mem (i : Bool) : second i ∉ family i := by
  cases i
  · exact pairSwap_not_mem_point F σ hσ
  · exact middleSwap_not_mem_plane F σ hσ

theorem longest (i : Bool) : second i * first i * second i * first i = reverse F σ hσ := by
  cases i
  · rfl
  · apply Subtype.ext
    apply Units.ext
    change ((middleSwap F σ hσ).val.val * (pairSwap F σ hσ).val.val *
      (middleSwap F σ hσ).val.val * (pairSwap F σ hσ).val.val) = (reverse F σ hσ).val.val
    rw [reverse_val]
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [middleSwap, pairSwap, involutionElement, pairSwapMatrix, middleSwapMatrix,
        gram, Matrix.mul_apply, Fin.sum_univ_succ]

theorem family_intersection (i : Bool) : family i ⊓ family (!i) =
    borelSU F (form F σ hσ) := by
  cases i
  · rfl
  · exact inf_comm _ _

def path (i : Bool) : BasedWalk (graph family) 5 (base family i) :=
  alternatingFive family i (first i) (second i) (first_mem i) (second_mem i)

theorem path_nonbacktracking (i : Bool) : (path i).Nonbacktracking :=
  alternatingFive_nonbacktracking family i (first i) (second i)
    (first_mem i) (second_mem i) (first_not_mem i) (second_not_mem i)

theorem path_fixer_le (i : Bool) : pathStabilizer family (path i) ≤
    UnitaryFourApartment.oppositeFlagFixer F σ hσ := by
  change pathStabilizer family (alternatingFive family i (first i) (second i)
    (first_mem i) (second_mem i)) ≤
    (borelSU F (form F σ hσ) ⊓
      (borelSU F (form F σ hσ)).comap (MulAut.conj (reverse F σ hσ)).toMonoidHom)
  have h := alternatingFive_fixer_le family i (first i) (second i)
    (first_mem i) (second_mem i)
  rw [family_intersection i, longest i] at h
  have hr : reverse F σ hσ = (reverse F σ hσ)⁻¹ :=
    (UnitaryFourApartment.reverse_inv F σ hσ).symm
  rw [hr]
  exact h

theorem path_fixer_card_le (i : Bool) : Nat.card (pathStabilizer family (path i)) ≤ 3 := by
  have h := Nat.card_le_card_of_injective (Subgroup.inclusion (path_fixer_le i))
    (Subgroup.inclusion_injective (path_fixer_le i))
  have hb := UnitaryFourApartment.oppositeFlagFixer_card_le F σ hσ
  rw [matrixField_card 1 h1, PointLocal.fixedField_card 1 h1] at hb
  exact h.trans hb

theorem base_neighbor_card (i : Bool) :
    Nat.card ((graph family).neighborSet (base family i)) = if i then 5 else 3 := by
  rw [card_neighbor_base]
  cases i
  · change ((planeParabolicMatrix 1 h1).subgroupOf
      (pointParabolicMatrix 1 h1)).index = 3
    have hidx := ((planeParabolicMatrix 1 h1).subgroupOf
      (pointParabolicMatrix 1 h1)).card_mul_index
    have hmid : Nat.card ((planeParabolicMatrix 1 h1).subgroupOf
        (pointParabolicMatrix 1 h1)) = Nat.card (overlapMatrix 1 h1) := by
      rw [← Subgroup.inf_subgroupOf_left]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [hmid, BinaryCompletion.overlap_matrix_card, BinaryCompletion.point_matrix_card] at hidx
    omega
  · change ((pointParabolicMatrix 1 h1).subgroupOf
      (planeParabolicMatrix 1 h1)).index = 5
    have hidx := ((pointParabolicMatrix 1 h1).subgroupOf
      (planeParabolicMatrix 1 h1)).card_mul_index
    have hmid : Nat.card ((pointParabolicMatrix 1 h1).subgroupOf
        (planeParabolicMatrix 1 h1)) = Nat.card (overlapMatrix 1 h1) := by
      rw [← Subgroup.inf_subgroupOf_right]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [hmid, BinaryCompletion.overlap_matrix_card, BinaryCompletion.plane_matrix_card] at hidx
    omega

theorem neighbor_card (v : Vertex family) :
    Nat.card ((graph family).neighborSet v) = if v.type then 5 else 3 := by
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base family v
  have hh := Nat.card_congr ((Subgroup.CosetGeometry.translationGraphIso family g).mapNeighborSet
    (base family v.type))
  change Nat.card ((graph family).neighborSet (base family v.type)) =
    Nat.card ((graph family).neighborSet (g • base family v.type)) at hh
  rw [hg] at hh
  rw [← hh]
  exact base_neighbor_card v.type

theorem root_stabilizer_card (i : Bool) : Nat.card (stabilizer family (base family i)) =
    if i then 960 else 576 := by
  rw [stabilizer, Subgroup.CosetGeometry.stabilizer_base]
  cases i
  · exact BinaryCompletion.point_matrix_card
  · exact BinaryCompletion.plane_matrix_card

theorem five_path_card (i : Bool) :
    Nat.card {p : BasedWalk (graph family) 5 (base family i) // p.Nonbacktracking} =
      if i then 320 else 192 := by
  have (x : Vertex family) : Finite ((graph family).neighborSet x) :=
    Nat.finite_of_card_ne_zero (by rw [neighbor_card]; cases x.type <;> decide)
  have hf : ∀ {x y : Vertex family}, (graph family).Adj x y → y.type = !x.type := by
    intro x y h
    have hxy := h.1
    cases hx : x.type <;> cases hy : y.type <;> simp_all
  have hc := BasedWalk.card_nonbacktracking_succ (graph family)
    (fun x : Vertex family => x.type) (fun b : Bool => if b then 5 else 3)
    hf neighbor_card 4 (base family i)
  rw [hc]
  cases i <;> norm_num [BasedWalk.forwardCount, base]

theorem five_path_transitive (i : Bool) :
    RootPathTransitive (graph family) MG (base family i) 5 := by
  have : Finite {p : BasedWalk (graph family) 5 (base family i) // p.Nonbacktracking} :=
    Nat.finite_of_card_ne_zero (by rw [five_path_card]; cases i <;> decide)
  apply rootPathTransitive_of_pathStabilizer_card_le family (path i)
    (path_nonbacktracking i) (by decide : 0 < 3) (path_fixer_card_le i)
  rw [root_stabilizer_card, five_path_card]
  cases i <;> decide
end
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.NativeFive
