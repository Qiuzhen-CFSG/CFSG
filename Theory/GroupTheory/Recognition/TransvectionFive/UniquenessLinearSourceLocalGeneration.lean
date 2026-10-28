module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceFlags
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceFusion
import all Theory.GroupTheory.GraphUniquenessSystem.CosetConstruction

/-!
# Seven-point local residue and local generation

The normalizer of the marked row–three-space four-group is transitive on
its three nonidentity elements. The relative point-centralizer index 21
therefore gives index seven for the row intersection inside the three-space
normalizer. Its maximality and the already constructed edge reversal prove
the local-generation identity of the source uniqueness system.

Source: Aschbacher, *Sporadic Groups* (1994), 41.1–41.4, pp.219–222.
These local assertions require neither ambient simplicity nor global generation.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
open GraphUniquenessSystem GraphUniquenessSystem.Cosets
variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (hlinear : F.LinearFusion)

omit [Finite G] in
include F in
private theorem point_ne_one : z ≠ 1 := by
  intro hz
  have ho := F.point_orderOf
  simp [hz] at ho

include hlinear

/-- All three nonidentity elements of the actual four-group are point conjugates. -/
theorem fourGroup_fusion :
    F.fusion (F.row ⊓ F.threeSpace) =
      ((F.row ⊓ F.threeSpace : Subgroup G) : Set G) \ {1} := by
  ext a
  constructor
  · rintro ⟨ha, hza⟩
    refine ⟨ha, ?_⟩
    intro he
    have haz : IsConj z (1 : G) := he ▸ hza
    exact point_ne_one F (isConj_one_left.mp haz)
  · rintro ⟨ha, ha1⟩
    have hzD : z ∈ F.row ⊓ F.threeSpace := ⟨point_mem_row F, point_mem_threeSpace F⟩
    obtain ⟨g, _, _, hg⟩ := row_subgroup_nonidentity_transitive F hlinear
      (F.row ⊓ F.threeSpace) inf_le_left ⟨z, hzD⟩ ⟨a, ha⟩
      (fun he => point_ne_one F (congrArg Subtype.val he))
      (fun he => ha1 (congrArg Subtype.val he))
    exact ⟨ha, isConj_iff.mpr ⟨g, hg⟩⟩

/-- The point centralizer has relative index three in the actual point–plane intersection. -/
theorem fourGroup_point_index :
    (centralizer ({z} : Set G)).relIndex
      (rowNormalizer F ⊓ sourceThreeSpaceNormalizer F) = 3 := by
  rw [← source_row_threeSpace_normalizer F hlinear]
  rw [normalizer_point_index F (F.row ⊓ F.threeSpace)
    ⟨point_mem_row F, point_mem_threeSpace F⟩]
  · rw [fourGroup_fusion F hlinear,
      Set.ncard_sdiff_singleton_of_mem (F.row ⊓ F.threeSpace).one_mem]
    change Nat.card ↥(F.row ⊓ F.threeSpace) - 1 = 3
    rw [UniquenessMathieu.SourceNormalizer.row_threeSpace_card F]
  · intro a ha hza
    obtain ⟨g, _, hgN, hg⟩ := row_subgroup_nonidentity_transitive F hlinear
      (F.row ⊓ F.threeSpace) inf_le_left
      ⟨z, point_mem_row F, point_mem_threeSpace F⟩ ⟨a, ha⟩
      (fun he => point_ne_one F (congrArg Subtype.val he)) (by
        intro he
        have ha1 : a = 1 := congrArg Subtype.val he
        exact point_ne_one F (isConj_one_left.mp (ha1 ▸ hza)))
    exact ⟨g, hgN, hg⟩

/-- The seven points on the actual source plane are its literal row-intersection cosets. -/
theorem plane_point_index : (rowNormalizer F).relIndex (sourceThreeSpaceNormalizer F) = 7 := by
  have hm := relIndex_inf_mul_relIndex (centralizer ({z} : Set G))
    (rowNormalizer F) (sourceThreeSpaceNormalizer F)
  rw [fourGroup_point_index F hlinear,
    inf_eq_left.mpr (point_centralizer_le_row_normalizer F),
    source_threeSpace_point_index F hlinear] at hm
  omega

/-- The point stabilizer is maximal in the original three-space normalizer. -/
theorem local_flag_maximal :
    IsCoatom ((rowNormalizer F).subgroupOf (sourceThreeSpaceNormalizer F)) := by
  let A := (rowNormalizer F).subgroupOf (sourceThreeSpaceNormalizer F)
  have hi : A.index = 7 := plane_point_index F hlinear
  change IsCoatom A
  refine ⟨fun ht => by simp [ht] at hi, fun B hAB => ?_⟩
  have hm := relIndex_mul_index hAB.le
  rw [hi] at hm
  have hp : (A.relIndex B * B.index).Prime := hm ▸ (by decide : Nat.Prime 7)
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hB⟩ | ⟨_, hrel⟩
  · exact index_eq_one.mp hB
  · exact (hAB.not_ge (relIndex_eq_one.mp hrel)).elim

/-- The actual local edge stabilizer and point stabilizer generate the full
three-space normalizer, with the original chosen coset edge. -/
theorem local_generate :
    (sourceThreeSpaceNormalizer F ⊓ edgeStabilizer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (planeSwap F hlinear : G))) ⊔
      (sourceThreeSpaceNormalizer F ⊓ MulAction.stabilizer G (vertex (rowNormalizer F) 1)) =
        sourceThreeSpaceNormalizer F := by
  rw [stabilizer_base, inf_comm (sourceThreeSpaceNormalizer F) (rowNormalizer F)]
  apply Cosets.sup_inter_eq_of_maximal (rowNormalizer F) (sourceThreeSpaceNormalizer F) _
    (local_flag_maximal F hlinear) inf_le_left
  intro hle
  exact planeSwap_not_row F hlinear (hle ⟨planeSwap_mem F hlinear,
    Or.inr (swap (rowNormalizer F) (planeSwap F hlinear : G) (planeSwap_square_mem F hlinear))⟩)

/-- Both local generation identities hold inside the source induction subgroup,
without a simplicity assumption on that subgroup. -/
theorem normalizerSpan_local_generation :
    let E := normalizerSpanMarking F
    let hE := normalizerSpan_linearFusion F hlinear
    let x := vertex (rowNormalizer E) 1
    let y := vertex (rowNormalizer E) (planeSwap E hE : normalizerSpan F)
    (edgeFixer (normalizerSpan F) x y ⊔
      (sourceThreeSpaceNormalizer E ⊓ MulAction.stabilizer (normalizerSpan F) x) =
        MulAction.stabilizer (normalizerSpan F) x) ∧
    ((sourceThreeSpaceNormalizer E ⊓ edgeStabilizer (normalizerSpan F) x y) ⊔
      (sourceThreeSpaceNormalizer E ⊓ MulAction.stabilizer (normalizerSpan F) x) =
        sourceThreeSpaceNormalizer E) :=
  ⟨vertex_generate _ _, local_generate _ _⟩

end Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
