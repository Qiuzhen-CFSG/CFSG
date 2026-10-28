module
public import Theory.SpecificGroups.PSL3.SmallCompletion.Orders
public import Theory.GroupAction.RankTwoCosetGeometry.AlternatingFive
public import Theory.GroupAction.RankTwoCosetGeometry.PathCardinality
public import Theory.GroupAction.RankTwoCosetGeometry.Valence
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount

/-!
# Four-edge transitivity for the native linear-three flag graph

Coordinate reflections give a nonbacktracking four-edge path. Fixing its
first and last flags forces a matrix into the upper and lower Borels, hence
into the actual projective torus. The endpoint order is precisely the number
(q + 1)q³ of rooted four-paths times the torus order, so orbit–stabilizer
proves transitivity. The calculation includes q = 4 and the full scalar kernel.

This supplies the path action used by the exact native amalgam lift.
Source: Aschbacher–Smith F.4.5–6, printed pp.275–277 (`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace Matrix.PSL3.SmallCompletion.NativePaths
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
local notation "PSL" => PSL(3,F)
def longestSL : SL(3,F) :=
  ⟨!![0,0,1; 0,1,0; 1,0,0], by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩
def longest : PSL := projection F (longestSL F)
theorem reflection_not_mem_opposite (i : Bool) : reflection F i ∉ (parabolic F) (!i) := by
  intro h
  apply reflection_not_mem_borel F i
  have hi : (parabolic F) i ⊓ (parabolic F) (!i) = borel F := by
    apply Subgroup.comap_injective (projection_surjective F)
    cases i <;> simp only [parabolic,Bool.not_false,Bool.not_true,Bool.false_eq_true,
      if_false,if_true,Subgroup.comap_inf,pointParabolic_comap,lineParabolic_comap,borel_comap,borelSL,inf_comm]
  rw [←hi]
  exact ⟨reflection_mem F i,h⟩
omit [Finite F] in
theorem longest_word (i : Bool) : reflection F (!i) * reflection F i * reflection F (!i) = longest F := by
  unfold reflection longest
  rw [←map_mul,←map_mul]
  congr 1
  apply Subtype.ext
  change (reflectionSL F (!i)).val * (reflectionSL F i).val * (reflectionSL F (!i)).val = (longestSL F).val
  cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [reflectionSL,longestSL,Matrix.mul_apply,Fin.sum_univ_three]
omit [Finite F] in
theorem longest_inv : (longest F)⁻¹ = longest F := by
  apply inv_eq_of_mul_eq_one_right
  unfold longest
  rw [←map_mul]
  have h : longestSL F * longestSL F = 1 := by
    apply Subtype.ext
    change (longestSL F).val * (longestSL F).val = (1 : Matrix (Fin 3) (Fin 3) F)
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [longestSL,Matrix.mul_apply,Fin.sum_univ_three]
  rw [h,map_one]

def path (i : Bool) : BasedWalk (graph (parabolic F)) 4 (RankTwo.base (parabolic F) i) :=
  (alternatingFive (parabolic F) i (reflection F i) (reflection F (!i))
    (reflection_mem F i) (reflection_mem F (!i))).take 4 (by decide)
theorem path_vertices (i : Bool) : (path F i).vertices =
    [RankTwo.base (parabolic F) i,RankTwo.base (parabolic F) (!i),
    reflection F (!i) • RankTwo.base (parabolic F) i,
    (reflection F (!i)*reflection F i) • RankTwo.base (parabolic F) (!i),
    longest F • RankTwo.base (parabolic F) i] := by
  rw [path, BasedWalk.vertices_take, alternatingFive_vertices]
  simp only [List.take_succ_cons, List.take_zero, longest_word]
theorem path_nonbacktracking (i : Bool) : (path F i).Nonbacktracking := by
  apply BasedWalk.nonbacktracking_take
  apply alternatingFive_nonbacktracking
  · exact reflection_not_mem_opposite F i
  · simpa using reflection_not_mem_opposite F (!i)

omit [CharP F 2] in
theorem family_inf (i : Bool) : (parabolic F) i ⊓ (parabolic F) (!i) = borel F := by
  apply Subgroup.comap_injective (projection_surjective F)
  cases i <;> simp only [parabolic,Bool.not_false,Bool.not_true,Bool.false_eq_true,
    if_false,if_true,Subgroup.comap_inf,pointParabolic_comap,lineParabolic_comap,borel_comap,borelSL,inf_comm]

theorem path_fixer_le (i : Bool) : pathStabilizer (parabolic F) (path F i) ≤
    borel F ⊓ (borel F).comap (MulAut.conj (longest F)).toMonoidHom := by
  intro g hg
  have h0 := hg (RankTwo.base (parabolic F) i) (by simp [path_vertices])
  have h1 := hg (RankTwo.base (parabolic F) (!i)) (by simp [path_vertices])
  have h3 := hg ((reflection F (!i)*reflection F i) • RankTwo.base (parabolic F) (!i))
    (by simp [path_vertices])
  have h4 := hg (longest F • RankTwo.base (parabolic F) i) (by simp [path_vertices])
  have hf : reflection F (!i) • RankTwo.base (parabolic F) (!i) = RankTwo.base (parabolic F) (!i) := by
    change reflection F (!i) ∈ stabilizer (parabolic F) (RankTwo.base (parabolic F) (!i))
    simpa only [stabilizer,RankTwo.base,stabilizer_base] using reflection_mem F (!i)
  have h3' : g • (longest F • RankTwo.base (parabolic F) (!i)) =
      longest F • RankTwo.base (parabolic F) (!i) := by
    rw [←longest_word F i]
    simpa only [mul_smul,hf] using h3
  have mem_of_fix {j : Bool} {x : PSL}
      (hx : x • RankTwo.base (parabolic F) j = RankTwo.base (parabolic F) j) :
      x ∈ parabolic F j := by
    have hh : x ∈ stabilizer (parabolic F) (RankTwo.base (parabolic F) j) := hx
    simpa only [stabilizer,RankTwo.base,stabilizer_base] using hh
  refine ⟨(family_inf F i) ▸ ⟨mem_of_fix h0,mem_of_fix h1⟩, ?_⟩
  change longest F * g * (longest F)⁻¹ ∈ borel F
  rw [←longest_inv F]
  rw [inv_inv]
  rw [←family_inf F i]
  constructor
  · apply mem_of_fix
    rw [mul_smul,mul_smul,h4,←longest_inv F,inv_smul_smul]
  · apply mem_of_fix
    rw [mul_smul,mul_smul,h3',←longest_inv F,inv_smul_smul]
theorem opposite_borels_le_torus :
    borel F ⊓ (borel F).comap (MulAut.conj (longest F)).toMonoidHom ≤ torus F := by
  rintro g ⟨hg,hopp⟩
  obtain ⟨a,ha,rfl⟩ := hg
  have hconj : projection F (longestSL F * a * longestSL F) ∈ borel F := by
    change longest F * projection F a * (longest F)⁻¹ ∈ borel F at hopp
    rw [longest_inv F] at hopp
    simpa only [longest, map_mul] using hopp
  have hb : longestSL F * a * longestSL F ∈ borelSL F := by
    change longestSL F * a * longestSL F ∈ (borel F).comap (projection F) at hconj
    rwa [borel_comap] at hconj
  obtain ⟨h10,h20,h21⟩ := (mem_borelSL_iff F a).mp ha
  have hu := (mem_borelSL_iff F _).mp hb
  have hu' : a.val 1 2 = 0 ∧ a.val 0 2 = 0 ∧ a.val 0 1 = 0 := by
    change ((longestSL F).val * a.val * (longestSL F).val) 1 0 = 0 ∧
      ((longestSL F).val * a.val * (longestSL F).val) 2 0 = 0 ∧
      ((longestSL F).val * a.val * (longestSL F).val) 2 1 = 0 at hu
    simpa [longestSL,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,vecHead,vecTail] using hu
  obtain ⟨h12,h02,h01⟩ := hu'
  obtain ⟨d,hd⟩ := (mem_torusSL_iff_entries F a).mpr ⟨h01,h02,h10,h12,h20,h21⟩
  exact ⟨d, congrArg (projection F) hd⟩


theorem path_fixer_card_le (i : Bool) : Nat.card (pathStabilizer (parabolic F) (path F i)) ≤ Nat.card (torus F) :=
  Nat.card_le_card_of_injective
    (Subgroup.inclusion ((path_fixer_le F i).trans (opposite_borels_le_torus F)))
    (Subgroup.inclusion_injective _)

omit [CharP F 2] in
theorem neighbor_index (i : Bool) :
    ((parabolic F (!i)).subgroupOf (parabolic F i)).index = Nat.card F+1 := by
  have hi : parabolic F (!i) ⊓ parabolic F i = borel F := by
    rw [inf_comm]; exact family_inf F i
  have hh : (parabolic F (!i)).subgroupOf (parabolic F i) =
      (borel F).subgroupOf (parabolic F i) := by
    rw [←hi]
    ext g
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h,g.property⟩,fun h => h.1⟩
  rw [hh]
  exact borel_relIndex F i

omit [CharP F 2] in
theorem card_neighbors (v : RankTwo.Vertex (parabolic F)) :
    Nat.card ((graph (parabolic F)).neighborSet v) = Nat.card F+1 :=
  card_neighbors_of_indices (parabolic F) (fun _ => Nat.card F+1) (neighbor_index F) v

omit [CharP F 2] in
theorem four_path_card (i : Bool) :
    Nat.card {p : BasedWalk (graph (parabolic F)) 4 (RankTwo.base (parabolic F) i) //
      p.Nonbacktracking} = (Nat.card F+1)*Nat.card F^3 := by
  have (x : RankTwo.Vertex (parabolic F)) : Finite ((graph (parabolic F)).neighborSet x) :=
    Nat.finite_of_card_ne_zero (by rw [card_neighbors]; omega)
  have hf : ∀ {x y : RankTwo.Vertex (parabolic F)}, (graph (parabolic F)).Adj x y → y.type = !x.type := by
    intro x y h
    have hxy := h.1
    cases hx : x.type <;> cases hy : y.type <;> simp_all
  rw [BasedWalk.card_nonbacktracking_succ (graph (parabolic F))
    (fun x : RankTwo.Vertex (parabolic F) => x.type) (fun _ : Bool => Nat.card F+1)
    hf (card_neighbors F) 3 (RankTwo.base (parabolic F) i)]
  simp [BasedWalk.forwardCount, pow_succ, mul_assoc]

theorem four_path_transitive {n : ℕ} (hF : Nat.card F = 2^n) (i : Bool) :
    RootPathTransitive (graph (parabolic F)) PSL (RankTwo.base (parabolic F) i) 4 := by
  have : Finite {p : BasedWalk (graph (parabolic F)) 4 (RankTwo.base (parabolic F) i) //
      p.Nonbacktracking} := Nat.finite_of_card_ne_zero (by rw [four_path_card]; exact ne_of_gt (Nat.mul_pos (by omega) (pow_pos Nat.card_pos _)))
  apply rootPathTransitive_of_pathStabilizer_card_le (parabolic F) (path F i)
    (path_nonbacktracking F i) Nat.card_pos (path_fixer_card_le F i)
  rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base,four_path_card,card_parabolic F hF]
end Matrix.PSL3.SmallCompletion.NativePaths
