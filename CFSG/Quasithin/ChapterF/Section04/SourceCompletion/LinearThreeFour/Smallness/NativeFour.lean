module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.Smallness.CommonCover
public import Theory.GroupAction.RankTwoCosetGeometry.AlternatingFive
public import Theory.GroupAction.RankTwoCosetGeometry.PathCardinality
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount

/-!
# Four-edge transitivity in the native PSL₃(4) coset graph

The two coordinate transpositions give a literal alternating four-edge walk
at each root type. Its first and last edges are opposite flags, so its fixer
lies in both upper and lower Borels. Matrix entries put that intersection
in the actual diagonal torus, of order three. There are 5·4³ = 320 rooted
nonbacktracking walks and each endpoint has order 960; orbit–stabilizer
therefore proves transitivity. No recognition or ambient order bound for an
arbitrary completion enters this calculation.

Source: Aschbacher–Smith F.4.5–6, printed pp.275–277.
-/

@[expose] public noncomputable section

open Matrix Subgroup
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Native
local notation "F" => Matrix.PSL3Four.F
local notation "PSL" => Matrix.PSL3Four.PSL

def firstSL (i : Bool) : SL(3,F) :=
  if i then ⟨!![0,1,0; 1,0,0; 0,0,1], by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩
  else ⟨!![1,0,0; 0,0,1; 0,1,0], by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩
def first (i : Bool) : PSL := projection F (firstSL i)
def longestSL : SL(3,F) :=
  ⟨!![0,0,1; 0,1,0; 1,0,0], by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩
def longest : PSL := projection F longestSL
theorem first_mem (i : Bool) : first i ∈ modelCompletion.family i := by
  cases i
  · rw [Completion.family_false, model_left_range]
    exact mem_map_of_mem _ ((mem_pointParabolicSL_iff F _).mpr (by simp [firstSL]))
  · rw [Completion.family_true, model_right_range]
    exact mem_map_of_mem _ ((mem_lineParabolicSL_iff F _).mpr (by simp [firstSL]))
theorem first_not_mem (i : Bool) : first i ∉ modelCompletion.family (!i) := by
  cases i
  · rw [Bool.not_false,Completion.family_true,model_right_range]
    change firstSL false ∉ (lineParabolic F).comap (projection F)
    rw [lineParabolic_comap,mem_lineParabolicSL_iff]
    simp [firstSL]
  · rw [Bool.not_true,Completion.family_false,model_left_range]
    change firstSL true ∉ (pointParabolic F).comap (projection F)
    rw [pointParabolic_comap,mem_pointParabolicSL_iff]
    simp [firstSL]
theorem longest_word (i : Bool) : first (!i) * first i * first (!i) = longest := by
  unfold first longest
  rw [←map_mul,←map_mul]
  congr 1
  apply Subtype.ext
  change (firstSL (!i)).val * (firstSL i).val * (firstSL (!i)).val = longestSL.val
  cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [firstSL,longestSL,Matrix.mul_apply,Fin.sum_univ_three]
theorem longest_inv : longest⁻¹ = longest := by
  apply inv_eq_of_mul_eq_one_right
  unfold longest
  rw [←map_mul]
  have h : longestSL * longestSL = 1 := by
    apply Subtype.ext
    change longestSL.val * longestSL.val = (1 : Matrix (Fin 3) (Fin 3) F)
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [longestSL,Matrix.mul_apply,Fin.sum_univ_three]
  rw [h,map_one]

def path (i : Bool) : BasedWalk modelCompletion.graph 4 (RankTwo.base modelCompletion.family i) :=
  (alternatingFive modelCompletion.family i (first i) (first (!i))
    (first_mem i) (first_mem (!i))).take 4 (by decide)
theorem path_vertices (i : Bool) : (path i).vertices =
    [RankTwo.base modelCompletion.family i,RankTwo.base modelCompletion.family (!i),
    first (!i) • RankTwo.base modelCompletion.family i,
    (first (!i)*first i) • RankTwo.base modelCompletion.family (!i),
    longest • RankTwo.base modelCompletion.family i] := by
  rw [path, BasedWalk.vertices_take, alternatingFive_vertices]
  simp only [List.take_succ_cons, List.take_zero, longest_word]
theorem path_nonbacktracking (i : Bool) : (path i).Nonbacktracking := by
  apply BasedWalk.nonbacktracking_take
  apply alternatingFive_nonbacktracking
  · exact first_not_mem i
  · simpa using first_not_mem (!i)

theorem family_inf (i : Bool) : modelCompletion.family i ⊓ modelCompletion.family (!i) = borel F := by
  cases i
  · exact model_overlap.trans model_middle_range
  · exact (inf_comm _ _).trans (model_overlap.trans model_middle_range)

theorem path_fixer_le (i : Bool) : pathStabilizer modelCompletion.family (path i) ≤
    borel F ⊓ (borel F).comap (MulAut.conj longest).toMonoidHom := by
  intro g hg
  have h0 := hg (RankTwo.base modelCompletion.family i) (by simp [path_vertices])
  have h1 := hg (RankTwo.base modelCompletion.family (!i)) (by simp [path_vertices])
  have h3 := hg ((first (!i)*first i) • RankTwo.base modelCompletion.family (!i))
    (by simp [path_vertices])
  have h4 := hg (longest • RankTwo.base modelCompletion.family i) (by simp [path_vertices])
  have hf : first (!i) • RankTwo.base modelCompletion.family (!i) = RankTwo.base modelCompletion.family (!i) := by
    change first (!i) ∈ stabilizer modelCompletion.family (RankTwo.base modelCompletion.family (!i))
    simpa only [stabilizer,RankTwo.base,stabilizer_base] using first_mem (!i)
  have h3' : g • (longest • RankTwo.base modelCompletion.family (!i)) =
      longest • RankTwo.base modelCompletion.family (!i) := by
    rw [←longest_word i]
    simpa only [mul_smul,hf] using h3
  have mem_of_fix {j : Bool} {x : PSL}
      (hx : x • RankTwo.base modelCompletion.family j = RankTwo.base modelCompletion.family j) :
      x ∈ modelCompletion.family j := by
    have hh : x ∈ stabilizer modelCompletion.family (RankTwo.base modelCompletion.family j) := hx
    simpa only [stabilizer,RankTwo.base,stabilizer_base] using hh
  refine ⟨(family_inf i) ▸ ⟨mem_of_fix h0,mem_of_fix h1⟩, ?_⟩
  change longest * g * longest⁻¹ ∈ borel F
  rw [←longest_inv]
  rw [inv_inv]
  rw [←family_inf i]
  constructor
  · apply mem_of_fix
    rw [mul_smul,mul_smul,h4,←longest_inv,inv_smul_smul]
  · apply mem_of_fix
    rw [mul_smul,mul_smul,h3',←longest_inv,inv_smul_smul]
theorem opposite_borels_le_torus :
    borel F ⊓ (borel F).comap (MulAut.conj longest).toMonoidHom ≤ torus F := by
  rintro g ⟨hg,hopp⟩
  obtain ⟨a,ha,rfl⟩ := hg
  have hconj : projection F (longestSL * a * longestSL) ∈ borel F := by
    change longest * projection F a * longest⁻¹ ∈ borel F at hopp
    rw [longest_inv] at hopp
    simpa only [longest, map_mul] using hopp
  have hb : longestSL * a * longestSL ∈ borelSL F := by
    change longestSL * a * longestSL ∈ (borel F).comap (projection F) at hconj
    rwa [borel_comap] at hconj
  obtain ⟨h10,h20,h21⟩ := (mem_borelSL_iff F a).mp ha
  have hu := (mem_borelSL_iff F _).mp hb
  have hu' : a.val 1 2 = 0 ∧ a.val 0 2 = 0 ∧ a.val 0 1 = 0 := by
    change (longestSL.val * a.val * longestSL.val) 1 0 = 0 ∧
      (longestSL.val * a.val * longestSL.val) 2 0 = 0 ∧
      (longestSL.val * a.val * longestSL.val) 2 1 = 0 at hu
    simpa [longestSL,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,vecHead,vecTail] using hu
  obtain ⟨h12,h02,h01⟩ := hu'
  have hd : a.val 0 0 * a.val 1 1 * a.val 2 2 = 1 := by
    have h := a.property
    rw [Matrix.det_fin_three,h10,h20,h21] at h
    simpa only [zero_mul,mul_zero,add_zero,sub_zero] using h
  have h00 : a.val 0 0 ≠ 0 := by intro h; simp [h] at hd
  have h22 : a.val 2 2 ≠ 0 := by intro h; simp [h] at hd
  have h11 : a.val 1 1 = (a.val 0 0 * a.val 2 2)⁻¹ := by
    apply mul_left_cancel₀ (mul_ne_zero h00 h22)
    rw [mul_inv_cancel₀ (mul_ne_zero h00 h22)]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hd
  let d : Fˣ × Fˣ := (Units.mk0 _ h00, Units.mk0 _ h22)
  have he : a = torusSL F d := by
    apply Subtype.ext
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [torusSL_val,d,h10,h20,h21,h01,h02,h12,h11]
  exact ⟨d, congrArg (projection F) he.symm⟩

theorem path_fixer_card_le (i : Bool) : Nat.card (pathStabilizer modelCompletion.family (path i)) ≤ 3 := by
  have hh := Nat.card_le_card_of_injective
    (Subgroup.inclusion ((path_fixer_le i).trans opposite_borels_le_torus))
    (Subgroup.inclusion_injective _)
  have ht : Nat.card (torus F) * 3 = 9 := by
    simpa only [Matrix.PSL3Four.card_F,Nat.reduceSub,Nat.gcd_self,Nat.reducePow] using
      BorelQuotient.card_torus_mul_scalar F
  have hc : Nat.card (torus F) = 3 := Nat.eq_of_mul_eq_mul_right (by decide : 0 < 3) ht
  exact hh.trans_eq hc
theorem four_path_card (i : Bool) :
    Nat.card {p : BasedWalk modelCompletion.graph 4 (RankTwo.base modelCompletion.family i) //
      p.Nonbacktracking} = 320 := by
  have (x : modelCompletion.Vertex) : Finite (modelCompletion.graph.neighborSet x) :=
    Nat.finite_of_card_ne_zero (by rw [modelCompletion.card_neighbors]; decide)
  have hf : ∀ {x y : modelCompletion.Vertex}, modelCompletion.graph.Adj x y → y.type = !x.type := by
    intro x y h
    have hxy := h.1
    cases hx : x.type <;> cases hy : y.type <;> simp_all
  have hc := BasedWalk.card_nonbacktracking_succ modelCompletion.graph
    (fun x : modelCompletion.Vertex => x.type) (fun _ : Bool => 5)
    hf modelCompletion.card_neighbors 3 (RankTwo.base modelCompletion.family i)
  rw [hc]
  rfl

theorem four_path_transitive (i : Bool) :
    RootPathTransitive modelCompletion.graph PSL (RankTwo.base modelCompletion.family i) 4 := by
  have : Finite {p : BasedWalk modelCompletion.graph 4 (RankTwo.base modelCompletion.family i) //
      p.Nonbacktracking} := Nat.finite_of_card_ne_zero (by rw [four_path_card]; decide)
  apply rootPathTransitive_of_pathStabilizer_card_le modelCompletion.family (path i)
    (path_nonbacktracking i) (by decide : 0 < 3) (path_fixer_card_le i)
  rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base,four_path_card,native_endpoint_card]
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Native
