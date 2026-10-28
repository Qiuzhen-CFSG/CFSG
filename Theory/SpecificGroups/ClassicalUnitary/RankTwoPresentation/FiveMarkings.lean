module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveElimination
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.ModelSeparation
import Mathlib.Tactic.Group

/-!
# The full unitary-five Borel and both marked parabolics

Whole-model Bruhat coverage and literal permutation pivots identify the
generated root-and-torus Borel with the entire line/plane flag stabilizer.
The same eight cells show that adjoining t gives the point parabolic and
adjoining s gives the plane parabolic. These are statements about the actual
SU₅ matrices for every finite parameter; no scalar quotient is suppressed.
Source: Steinberg, Lectures on Chevalley Groups, Theorems 4 and 33;
DGS, Groups and Graphs, the unitary quadrangles on printed p.209.
-/
@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveCells
open FivePositive FiveWeyl FiveCoordinates
open Theory.SpecificGroups.UnitaryFive PlaneCore SmallCompletion FivePaths
variable {E : Type*} [Field E] [Finite E] [CharP E 2]
variable (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)
local notation "BB" => PositiveMaps.borel (roots J κ hκ hJ) (h J κ hκ hJ)

/-- Unconditional Bruhat coverage of the entire special-unitary five-space. -/
theorem all_eight_cells (g : J.specialSubgroup) :
    ∃ w : WeylWord, InCell BB (w.eval (s J κ hκ hJ) (t J κ hκ hJ)) g := by
  apply eight_cells J κ hκ hJ
  rw [FiveElimination.fullGenerated_eq_top J κ hκ hJ]
  trivial

theorem borel_le_flag : BB≤specialStabilizer J (line E) ⊓ specialStabilizer J (plane E) := by
  intro g hg
  have ht := borel_triangular J κ hκ hJ hg
  constructor
  · apply (mem_line_iff J κ g).mpr
    intro i hi
    exact ht (Fin.pos_iff_ne_zero.mpr hi)
  · apply (mem_plane_iff J κ g).mpr
    intro i j hi hj
    apply ht
    rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl <;> decide

theorem weyl_mem_line_iff (w : WeylWord) :
    w.eval (s J κ hκ hJ) (t J κ hκ hJ)∈specialStabilizer J (line E) ↔ w=.one ∨ w=.t := by
  rw [mem_line_iff J κ]
  simp only [WeylWord.map_eval,evaluate_s,evaluate_t]
  cases w <;> simp [WeylWord.eval,Matrix5.S,Matrix5.T,Fin.forall_fin_succ,
    Matrix.mul_apply,Fin.sum_univ_succ]

theorem weyl_mem_plane_iff (w : WeylWord) :
    w.eval (s J κ hκ hJ) (t J κ hκ hJ)∈specialStabilizer J (plane E) ↔ w=.one ∨ w=.s := by
  rw [mem_plane_iff J κ]
  simp only [WeylWord.map_eval,evaluate_s,evaluate_t]
  cases w <;> simp [WeylWord.eval,Matrix5.S,Matrix5.T,Fin.forall_fin_succ,
    Matrix.mul_apply,Fin.sum_univ_succ]

/-- The generated Borel is the FULL literal overlap, including every odd
Cartan factor and every projective scalar. -/
theorem borel_eq_flag : BB=specialStabilizer J (line E) ⊓ specialStabilizer J (plane E) := by
  apply le_antisymm (borel_le_flag J κ hκ hJ)
  intro g hg
  obtain ⟨w,l,hl,v,hv,he⟩ := all_eight_cells J κ hκ hJ g
  let P := specialStabilizer J (line E) ⊓ specialStabilizer J (plane E)
  have hn : w.eval (s J κ hκ hJ) (t J κ hκ hJ)∈P := by
    have hh : w.eval (s J κ hκ hJ) (t J κ hκ hJ)=l⁻¹*g*v⁻¹ := by rw [he]; group
    rw [hh]
    exact P.mul_mem (P.mul_mem (P.inv_mem (borel_le_flag J κ hκ hJ hl)) hg)
      (P.inv_mem (borel_le_flag J κ hκ hJ hv))
  have hw0 := (weyl_mem_line_iff J κ hκ hJ w).mp hn.1
  have hw1 := (weyl_mem_plane_iff J κ hκ hJ w).mp hn.2
  have hw : w=.one := by rcases hw0 with rfl|rfl <;> simp_all
  subst w
  exact InCell.mem_of_one ⟨l,hl,v,hv,he⟩

/-- Literal point stabilizer generation by the full overlap and the point
reflection, with no line-Levi splitting premise. -/
theorem line_eq_generated :
    specialStabilizer J (line E)=BB ⊔ closure {t J κ hκ hJ} := by
  apply le_antisymm
  · intro g hg
    obtain ⟨w,l,hl,v,hv,he⟩ := all_eight_cells J κ hκ hJ g
    have hB : BB≤specialStabilizer J (line E) := (borel_le_flag J κ hκ hJ).trans inf_le_left
    have hn : w.eval (s J κ hκ hJ) (t J κ hκ hJ)∈specialStabilizer J (line E) := by
      have hh : w.eval (s J κ hκ hJ) (t J κ hκ hJ)=l⁻¹*g*v⁻¹ := by rw [he]; group
      rw [hh]
      exact (specialStabilizer J (line E)).mul_mem
        ((specialStabilizer J (line E)).mul_mem ((specialStabilizer J (line E)).inv_mem (hB hl)) hg)
        ((specialStabilizer J (line E)).inv_mem (hB hv))
    have hW : w.eval (s J κ hκ hJ) (t J κ hκ hJ)∈BB ⊔ closure {t J κ hκ hJ} := by
      rcases (weyl_mem_line_iff J κ hκ hJ w).mp hn with rfl|rfl
      · exact (BB ⊔ closure {t J κ hκ hJ}).one_mem
      · exact Subgroup.mem_sup_right (subset_closure (Set.mem_singleton _))
    rw [he]
    exact (BB ⊔ closure {t J κ hκ hJ}).mul_mem
      ((BB ⊔ closure {t J κ hκ hJ}).mul_mem (Subgroup.mem_sup_left hl) hW) (Subgroup.mem_sup_left hv)
  · apply sup_le ((borel_le_flag J κ hκ hJ).trans inf_le_left)
    apply (Subgroup.closure_le _).2
    rintro x rfl
    exact middleSwap_mem_line J κ hκ hJ

/-- Literal plane stabilizer generation, with its prescribed other reflection. -/
theorem plane_eq_generated :
    specialStabilizer J (plane E)=BB ⊔ closure {s J κ hκ hJ} := by
  apply le_antisymm
  · intro g hg
    obtain ⟨w,l,hl,v,hv,he⟩ := all_eight_cells J κ hκ hJ g
    have hB : BB≤specialStabilizer J (plane E) := (borel_le_flag J κ hκ hJ).trans inf_le_right
    have hn : w.eval (s J κ hκ hJ) (t J κ hκ hJ)∈specialStabilizer J (plane E) := by
      have hh : w.eval (s J κ hκ hJ) (t J κ hκ hJ)=l⁻¹*g*v⁻¹ := by rw [he]; group
      rw [hh]
      exact (specialStabilizer J (plane E)).mul_mem
        ((specialStabilizer J (plane E)).mul_mem ((specialStabilizer J (plane E)).inv_mem (hB hl)) hg)
        ((specialStabilizer J (plane E)).inv_mem (hB hv))
    have hW : w.eval (s J κ hκ hJ) (t J κ hκ hJ)∈BB ⊔ closure {s J κ hκ hJ} := by
      rcases (weyl_mem_plane_iff J κ hκ hJ w).mp hn with rfl|rfl
      · exact (BB ⊔ closure {s J κ hκ hJ}).one_mem
      · exact Subgroup.mem_sup_right (subset_closure (Set.mem_singleton _))
    rw [he]
    exact (BB ⊔ closure {s J κ hκ hJ}).mul_mem
      ((BB ⊔ closure {s J κ hκ hJ}).mul_mem (Subgroup.mem_sup_left hl) hW) (Subgroup.mem_sup_left hv)
  · apply sup_le ((borel_le_flag J κ hκ hJ).trans inf_le_right)
    apply (Subgroup.closure_le _).2
    rintro x rfl
    exact pairSwap_mem_plane J κ hκ hJ
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveCells
