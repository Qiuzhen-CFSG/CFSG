module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Equivalence
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Base
public import Theory.SpecificGroups.Tits.PresentationWords

/-! Explicit words for the order-eight outer normalizer actor of ATLAS max4.
The words use Parrott’s original ten generators. GAP supplies witnesses only;
the next module checks the original 37 relators and the native square/action.
Source: Aschbacher–Smith J.5.4, printed pp.445–446. -/

@[expose] public section
open Subgroup
namespace Tits.Max4Outer
open MinimumIndexCandidates

def eval {ι G : Type*} [Group G] (g : ι → G) : List (ι × Bool) → G
 | [] => 1
 | (i,b)::w => (if b then g i else (g i)⁻¹) * eval g w

theorem map_eval {ι G H : Type*} [Group G] [Group H] (f : G →* H) (g : ι → G)
    (w : List (ι × Bool)) : f (eval g w)=eval (fun i=>f (g i)) w := by
  induction w with
  | nil => exact f.map_one
  | cons a w ih =>
    rcases a with ⟨i,b⟩
    cases b <;> simp only [eval, Bool.false_eq_true, if_false, if_true, map_mul, map_inv, ih]

theorem lift_word {ι G : Type*} [Group G] (g : ι → G) (w : List (ι × Bool)) :
    FreeGroup.lift g (FreeGroup.mk w)=eval g w := by
  rw [FreeGroup.lift_mk]
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨i,b⟩
    cases b <;> simp only [List.map_cons,List.prod_cons,eval,cond_false,cond_true,
      Bool.false_eq_true,if_false,if_true,ih]

def word : ParrottGenerator → List (ParrottGenerator × Bool)
 | .r1 => [(.s3, true), (.s8, true), (.s7, false), (.r8, true), (.r1, true), (.r8, true), (.r1, true), (.s3, false), (.s3, false), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.s8, false), (.s3, false), (.s3, false), (.r8, false), (.s3, false), (.s3, false), (.r8, false), (.s1, true), (.s6, true)]
 | .r8 => [(.s7, true), (.s8, false), (.s3, false), (.r8, false), (.r1, false), (.r8, true), (.r1, true), (.r8, true), (.s4, true), (.s8, true), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.s3, false), (.r1, false), (.s3, false), (.r8, false), (.s8, false), (.s2, false)]
 | .s1 => [(.s3, false), (.s3, false), (.s7, false), (.s6, false), (.s7, false), (.s1, false), (.r8, false), (.r1, false), (.r8, true), (.r1, true), (.s3, true), (.s3, true), (.s4, true), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.s3, false), (.s3, false), (.r1, true), (.s5, true), (.s5, true), (.r1, true), (.r8, true)]
 | .s2 => [(.s4, false), (.s3, false), (.s3, false), (.s8, false), (.r8, true), (.r1, true), (.r8, true), (.r1, true), (.r8, true), (.r1, false), (.r8, false), (.r1, false), (.s3, false), (.s3, false), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.s3, false), (.s3, false), (.r8, false), (.s3, false), (.s3, false), (.s8, false), (.r1, true), (.s3, false), (.s5, false)]
 | .s3 => [(.s7, true), (.s8, false), (.s3, false), (.r8, true), (.r1, true), (.r8, true), (.r1, true), (.r8, true), (.s8, true), (.s3, true), (.s3, true), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.s3, false), (.s3, false), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.s3, false), (.s3, false), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.r1, true), (.s5, true)]
 | .s4 => [(.s4, false), (.s6, false), (.s5, true), (.s3, false), (.r1, true), (.r8, true), (.r1, true), (.r8, true), (.s8, true), (.s3, true), (.s3, true), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.s3, false), (.s3, false), (.s8, false), (.s3, false), (.s3, false), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.s3, false), (.s3, false), (.r1, false), (.s1, false), (.r1, false), (.r8, false), (.r1, false), (.s1, false), (.s2, false)]
 | .s5 => [(.s1, true), (.r1, true), (.r8, true), (.r1, true), (.s5, true), (.s6, true), (.s3, false), (.s3, false), (.s8, false), (.r8, false), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.s8, true), (.s3, true), (.s3, true), (.s4, true)]
 | .s6 => [(.s4, false), (.s6, false), (.s5, true), (.s3, false), (.r8, false), (.r1, false), (.r8, true), (.r1, true), (.r8, true), (.s4, true), (.s8, true), (.s3, false), (.s3, false), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.r8, false), (.r1, false), (.s1, false), (.r1, false), (.r8, false), (.r1, false), (.s1, false), (.s2, false)]
 | .s7 => [(.s6, false), (.r8, false), (.r1, false), (.r8, false), (.r1, false), (.s3, true), (.r8, false), (.r1, false), (.s3, false), (.s3, false), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.s3, false), (.s3, false), (.s5, false), (.s1, false), (.r1, false), (.r8, false), (.r1, false), (.s1, false), (.s2, false)]
 | .s8 => [(.s4, false), (.s3, false), (.s3, false), (.r8, false), (.s3, false), (.s3, false), (.r1, true), (.r8, true), (.r1, true), (.s4, true), (.r8, false), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.s3, false), (.s3, false), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.s8, false), (.s3, false), (.s1, false), (.r1, false), (.r8, false), (.r1, false), (.s2, false), (.s7, false)]

def packed : ParrottGenerator → Equiv.Perm (Fin 1600)
 | .r1 => OuterOddSubgroups.OverlapCentralizers.Packed.perm 0
 | .r8 => OuterOddSubgroups.OverlapCentralizers.Packed.perm 1
 | .s1 => OuterOddSubgroups.OverlapCentralizers.Packed.perm 2
 | .s2 => OuterOddSubgroups.OverlapCentralizers.Packed.perm 3
 | .s3 => OuterOddSubgroups.OverlapCentralizers.Packed.perm 4
 | .s4 => OuterOddSubgroups.OverlapCentralizers.Packed.perm 5
 | .s5 => OuterOddSubgroups.OverlapCentralizers.Packed.perm 6
 | .s6 => OuterOddSubgroups.OverlapCentralizers.Packed.perm 7
 | .s7 => OuterOddSubgroups.OverlapCentralizers.Packed.perm 8
 | .s8 => OuterOddSubgroups.OverlapCentralizers.Packed.perm 9

theorem packed_eq (i : ParrottGenerator) : packed i=(atlas1600ParrottAssignment i).val := by
  rw [atlas1600ParrottAssignment_val]
  cases i <;> simp only [packed,OuterOddSubgroups.OverlapCentralizers.Packed.perm_eq,OuterOddSubgroups.OverlapCentralizers.Packed.generator,Atlas1600ParrottData.permutation] <;> rfl

def assignment (i : ParrottGenerator) : Atlas1600Group := eval atlas1600ParrottAssignment (word i)

theorem assignment_val (i : ParrottGenerator) : (assignment i).val=eval packed (word i) := by
  change Max4Projective.sourceEmbedding (eval atlas1600ParrottAssignment (word i))=_
  rw [map_eval]
  change eval (fun j => (atlas1600ParrottAssignment j).val) (word i) = _
  simp only [← packed_eq]

theorem eval_assignment_val (w : List (ParrottGenerator × Bool)) :
    (eval assignment w).val=eval (fun i=>eval packed (word i)) w := by
  change Max4Projective.sourceEmbedding (eval assignment w)=_
  rw [map_eval]
  change eval (fun i => (assignment i).val) w = _
  simp only [assignment_val]

end Tits.Max4Outer
