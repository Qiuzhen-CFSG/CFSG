module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Relations
/-! Checked square and two-generator conjugation words for the literal outer
actor. The core involution supplies the semidihedral conjugation relation. -/

@[expose] public section
open Subgroup
namespace Tits.Max4Outer
open MinimumIndexCandidates

def coreGen : Fin 2 → Atlas1600Group := ![max4Generators.1,max4Generators.2]
def corePacked : Fin 2 → Equiv.Perm (Fin 1600) :=
  ![OrderCertificate.Max4.L0Gen 0,OrderCertificate.Max4.L0Gen 1]

theorem coreGen_val (i : Fin 2) : (coreGen i).val=corePacked i := by
  fin_cases i
  · exact (Max4Projective.sourceGen_spec 0).symm
  · exact (Max4Projective.sourceGen_spec 1).symm

def coreWord : Fin 2 → List (ParrottGenerator × Bool) :=
  ![[(.s4, false), (.r8, false), (.s3, false), (.s3, false), (.r1, true), (.r8, true), (.r1, true), (.s4, true), (.r8, false), (.r1, false), (.r8, false), (.r1, false), (.r8, false), (.s3, false), (.s3, false), (.s8, false), (.s3, false), (.s3, false), (.r8, false), (.s7, false), (.r1, false), (.s5, true), (.r8, false)],
    [(.s4, false), (.r8, false), (.s3, false), (.s3, false), (.r8, false), (.r8, false), (.r1, false), (.r8, true), (.r1, true), (.r8, true), (.s4, true), (.s8, true), (.s3, false), (.s3, false), (.s6, false), (.s5, false), (.r1, false), (.r8, false), (.r1, false), (.s3, false), (.s3, false)]]

def squareWord : List (Fin 2 × Bool) := [(1, true), (1, true), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true)]

def actionWord : Fin 2 → List (Fin 2 × Bool) := ![[(1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false)],
  [(0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (1, false)]]

def reflectionWord : List (Fin 2 × Bool) := [(1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false)]

theorem eval_core_val (w : List (Fin 2 × Bool)) :
    (eval coreGen w).val=eval corePacked w := by
  change Max4Projective.sourceEmbedding (eval coreGen w)=_
  rw [map_eval]
  change eval (fun i=>(coreGen i).val) w=_
  simp only [coreGen_val]

theorem eval_parrott_val (w : List (ParrottGenerator × Bool)) :
    (eval atlas1600ParrottAssignment w).val=eval packed w := by
  change Max4Projective.sourceEmbedding (eval atlas1600ParrottAssignment w)=_
  rw [map_eval]
  change eval (fun i=>(atlas1600ParrottAssignment i).val) w=_
  simp only [← packed_eq]

theorem coreWord_eq (i : Fin 2) : eval atlas1600ParrottAssignment (coreWord i)=coreGen i := by
  apply ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext
  all_goals rw [eval_parrott_val,coreGen_val]
  all_goals fin_cases i <;> decide +kernel

def squareElement : Atlas1600Group := (eval coreGen squareWord)⁻¹

theorem squareElement_val : squareElement.val=(eval corePacked squareWord)⁻¹ := by
  change ((eval coreGen squareWord).val)⁻¹=_
  rw [eval_core_val]

theorem val_mul (x y : Atlas1600Group) : (x*y).val=x.val*y.val := rfl
theorem val_inv (x : Atlas1600Group) : x⁻¹.val=x.val⁻¹ := rfl

theorem square_certificate (i : ParrottGenerator) : eval assignment (word i)=
    squareElement * atlas1600ParrottAssignment i * squareElement⁻¹ := by
  apply ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext
  all_goals rw [eval_assignment_val]
  all_goals simp only [val_mul,val_inv,squareElement_val,← packed_eq]
  all_goals cases i <;> decide +kernel

theorem action_certificate (i : Fin 2) : eval assignment (coreWord i)=eval coreGen (actionWord i) := by
  apply ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext
  all_goals rw [eval_assignment_val,eval_core_val]
  all_goals fin_cases i <;> decide +kernel


def reflection : Atlas1600Group := eval coreGen reflectionWord

theorem reflection_val : reflection.val=eval corePacked reflectionWord := eval_core_val _

theorem square_four : squareElement^4=1 := by
  apply ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext
  all_goals change ((squareElement.val)^4) _ = _
  all_goals rw [squareElement_val]
  all_goals decide +kernel

theorem square_sq_ne : squareElement^2≠1 := by
  intro he
  have h := congrArg (fun x : Atlas1600Group => x.val 0) he
  have hn : (squareElement.val^2) 0≠0 := by rw [squareElement_val]; decide +kernel
  exact hn h

theorem reflection_square : reflection^2=1 := by
  apply ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext
  all_goals change ((reflection.val)^2) _ = _
  all_goals rw [reflection_val]
  all_goals decide +kernel

theorem reflection_ne : reflection≠1 := by
  intro he
  have h := congrArg (fun x : Atlas1600Group => x.val 1) he
  have hn : reflection.val 1≠1 := by rw [reflection_val]; decide +kernel
  exact hn h

theorem reflection_image_certificate :
    eval (fun i=>eval coreGen (actionWord i)) reflectionWord = reflection*squareElement := by
  apply ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext
  all_goals change (Max4Projective.sourceEmbedding (eval (fun i=>eval coreGen (actionWord i)) reflectionWord)) _ = _
  all_goals rw [map_eval]
  all_goals simp only [show ∀ i, Max4Projective.sourceEmbedding (eval coreGen (actionWord i)) =
    eval corePacked (actionWord i) from fun i => eval_core_val _,val_mul,reflection_val,squareElement_val]
  all_goals decide +kernel

end Tits.Max4Outer
