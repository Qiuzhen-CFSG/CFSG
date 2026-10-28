module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.ModelSeparation
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-!
# General unitary-five Borel kernels are projective scalars

Coordinate reversal makes a normal Borel subgroup both upper and lower
triangular. Conjugation by A(1) and B(1,κ), with trace(κ)=1, then equates all
five diagonal entries. The actual basis change transports that scalar back
to the original carrier, and the determinant supplies its nonzero fifth-root
condition. Thus a homomorphism kernel trapped in this generated Borel lies
in the canonical SU₅→PSU₅ kernel. No simplicity, field cardinality, or q=4
assumption is used. The generated Borel is kept explicit pending its full
flag identification. Source: the elementary core argument following the
Bruhat decomposition, Steinberg, Lectures on Chevalley Groups, Theorem 4;
projective convention as in DGS, Theorem D, printed p.224.
-/
@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveCells
open FivePositive FiveWeyl
open Theory.SpecificGroups.UnitaryFive
open PlaneCore SmallCompletion FivePaths
variable {E : Type*} [Field E] [CharP E 2]
variable (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)

private def reverseMatrix : Matrix (Fin 5) (Fin 5) E :=
  !![0,0,0,0,1;0,0,0,1,0;0,0,1,0,0;0,1,0,0,0;1,0,0,0,0]

omit [CharP E 2] in
private theorem reverse_conj (M : Matrix (Fin 5) (Fin 5) E) (i j : Fin 5) :
    ((reverseMatrix (E := E))*M*(reverseMatrix (E := E))) i j=M i.rev j.rev := by
  fin_cases i <;> fin_cases j <;>
    simp [reverseMatrix,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ,Fin.rev]

omit [CharP E 2] in
private theorem diagonal_of_reverse (M : Matrix (Fin 5) (Fin 5) E)
    (hM : M.IsUpperTriangular) (hR : ((reverseMatrix (E := E))*M*(reverseMatrix (E := E))).IsUpperTriangular) :
    M=Matrix.diagonal (fun i => M i i) := by
  ext i j
  by_cases hij : i=j
  · subst j; simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    rcases lt_or_gt_of_ne hij with hij|hij
    · have h := hR (Fin.rev_lt_rev.mpr hij)
      rw [reverse_conj] at h
      change M i.rev.rev j.rev.rev=0 at h
      simpa only [Fin.rev_rev] using h
    · exact hM hij

private theorem normal_mem_diagonal (N : Subgroup J.specialSubgroup) [N.Normal]
    (hN : N≤(roots J κ hκ hJ).borel (h J κ hκ hJ))
    (a : J.specialSubgroup) (ha : a∈N) :
    evaluate J κ a=Matrix.diagonal (fun i => evaluate J κ a i i) := by
  let w := (s J κ hκ hJ*t J κ hκ hJ)^2
  have hww : w*w=1 := by
    rw [←pow_two]
    change ((s J κ hκ hJ*t J κ hκ hJ)^2)^2=1
    rw [←pow_mul]
    exact st_four J κ hκ hJ
  have hwi : w⁻¹=w := inv_eq_of_mul_eq_one_left hww
  have he : evaluate J κ w=reverseMatrix (E := E) := by
    change evaluate J κ ((s J κ hκ hJ*t J κ hκ hJ)^2)=_
    rw [map_pow,map_mul,evaluate_s,evaluate_t,Matrix5.ST_sq]
    rfl
  have hcon : w*a*w∈N := by
    simpa only [hwi] using Subgroup.Normal.conj_mem (inferInstance : N.Normal) a ha w
  apply diagonal_of_reverse _ (borel_triangular J κ hκ hJ (hN ha))
  have hh := borel_triangular J κ hκ hJ (hN hcon)
  simpa only [map_mul,he] using hh

/-- A normal subgroup inside the generated unitary Borel consists of scalars,
with no field-order or simplicity assumption. -/
theorem normal_le_borel_scalar (N : Subgroup J.specialSubgroup) [N.Normal]
    (hN : N≤(roots J κ hκ hJ).borel (h J κ hκ hJ))
    (a : J.specialSubgroup) (ha : a∈N) :
    ∃ z : E, evaluate J κ a=Matrix.diagonal (fun _ => z) := by
  have had := normal_mem_diagonal J κ hκ hJ N hN a ha
  have hcomm (r : J.specialSubgroup) (hr : ∀ i, evaluate J κ r i i=1) (i j : Fin 5) :
      evaluate J κ r i j*evaluate J κ a j j=evaluate J κ a i i*evaluate J κ r i j := by
    let b := r*a*r⁻¹
    have hb : b∈N := Subgroup.Normal.conj_mem inferInstance a ha r
    have hbd := normal_mem_diagonal J κ hκ hJ N hN b hb
    have he : r*a=b*r := by dsimp [b]; group
    have hm := congrArg (evaluate J κ) he
    simp only [map_mul] at hm
    rw [had,hbd] at hm
    have hbdiag (k : Fin 5) : evaluate J κ b k k=evaluate J κ a k k := by
      have hk := congrArg (fun M : Matrix (Fin 5) (Fin 5) E => M k k) hm
      simpa only [Matrix.mul_diagonal,Matrix.diagonal_mul,hr k,one_mul,mul_one] using hk.symm
    have hij := congrArg (fun M : Matrix (Fin 5) (Fin 5) E => M i j) hm
    simpa only [Matrix.mul_diagonal,Matrix.diagonal_mul,hbdiag] using hij
  have hA (i : Fin 5) : evaluate J κ (A J κ hκ hJ 1) i i=1 := by
    rw [evaluate_A]
    fin_cases i <;> rfl
  let p : Parameter J := ⟨(1,κ),by
    change κ+J.conj κ+1*J.conj 1=0
    rw [hκ,map_one,one_mul,CharTwo.add_self_eq_zero]⟩
  have hB (i : Fin 5) : evaluate J κ (B J hJ p) i i=1 := by
    rw [evaluate_B]
    fin_cases i <;> rfl
  have h01 : evaluate J κ a 1 1=evaluate J κ a 0 0 := by
    simpa [evaluate_A,Matrix5.A] using hcomm (A J κ hκ hJ 1) hA 0 1
  have h34 : evaluate J κ a 4 4=evaluate J κ a 3 3 := by
    simpa [evaluate_A,Matrix5.A] using hcomm (A J κ hκ hJ 1) hA 3 4
  have h12 : evaluate J κ a 2 2=evaluate J κ a 1 1 := by
    simpa [evaluate_B,Matrix5.B,p] using hcomm (B J hJ p) hB 1 2
  have h23 : evaluate J κ a 3 3=evaluate J κ a 2 2 := by
    simpa [evaluate_B,Matrix5.B,p] using hcomm (B J hJ p) hB 2 3
  refine ⟨evaluate J κ a 0 0,had.trans ?_⟩
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact h01
  · exact h12.trans h01
  · exact h23.trans (h12.trans h01)
  · exact h34.trans (h23.trans (h12.trans h01))

/-- Being scalar in the presentation basis is equivalent to being scalar in
the original identity-form model; the actual basis change is retained. -/
theorem literal_scalar_of_evaluate_scalar (a : J.specialSubgroup) (z : E)
    (ha : evaluate J κ a=Matrix.diagonal (fun _ => z)) :
    a.val.val=Matrix.diagonal (fun _ => z) := by
  have hc : (coordinates J κ a).val=Matrix.diagonal (fun _ => z) := by
    apply (Matrix.reindexRingEquiv E orderSwap).injective
    change evaluate J κ a=Matrix.reindexRingEquiv E orderSwap (Matrix.diagonal (fun _ => z))
    rw [ha]
    ext i j
    simp [Matrix.reindexRingEquiv,Matrix.reindex,Matrix.diagonal_apply]
  rw [coordinates_val] at hc
  have hm := congrArg (fun M : Matrix (Fin 5) (Fin 5) E => planeBasis κ*M*planeBasisInv κ) hc
  simp only [←Matrix.mul_assoc,planeBasis_mul_inv,Matrix.one_mul] at hm
  have hz (M : Matrix (Fin 5) (Fin 5) E) : M*Matrix.diagonal (fun _ => z)=Matrix.diagonal (fun _ => z)*M := by
    ext i j
    simp [Matrix.mul_diagonal,Matrix.diagonal_mul,mul_comm]
  rw [Matrix.mul_assoc,planeBasis_mul_inv,Matrix.mul_one] at hm
  rw [hz,Matrix.mul_assoc,planeBasis_mul_inv,Matrix.mul_one] at hm
  exact hm

/-- The same normal subgroup lies in the kernel of the canonical SU₅→PSU₅
map. This keeps the scalar quotient rather than incorrectly killing it. -/
theorem normal_le_borel_le_project_kernel (N : Subgroup J.specialSubgroup) [N.Normal]
    (hN : N≤(roots J κ hκ hJ).borel (h J κ hκ hJ)) : N≤(project J).ker := by
  intro a ha
  obtain ⟨z,hz⟩ := normal_le_borel_scalar J κ hκ hJ N hN a ha
  have hl := literal_scalar_of_evaluate_scalar J κ a z hz
  have hdU : GeneralLinearGroup.det a.val=1 := ((J.mem_specialSubgroup_iff a.val).mp a.property).2
  have hd : a.val.val.det=1 := by
    simpa only [GeneralLinearGroup.val_det_apply,Units.val_one] using
      congrArg (fun u : Eˣ => (u:E)) hdU
  have hz5 : z^5=1 := by
    rw [hl,Matrix.det_diagonal] at hd
    simpa using hd
  have hz0 : z≠0 := by intro hz; simp [hz] at hz5
  have he : a.val=GeneralLinearGroup.scalar (Fin 5) (Units.mk0 z hz0) := by
    apply Units.ext
    ext i j
    simp [GeneralLinearGroup.coe_scalar,Matrix.scalar,Matrix.diagonal_apply,hl,Pi.algebraMap_apply]
  change project J a=1
  apply Subtype.ext
  change ProjGenLinGroup.mk a.val=1
  rw [he]
  exact ProjGenLinGroup.mk_scalar _

/-- Consumer: any homomorphism whose kernel is trapped in this Borel has
only canonical projective scalars in its kernel. -/
theorem kernel_le_project_kernel {Y : Type*} [Group Y] (f : J.specialSubgroup →* Y)
    (hf : f.ker≤(roots J κ hκ hJ).borel (h J κ hκ hJ)) : f.ker≤(project J).ker :=
  normal_le_borel_le_project_kernel J κ hκ hJ f.ker hf
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveCells
