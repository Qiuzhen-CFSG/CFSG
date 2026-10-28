module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.NativeModel.Residual
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.InvolutionCentralizer.RepresentativeBound.UnitaryTwo
/-!
# The exact order of the native PSU₄(3) involution centralizer

A determinant-compatible pair of unitary planes is uniquely determined by
one GU₂(3) matrix and one SU₂(3) matrix, giving 96 · 24 = 2304 pairs.
The lifts preserving and interchanging the two planes are disjoint, so the
actual preimage of the projective centralizer in SU₄(3) has order 4608.
The restricted projection has the full order-four scalar kernel, leaving
centralizer order 1152. No ambient group recognition or simplicity is used.

Source: Aschbacher, *Sporadic Groups* (1994), type U₄(3), printed p.244;
unitary covering conventions are those of GLS3, §2.7.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
open RepresentativeCore
open RepresentativeCore.QuotientCore.Blocks

def determinantDiagonal (A : U 2) : U 2 := ⟨Matrix.diagonal ![A.val.det,1],by
  rw [Matrix.mem_unitaryGroup_iff']
  apply Matrix.ext
  intro i j
  have hd := (Matrix.det_of_mem_unitary A.property).1
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_succ,Matrix.star_apply,hd]⟩

def determinantDiagonalHom : U 2 →* U 2 where
  toFun := determinantDiagonal
  map_one' := by apply Subtype.ext; apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp [determinantDiagonal]
  map_mul' A B := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [determinantDiagonal,Matrix.det_mul]

theorem determinantDiagonal_det (A : U 2) : (determinantDiagonalHom A).val.det=A.val.det := by
  simp [determinantDiagonalHom,determinantDiagonal,Matrix.det_diagonal,Fin.prod_univ_succ]

theorem planeUnitary_injective : Function.Injective planeUnitary := by
  intro A B h
  exact Subtype.ext (Units.ext (congrArg Subtype.val h))

theorem planeUnitary_planeOfUnitary (A : U 2) (hd : A.val.det=1) :
    planeUnitary (planeOfUnitary A hd)=A := Subtype.ext rfl

abbrev CompatibleBlocks := {p : U 2 × U 2 // p.1.val.det*p.2.val.det=1}

def compatibleParam (p : U 2 × Plane) : CompatibleBlocks :=
  ⟨(p.1, determinantDiagonalHom p.1⁻¹ * planeUnitary p.2),by
    change p.1.val.det * ((determinantDiagonalHom p.1⁻¹).val * p.2.val.val).det=1
    rw [Matrix.det_mul,determinantDiagonal_det,plane_det,mul_one,← Matrix.det_mul]
    exact congrArg Matrix.det (congrArg Subtype.val (mul_inv_cancel p.1))⟩

theorem compatibleParam_bijective : Function.Bijective compatibleParam := by
  constructor
  · rintro ⟨A,C⟩ ⟨B,D⟩ h
    have hab : A=B := congrArg (fun p : CompatibleBlocks=>p.val.1) h
    subst B
    refine Prod.ext rfl ?_
    apply planeUnitary_injective
    exact mul_left_cancel (congrArg (fun p : CompatibleBlocks=>p.val.2) h)
  · rintro ⟨⟨A,B⟩,hAB⟩
    have hc : (determinantDiagonalHom A * B).val.det=1 := by
      change ((determinantDiagonalHom A).val * B.val).det=1
      rw [Matrix.det_mul,determinantDiagonal_det]
      exact hAB
    refine ⟨(A,planeOfUnitary (determinantDiagonalHom A * B) hc),?_⟩
    apply Subtype.ext
    refine Prod.ext rfl ?_
    change determinantDiagonalHom A⁻¹ * planeUnitary (planeOfUnitary _ hc)=B
    rw [planeUnitary_planeOfUnitary,map_inv,inv_mul_cancel_left]

theorem compatibleBlocks_card : Nat.card CompatibleBlocks=2304 := by
  rw [← Nat.card_congr (Equiv.ofBijective compatibleParam compatibleParam_bijective),Nat.card_prod,
    RepresentativeBound.unitaryTwo_card,plane_card]

theorem unitary_adj_mul (A : U 2) : A.val.conjTranspose*A.val=1 := A.property.1

def specialBlock (p : CompatibleBlocks) : SU :=
  ⟨Unitary.toUnits (⟨RepresentativeCore.block p.val.1.val p.val.2.val,by
    rw [Matrix.mem_unitaryGroup_iff']
    change (RepresentativeCore.block p.val.1.val p.val.2.val).conjTranspose *
      RepresentativeCore.block p.val.1.val p.val.2.val=1
    rw [block_adj,RepresentativeCore.block_mul,unitary_adj_mul,unitary_adj_mul,block_one]⟩ : U 4),by
    rw [HermitianForm.mem_specialSubgroup_iff]
    constructor
    · change (RepresentativeCore.block p.val.1.val p.val.2.val).conjTranspose * 1 *
        RepresentativeCore.block p.val.1.val p.val.2.val=1
      rw [mul_one,block_adj,RepresentativeCore.block_mul,unitary_adj_mul,unitary_adj_mul,block_one]
    · apply Units.ext
      change (RepresentativeCore.block p.val.1.val p.val.2.val).det=1
      rw [block_det]
      exact p.property⟩

def specialSwap : SU := ⟨Unitary.toUnits swapUnitary,by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · change swap.conjTranspose * 1 * swap=1
    rw [show swap.conjTranspose=swap from star_swap,mul_one,swap_sq]
  · exact Units.ext swap_det⟩

abbrev centralizerLift := standardCentralizer.comap (project 4)

def centralizerLiftParam : CompatibleBlocks ⊕ CompatibleBlocks → centralizerLift
  | .inl p => ⟨specialBlock p,(project_mem_standardCentralizer_iff _).mpr
      (Or.inl (block_commutes_standard _ _))⟩
  | .inr p => ⟨specialBlock p * specialSwap,(project_mem_standardCentralizer_iff _).mpr (Or.inr (by
      change (RepresentativeCore.block p.val.1.val p.val.2.val * swap) * standardInvolutionMatrix=
        -(standardInvolutionMatrix * (RepresentativeCore.block p.val.1.val p.val.2.val * swap))
      rw [mul_assoc,swap_anti,mul_neg,← mul_assoc,block_commutes_standard,mul_assoc]))⟩

theorem centralizerLiftParam_surjective : Function.Surjective centralizerLiftParam := by
  intro g
  obtain ⟨A,B,hd,he|he⟩ := signed_exists g.val g.property
  · refine ⟨.inl ⟨(A,B),hd⟩,Subtype.ext (Subtype.ext (Units.ext he.symm))⟩
  · refine ⟨.inr ⟨(A,B),hd⟩,Subtype.ext (Subtype.ext (Units.ext he.symm))⟩

theorem top_block_swap (A B : Mat₂) : top (RepresentativeCore.block A B * swap)=0 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [top,RepresentativeCore.block,swap,Matrix.mul_apply,Fin.sum_univ_succ]

theorem unitary_block_ne_swap (A B C D : U 2) :
    RepresentativeCore.block A.val B.val ≠ RepresentativeCore.block C.val D.val * swap := by
  intro he
  have hz : A.val=0 := by simpa only [top_block,top_block_swap] using congrArg top he
  have h := A.property.1
  rw [hz,mul_zero] at h
  exact zero_ne_one h

theorem compatible_block_injective (p q : CompatibleBlocks)
    (h : RepresentativeCore.block p.val.1.val p.val.2.val = RepresentativeCore.block q.val.1.val q.val.2.val) : p=q := by
  obtain ⟨hA,hB⟩ := NormalCentralizer.block_ext h
  exact Subtype.ext (Prod.ext (Subtype.ext hA) (Subtype.ext hB))

theorem centralizerLiftParam_injective : Function.Injective centralizerLiftParam := by
  intro p q he
  have hm := congrArg (fun g : centralizerLift=>g.val.val.val) he
  cases p with
  | inl p => cases q with
    | inl q => exact congrArg Sum.inl (compatible_block_injective p q hm)
    | inr q => exact (unitary_block_ne_swap _ _ _ _ hm).elim
  | inr p => cases q with
    | inl q => exact (unitary_block_ne_swap _ _ _ _ hm.symm).elim
    | inr q =>
      apply congrArg Sum.inr
      apply compatible_block_injective
      have hh := congrArg (fun A : Mat₄=>A*swap) hm
      change (RepresentativeCore.block p.val.1.val p.val.2.val * swap) * swap =
        (RepresentativeCore.block q.val.1.val q.val.2.val * swap) * swap at hh
      simpa only [mul_assoc,swap_sq,mul_one] using hh

theorem centralizerLift_card : Nat.card centralizerLift=4608 := by
  rw [← Nat.card_congr (Equiv.ofBijective centralizerLiftParam
    ⟨centralizerLiftParam_injective,centralizerLiftParam_surjective⟩),Nat.card_sum,compatibleBlocks_card]

def centralizerProjection : centralizerLift →* standardCentralizer :=
  ((project 4).comp centralizerLift.subtype).codRestrict _ (fun g=>g.property)

theorem centralizerProjection_surjective : Function.Surjective centralizerProjection := by
  intro g
  obtain ⟨a,ha⟩ := project_surjective 4 g.val
  refine ⟨⟨a,?_⟩,Subtype.ext ha⟩
  change project 4 a∈standardCentralizer
  rw [ha]
  exact g.property

theorem centralizerProjection_kernel_card : Nat.card centralizerProjection.ker=4 := by
  have hk : centralizerProjection.ker=(project 4).ker.subgroupOf centralizerLift := by
    ext g
    change centralizerProjection g=1 ↔ project 4 g.val=1
    exact Subtype.ext_iff
  rw [hk,Nat.card_congr (subgroupOfEquivOfLe (show (project 4).ker ≤ centralizerLift from
    ker_le_comap (project 4) standardCentralizer)).toEquiv]
  change Nat.card (ProjectiveKernel.project (form 4)).ker=4
  rw [ProjectiveKernel.card_project_kernel (form 4) (form_conj_cube 4) (show Nat.card FiniteField.Nine=3^2 by norm_num)]
  decide

theorem native_centralizer_card : Nat.card standardCentralizer=1152 := by
  have hc := centralizerProjection.ker.card_mul_index
  rw [index_ker,centralizerProjection_kernel_card,centralizerLift_card,
    MonoidHom.range_eq_top_of_surjective _ centralizerProjection_surjective,card_top] at hc
  omega

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
