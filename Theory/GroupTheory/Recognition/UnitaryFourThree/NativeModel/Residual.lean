module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.NativeModel.Factors
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore.Blocks
public import Theory.GroupTheory.Recognition.UnitaryFourThree.Defs
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.Recognition.UnitaryFourThree.Factors
/-!
# The actual two-residual of the native PSU₄(3) involution centralizer

The two special-unitary plane images are normal in their product and intersect
in the marked involution line. The full projective centralizer normalizes their
product: its lifts either preserve or interchange the two unitary blocks.
The determinant equations make the quotient a two-group of exponent dividing
four. Two-perfectness of both SL₂(3) factors identifies the original O²(C).
The existing quaternion core is then O₂(O²(C)) and the actual F*(C).

Source: Aschbacher, *Sporadic Groups* (1994), Hypothesis 45.1 and Lemma 45.2,
printed p.242. All maps are the concrete SU₄(3)-to-PGL projection.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
open RepresentativeCore
open RepresentativeCore.QuotientCore.Blocks

def planeOfUnitary (A : U 2) (hd : A.val.det = 1) : Plane :=
  ⟨Unitary.toUnits A, by
    rw [HermitianForm.mem_specialSubgroup_iff]
    refine ⟨?_, Units.ext hd⟩
    change star A.val * 1 * A.val = 1
    simpa only [mul_one] using A.property.1⟩

theorem planeOfUnitary_val (A : U 2) (h : A.val.det=1) :
    (planeOfUnitary A h).val.val=A.val := rfl

def planeUnitary (A : Plane) : U 2 :=
  ⟨A.val.val, by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    have h := ((form 2).mem_specialSubgroup_iff A.val).mp A.property
    have hu := h.1
    change star A.val.val * 1 * A.val.val = 1 at hu
    simpa only [mul_one] using hu⟩

theorem plane_det (A : Plane) : A.val.val.det = 1 := by
  exact congrArg Units.val (((form 2).mem_specialSubgroup_iff A.val).mp A.property).2

def planeConj (A : U 2) (B : Plane) : Plane :=
  planeOfUnitary (A * planeUnitary B * A⁻¹) (by
    change (A.val * B.val.val * (A⁻¹).val).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, plane_det, mul_one, ← Matrix.det_mul]
    change (A * A⁻¹).val.det = 1
    rw [mul_inv_cancel]
    exact Matrix.det_one)

def pairHom : Plane × Plane →* Carrier 4 :=
  (project 4).comp (OddFundamental.block conjugation star_involutive)

theorem pairHom_mul (A B : Plane) : pairHom (A,B) = leftHom A * rightHom B := by
  have h := map_mul pairHom (A,1) (1,B)
  have hl : pairHom (A,1) = leftHom A := by apply Subtype.ext; rfl
  have hr : pairHom (1,B) = rightHom B := by apply Subtype.ext; rfl
  simpa only [Prod.mk_mul_mk, mul_one, one_mul, hl, hr] using h

theorem pairHom_matrix (A B : Plane) :
    (OddFundamental.block conjugation star_involutive (A,B)).val.val =
      RepresentativeCore.block A.val.val B.val.val := block_eq _ _

theorem pairHom_range : pairHom.range = factorJoin := by
  apply le_antisymm
  · rintro x ⟨⟨A,B⟩,rfl⟩
    rw [pairHom_mul]
    exact mul_mem ((show leftFactor ≤ factorJoin from le_sup_left) ⟨A,rfl⟩)
      ((show rightFactor ≤ factorJoin from le_sup_right) ⟨B,rfl⟩)
  · apply sup_le
    · rintro x ⟨A,rfl⟩; exact ⟨(A,1),by rw [pairHom_mul,map_one,mul_one]⟩
    · rintro x ⟨B,rfl⟩; exact ⟨(1,B),by rw [pairHom_mul,map_one,one_mul]⟩

theorem factorJoin_mem_iff (x : Carrier 4) : x ∈ factorJoin ↔ ∃ A B : Plane, pairHom (A,B)=x := by
  rw [← pairHom_range]
  constructor
  · rintro ⟨⟨A,B⟩,h⟩; exact ⟨A,B,h⟩
  · rintro ⟨A,B,h⟩; exact ⟨(A,B),h⟩

def quaternionPlane : QuaternionGroup 2 →* Plane :=
  quaternionMatrixHom.toHomUnits.codRestrict _ (by
    intro q
    rw [HermitianForm.mem_specialSubgroup_iff]
    refine ⟨?_, Units.ext (quaternionMatrix_det q)⟩
    change (quaternionMatrix q).conjTranspose * 1 * quaternionMatrix q = 1
    simpa only [mul_one] using quaternionMatrix_unitary q)

theorem pairHom_quaternion (q : QuaternionGroup 2 × QuaternionGroup 2) :
    pairHom (quaternionPlane q.1,quaternionPlane q.2) = (quaternionPair q).val := by
  apply congrArg (project 4)
  apply Subtype.ext
  apply Units.ext
  exact block_eq _ _

theorem quaternionCore_le_factorJoin : quaternionCore.map standardCentralizer.subtype ≤ factorJoin := by
  rintro x ⟨a,⟨q,rfl⟩,rfl⟩
  change (quaternionPair q).val ∈ factorJoin
  rw [← pairHom_quaternion, ← pairHom_range]
  exact ⟨_,rfl⟩


theorem pair_project_eq (A B : Plane) (g : SU)
    (hm : RepresentativeCore.block A.val.val B.val.val = g.val.val) :
    pairHom (A,B)=project 4 g := by
  apply congrArg (project 4)
  apply Subtype.ext
  apply Units.ext
  exact (block_eq _ _).trans hm

theorem su_pow (g : SU) (n : ℕ) : (g^n).val.val=g.val.val^n := map_pow matrixHom g n

theorem block_conjugate_swap (A B C D : Mat₂) :
    (RepresentativeCore.block A B * swap) * RepresentativeCore.block C D *
      (swap * RepresentativeCore.block A.conjTranspose B.conjTranspose) =
    RepresentativeCore.block (A*D*A.conjTranspose) (B*C*B.conjTranspose) := by
  calc
    _ = RepresentativeCore.block A B * (swap * RepresentativeCore.block C D * swap) *
      RepresentativeCore.block A.conjTranspose B.conjTranspose := by simp only [mul_assoc]
    _ = _ := by
      rw [swap_block,mul_assoc _ swap swap,swap_sq,mul_one,
        RepresentativeCore.block_mul,RepresentativeCore.block_mul]

theorem conjugate_pair_mem (g : SU) (hg : project 4 g ∈ standardCentralizer)
    (C D : Plane) : project 4 g * pairHom (C,D) * (project 4 g)⁻¹ ∈ factorJoin := by
  obtain ⟨A,B,_,he | he⟩ := signed_exists g hg
  · apply (factorJoin_mem_iff _).mpr
    refine ⟨planeConj A C,planeConj B D,?_⟩
    change pairHom _ = project 4 g * project 4 _ * (project 4 g)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    apply pair_project_eq
    change _ = g.val.val * OddFundamental.blockMatrix C.val.val D.val.val * (g⁻¹).val.val
    rw [block_eq,su_inv,he,block_adj,RepresentativeCore.block_mul,RepresentativeCore.block_mul]
    rfl
  · apply (factorJoin_mem_iff _).mpr
    refine ⟨planeConj A D,planeConj B C,?_⟩
    change pairHom _ = project 4 g * project 4 _ * (project 4 g)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    apply pair_project_eq
    change _ = g.val.val * OddFundamental.blockMatrix C.val.val D.val.val * (g⁻¹).val.val
    rw [block_eq,su_inv,he,Matrix.conjTranspose_mul,block_adj,
      show swap.conjTranspose=swap from star_swap,block_conjugate_swap]
    rfl

theorem factorJoin_normal : (factorJoin.subgroupOf standardCentralizer).Normal := by
  constructor
  intro x hx g
  obtain ⟨a,ha⟩ := project_surjective 4 g.val
  obtain ⟨C,D,hCD⟩ := (factorJoin_mem_iff x.val).mp hx
  change g.val * x.val * g.val⁻¹ ∈ factorJoin
  rw [← ha, ← hCD]
  exact conjugate_pair_mem a (ha ▸ g.property) C D

theorem unitary_det_four (A : U 2) : A.val.det ^ 4 = 1 := by
  have h : ∀ d : FiniteField.Nine, star d * d = 1 → d^4=1 := by decide
  exact h _ (Matrix.det_of_mem_unitary A.property).1

theorem fourth_mem_factorJoin (g : SU) (hg : project 4 g ∈ standardCentralizer) :
    (project 4 g)^4 ∈ factorJoin := by
  obtain ⟨A,B,hd,he | he⟩ := signed_exists g hg
  · apply (factorJoin_mem_iff _).mpr
    have ha : (A^4).val.det=1 := by rw [SubmonoidClass.coe_pow,Matrix.det_pow]; exact unitary_det_four A
    have hb : (B^4).val.det=1 := by rw [SubmonoidClass.coe_pow,Matrix.det_pow]; exact unitary_det_four B
    refine ⟨planeOfUnitary (A^4) ha,planeOfUnitary (B^4) hb,?_⟩
    rw [← map_pow]
    apply pair_project_eq
    calc
      _ = RepresentativeCore.block (A^4).val (B^4).val := congrArg₂ RepresentativeCore.block
        (planeOfUnitary_val _ _) (planeOfUnitary_val _ _)
      _ = RepresentativeCore.block (A.val^4) (B.val^4) := congrArg₂ RepresentativeCore.block
        (SubmonoidClass.coe_pow A 4) (SubmonoidClass.coe_pow B 4)
      _ = _ := ((su_pow g 4).trans ((congrArg (fun x : Mat₄ => x^4) he).trans
        (block_pow A.val B.val 4))).symm
  · have h2 : (project 4 g)^2 ∈ factorJoin := by
      apply (factorJoin_mem_iff _).mpr
      have ha : (A*B).val.det=1 := by change (A.val*B.val).det=1; rwa [Matrix.det_mul]
      have hb : (B*A).val.det=1 := by change (B.val*A.val).det=1; rw [Matrix.det_mul,mul_comm]; exact hd
      refine ⟨planeOfUnitary (A*B) ha,planeOfUnitary (B*A) hb,?_⟩
      rw [← map_pow]
      apply pair_project_eq
      rw [su_pow,he,pow_two]
      change RepresentativeCore.block (A.val*B.val) (B.val*A.val) = _
      calc
        _ = RepresentativeCore.block A.val B.val * (swap * RepresentativeCore.block A.val B.val) * swap := by
          rw [swap_block,← mul_assoc,RepresentativeCore.block_mul,mul_assoc,swap_sq,mul_one]
        _ = _ := by simp only [mul_assoc]
    simpa only [← pow_mul] using factorJoin.pow_mem h2 2

theorem factorJoin_quotient_twoGroup :
    letI := factorJoin_normal
    IsPGroup 2 (standardCentralizer ⧸ factorJoin.subgroupOf standardCentralizer) := by
  let := factorJoin_normal
  intro x
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (factorJoin.subgroupOf standardCentralizer) x
  refine ⟨2,?_⟩
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  obtain ⟨a,ha⟩ := project_surjective 4 g.val
  change g.val ^ 4 ∈ factorJoin
  rw [← ha]
  exact fourth_mem_factorJoin a (ha ▸ g.property)

theorem residual_eq_factorJoin :
    Theory.GroupTheory.Recognition.UnitaryFourThree.residual standardInvolution = factorJoin := by
  let H := factorJoin.subgroupOf standardCentralizer
  let := factorJoin_normal
  have hle : pResidual 2 standardCentralizer ≤ H :=
    sInf_le ⟨factorJoin_normal,factorJoin_quotient_twoGroup⟩
  apply le_antisymm
  · exact (map_mono hle).trans (map_subgroupOf_eq_of_le factorJoin_le).le
  · apply sup_le
    · let f : Plane →* standardCentralizer := leftHom.codRestrict _ leftHom_mem
      have h := map_pResidual_le 2 f
      rw [(pResidual_eq_top_iff 2 Plane).mpr plane_twoPerfect] at h
      rintro x ⟨a,rfl⟩
      exact ⟨f a,h ⟨a,trivial,rfl⟩,rfl⟩
    · let f : Plane →* standardCentralizer := rightHom.codRestrict _ rightHom_mem
      have h := map_pResidual_le 2 f
      rw [(pResidual_eq_top_iff 2 Plane).mpr plane_twoPerfect] at h
      rintro x ⟨a,rfl⟩
      exact ⟨f a,h ⟨a,trivial,rfl⟩,rfl⟩

theorem left_le_centralizer_right : leftFactor ≤ Subgroup.centralizer (rightFactor : Set (Carrier 4)) := by
  rintro x ⟨a,rfl⟩ y ⟨b,rfl⟩
  exact (factors_commute a b).symm.eq

theorem left_normal_in_join : (leftFactor.subgroupOf factorJoin).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
  exact sup_le leftFactor.le_normalizer
    ((le_centralizer_iff.mp left_le_centralizer_right).trans (centralizer_le_normalizer _))

theorem right_normal_in_join : (rightFactor.subgroupOf factorJoin).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
  exact sup_le (left_le_centralizer_right.trans (centralizer_le_normalizer _))
    rightFactor.le_normalizer

theorem involution_mem_left : standardInvolution ∈ leftFactor := by
  have h := congrArg Subtype.val quaternionPair_sign_left
  rw [← pairHom_quaternion, pairHom_mul] at h
  have ho : quaternionPlane 1 = 1 := map_one _
  rw [ho,map_one,mul_one] at h
  exact ⟨quaternionPlane (.a 2),h⟩

theorem involution_mem_right : standardInvolution ∈ rightFactor := by
  refine ⟨quaternionPlane (.a 2),?_⟩
  apply Subtype.ext
  change ProjGenLinGroup.mk (OddFundamental.right conjugation star_involutive (m:=2) (n:=2)
    (quaternionPlane (.a 2))).val = ProjGenLinGroup.mk standardInvolutionSU.val
  apply ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨-1,Units.ext ?_⟩
  change OddFundamental.blockMatrix (1 : Mat₂) (quaternionMatrix (.a 2)) *
    Matrix.scalar (Fin 4) (-1 : FiniteField.Nine) = standardInvolutionMatrix
  rw [block_eq]
  decide

theorem factors_intersection : leftFactor ⊓ rightFactor = zpowers standardInvolution := by
  let Z := (center leftFactor).map leftFactor.subtype
  have hz : zpowers standardInvolution ≤ leftFactor ⊓ rightFactor :=
    zpowers_le.mpr ⟨involution_mem_left,involution_mem_right⟩
  have hi : leftFactor ⊓ rightFactor ≤ Z := by
    intro x hx
    refine ⟨⟨x,hx.1⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    apply Subtype.ext
    exact (left_le_centralizer_right y.property x hx.2).symm
  have hc : Nat.card Z=2 := by
    rw [card_map_of_injective leftFactor.subtype_injective]
    exact (Nat.card_congr (centerCongr leftFactorEquiv).toEquiv).trans
      GLS3.Chapter5.SchurPresentation.sl23_center_card
  have he : zpowers standardInvolution = Z := eq_of_le_of_card_ge (hz.trans hi) (by
    rw [hc,Nat.card_zpowers,standardInvolution_orderOf])
  exact le_antisymm (hi.trans he.ge) hz



noncomputable def nativeFactorData : Theory.GroupTheory.Recognition.UnitaryFourThree.Factors standardInvolution where
  left := leftFactor
  right := rightFactor
  span := residual_eq_factorJoin.symm
  normal_left := by rw [residual_eq_factorJoin]; exact left_normal_in_join
  normal_right := by rw [residual_eq_factorJoin]; exact right_normal_in_join
  left_model := ⟨leftFactorEquiv⟩
  right_model := ⟨rightFactorEquiv⟩
  intersection := factors_intersection

theorem native_residual_card : Nat.card (Theory.GroupTheory.Recognition.UnitaryFourThree.residual standardInvolution)=288 :=
  nativeFactorData.residual_card standardInvolution_orderOf

def nativeCore : Subgroup (Carrier 4) := quaternionCore.map standardCentralizer.subtype

theorem standardCentralizer_core_eq : standardCentralizer.pCoreIn 2 = nativeCore := by
  rw [pCoreIn,← quaternionCore_eq_pCore]; rfl

theorem standardCentralizer_normalizes_nativeCore :
    standardCentralizer ≤ normalizer (nativeCore : Set (Carrier 4)) := by
  rw [← standardCentralizer_core_eq]
  exact standardCentralizer.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image standardCentralizer (pCore 2 standardCentralizer))

theorem native_core_eq : Theory.GroupTheory.Recognition.UnitaryFourThree.core standardInvolution=nativeCore := by
  change (Theory.GroupTheory.Recognition.UnitaryFourThree.residual standardInvolution).pCoreIn 2=nativeCore
  rw [residual_eq_factorJoin]
  apply le_antisymm
  · rw [← standardCentralizer_core_eq]
    exact pCoreIn_mono_of_normalizes factorJoin_le
      ((normal_subgroupOf_iff_le_normalizer factorJoin_le).mp factorJoin_normal)
  · exact le_pCoreIn_of_normalizes (quaternionCore_isPGroup.map standardCentralizer.subtype)
      quaternionCore_le_factorJoin (factorJoin_le.trans standardCentralizer_normalizes_nativeCore)

theorem native_generalizedFitting :
    (Theory.GroupTheory.generalizedFitting standardCentralizer).map standardCentralizer.subtype =
      Theory.GroupTheory.Recognition.UnitaryFourThree.core standardInvolution := by
  rw [native_core_eq,← standardCentralizer_core_eq]
  exact congrArg (fun H : Subgroup standardCentralizer => H.map standardCentralizer.subtype)
    (Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
      standardCentralizer_twoCore_centralizer_le)
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
