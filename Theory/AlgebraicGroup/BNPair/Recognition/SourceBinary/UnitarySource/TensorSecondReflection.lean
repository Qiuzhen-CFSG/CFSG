module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorRoots

/-!
# The second reflection is linear over the same source coefficient field

Explicit full-torus parameters act by each square scalar on both A and C
while fixing B. Their actual source images lie in the smaller panel kernel
and centralize the entire smaller actor. Consequently its reflection sends
A(a) to C(ca) for one nonzero c. Conjugating the commuting A(1), C(1) pair
and using the trace commutator forces c to lie in the fixed field.

Multiplication of all three Hermitian summands by this fixed-field unit
preserves the tensor action. TensorReflectionApplication uses that actual
rescaling to prove tA(a)t=C(a) and tC(a)t=A(a) on the original quotient,
including q=2. No field-identification or reflection-coefficient premise
is introduced there. The smaller rank-one Bruhat and labelled Cartan
reflection equations remain separate obligations toward FourData.

Source: Fong--Seitz II (8B), pp.201--202, the common Cartan-scalar actions
on the same core and the coefficient comparison (8.7)--(8.9).
-/

@[expose] public noncomputable section
open Subgroup Representation Matrix
open scoped MatrixGroups IsMulCommutative commutatorElement
open Theory.PSL2.SemilinearCoverage
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource
namespace FourTensor
variable (E : Type*) [Field E] [Finite E] [CharP E 2]
  (σ : E ≃+* E) (hσ : Function.Involutive σ)
local notation "Kf" => Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ

def normUnit (a : Eˣ) : Kfˣ := Units.mk0
  ⟨(a : E) * σ (a : E), by change σ ((a : E) * σ (a : E)) = _; rw [map_mul,hσ]; exact mul_comm _ _⟩
  (fun hz => mul_ne_zero a.ne_zero ((map_ne_zero σ).mpr a.ne_zero) (congrArg Subtype.val hz))

def normHalf (a : Eˣ) : Eˣ :=
  Units.map (Subfield.subtype Kf).toMonoidHom (FourCartan.squareRoot E σ (normUnit E σ hσ a))

private theorem normHalf_fixed (a : Eˣ) : σ (normHalf E σ hσ a : E) = normHalf E σ hσ a :=
  (FourCartan.squareRoot E σ (normUnit E σ hσ a) : Kf).property

private theorem normHalf_sq (a : Eˣ) : (normHalf E σ hσ a : E)^2 = (a : E)*σ (a : E) :=
  congrArg Subtype.val (FourCartan.squareRoot_square E σ (normUnit E σ hσ a))

/-- A full source-torus parameter acts by the same square scalar on A and C,
while fixing the smaller simple root B. -/
def commonScalarParameter (a : Eˣ) : FourWeyl.torusParameters E σ :=
  ⟨(normHalf E σ hσ a * a, normHalf E σ hσ a * a⁻¹),by
    change σ ((↑(normHalf E σ hσ a * a) : E) * (↑(normHalf E σ hσ a * a⁻¹) : E)) = _
    simp only [Units.val_mul,Units.val_inv_eq_inv_val]
    have hh : ((normHalf E σ hσ a : E)*(a : E))*((normHalf E σ hσ a : E)*(a : E)⁻¹) =
        (normHalf E σ hσ a : E)^2 := by field_simp
    rw [hh,map_pow,normHalf_fixed]⟩

theorem commonScalarParameter_weights (a : Eˣ) :
    let p := commonScalarParameter E σ hσ a
    (p.val.1 : E) / (p.val.2 : E) = (a : E)^2 ∧
    (p.val.1 : E) * σ (p.val.2 : E) = (a : E)^2 ∧
    (p.val.2 : E) * σ (p.val.2 : E) = 1 := by
  dsimp only [commonScalarParameter]
  simp only [Units.val_mul,Units.val_inv_eq_inv_val]
  have hn := (normHalf E σ hσ a).ne_zero
  have ha := a.ne_zero
  have hbar := (map_ne_zero σ).mpr ha
  have hsq := normHalf_sq E σ hσ a
  rw [map_mul,map_inv₀,normHalf_fixed]
  constructor
  · field_simp
  constructor
  · field_simp
    exact hsq
  · field_simp
    linear_combination hsq

/-- Rescaling all three Hermitian summands by one fixed-field unit. -/
def scale (c : Kfˣ) : Multiplicative (Core E σ hσ) ≃* Multiplicative (Core E σ hσ) where
  toFun p := .ofAdd ((c : Kf) • p.toAdd)
  invFun p := .ofAdd (((c⁻¹ : Kfˣ) : Kf) • p.toAdd)
  left_inv p := by simp only [toAdd_ofAdd,smul_smul,Units.inv_mul,one_smul,ofAdd_toAdd]
  right_inv p := by simp only [toAdd_ofAdd,smul_smul,Units.mul_inv,one_smul,ofAdd_toAdd]
  map_mul' p q := by simp only [toAdd_mul,smul_add,ofAdd_add]

omit [Finite E] [CharP E 2] in
theorem scale_off (c : Kfˣ) (a : E) :
    (c : Kf) • offDiagonal E σ hσ a = offDiagonal E σ hσ ((c.val : E)*a) := by
  have hc : σ (c.val : E) = c.val := c.val.property
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagonal,hc] <;> rfl

end FourTensor
variable {X E : Type*} [Group X] [Field E] [Finite E] [CharP E 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i j : Fin 2) (σ : E ≃+* E) (hσ : Function.Involutive σ)
variable
  (R : PositiveMaps (X ⧸ Q.D) (Multiplicative E) (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ)) (Multiplicative E) (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ)))
  (cartan : FourWeyl.torusParameters E σ →* X ⧸ Q.D)
  (hB : R.B.range = simpleRoot Q split j)
  (ht : cartan.range ≤ Q.tits.B ⊓ Q.tits.N)
  (hwB : ∀ (p : FourWeyl.torusParameters E σ) (b : (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ)), cartan p * R.B (.ofAdd b) * (cartan p)⁻¹ =
    R.B (.ofAdd (FourPositive.normParameter E σ hσ p.val.2 b)))

include R hB ht hwB in
/-- These actual Cartan elements lie in the smaller actor's centralizing kernel. -/
theorem commonScalar_mem_coreCartan (a : Eˣ) :
    cartan (FourTensor.commonScalarParameter E σ hσ a) ∈ coreCartan Q j := by
  let p := FourTensor.commonScalarParameter E σ hσ a
  change cartan p ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ ReeSource.embeddedPanelKernel Q j
  rw [←ReeSource.cartan_centralizer_simpleRoot Q split j]
  refine ⟨ht ⟨p,rfl⟩,mem_centralizer_iff.mpr ?_⟩
  intro y hy
  rw [←hB] at hy
  obtain ⟨b,rfl⟩ := hy
  have hc : FourPositive.normParameter E σ hσ p.val.2 b.toAdd = b.toAdd := by
    apply Subtype.ext
    change (p.val.2 : E)*σ (p.val.2 : E)*(b.toAdd : E) = (b.toAdd : E)
    rw [(FourTensor.commonScalarParameter_weights E σ hσ a).2.2,one_mul]
  have he := hwB p b.toAdd
  rw [hc] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

variable
  (hA : R.A.range = simpleRoot Q split i)
  (hC : R.C.range = rootAt Q split i (Q.simple j))
  (hAi : Function.Injective R.A)
  (hwA : ∀ (p : FourWeyl.torusParameters E σ) (a : E), cartan p * R.A (.ofAdd a) * (cartan p)⁻¹ =
    R.A (.ofAdd (((p.val.1 : E) / (p.val.2 : E))*a)))
  (hwC : ∀ (p : FourWeyl.torusParameters E σ) (c : E), cartan p * R.C (.ofAdd c) * (cartan p)⁻¹ =
    R.C (.ofAdd (((p.val.1 : E)*σ (p.val.2 : E))*c)))
  (t : RootReflection Q split j)

include R hB ht hwB hA hC hAi hwA hwC in
/-- Commutation with the actual full scalar kernel makes the second reflection's
A-to-C coordinate change multiplication by one nonzero field element. -/
theorem secondReflection_A_scalar : ∃ c : E, c ≠ 0 ∧ ∀ a : E,
    (t.val : X ⧸ Q.D)⁻¹ * R.A (.ofAdd a) * t.val = R.C (.ofAdd (c*a)) := by
  have htmem (a : E) : (t.val : X ⧸ Q.D)⁻¹ * R.A (.ofAdd a) * t.val ∈ R.C.range := by
    rw [hC,rootAt_eq Q split i (Q.simple j) t.val t.class_eq]
    change (t.val : X ⧸ Q.D) * ((t.val : X ⧸ Q.D)⁻¹*R.A (.ofAdd a)*t.val) *
      (t.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split i
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using (hA ▸ (show R.A (.ofAdd a) ∈ R.A.range from ⟨_,rfl⟩))
  obtain ⟨c,hc⟩ := htmem 1
  have hc0 : c.toAdd ≠ 0 := by
    intro hz
    have he : R.C c = 1 := by rw [show c = 1 from congrArg Multiplicative.ofAdd hz,map_one]
    have ha : R.A (.ofAdd (1 : E)) = 1 := by
      have hh := congrArg (fun x : X ⧸ Q.D => (t.val : X ⧸ Q.D)*x*(t.val : X ⧸ Q.D)⁻¹) (hc.symm.trans he)
      simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_one,mul_inv_cancel] using hh
    exact one_ne_zero (Multiplicative.ofAdd.injective (hAi (ha.trans (map_one R.A).symm)))
  refine ⟨c.toAdd,hc0,fun a => ?_⟩
  by_cases ha : a = 0
  · subst a
    simp only [mul_zero,ofAdd_zero,map_one,mul_one,inv_mul_cancel]
  obtain ⟨u,hu⟩ := (frobeniusEquiv E 2).surjective a
  have hu2 : u^2 = a := hu
  have hu0 : u ≠ 0 := by
    intro hz
    apply ha
    simpa only [hz,zero_pow (by decide : (2 : ℕ) ≠ 0)] using hu2.symm
  let p := FourTensor.commonScalarParameter E σ hσ (Units.mk0 u hu0)
  have hp := FourTensor.commonScalarParameter_weights E σ hσ (Units.mk0 u hu0)
  have hpA : (p.val.1 : E) / (p.val.2 : E) = u^2 := hp.1
  have hpC : (p.val.1 : E) * σ (p.val.2 : E) = u^2 := hp.2.1
  have hker := commonScalar_mem_coreCartan Q split j σ hσ R cartan hB ht hwB (Units.mk0 u hu0)
  have hcomm : Commute (cartan p) (t.val : X ⧸ Q.D) :=
    ((mem_centralizer_iff.mp (coreCartan_centralizes_coreActor Q split j hker))
      t.val ((show rankOne Q split j ≤ coreActor Q split j from le_sup_right) t.mem_rankOne)).symm
  have hroot : cartan p * R.A (.ofAdd (1 : E)) * (cartan p)⁻¹ = R.A (.ofAdd a) := by
    simpa only [hpA,hu2,mul_one] using hwA p 1
  calc
    _ = (t.val : X ⧸ Q.D)⁻¹ * (cartan p * R.A (.ofAdd 1) * (cartan p)⁻¹) * t.val := by rw [hroot]
    _ = cartan p * ((t.val : X ⧸ Q.D)⁻¹ * R.A (.ofAdd 1) * t.val) * (cartan p)⁻¹ := by
      calc
        _ = ((t.val : X ⧸ Q.D)⁻¹ * cartan p) * R.A (.ofAdd 1) * ((cartan p)⁻¹ * t.val) := by group
        _ = (cartan p * (t.val : X ⧸ Q.D)⁻¹) * R.A (.ofAdd 1) * ((t.val : X ⧸ Q.D) * (cartan p)⁻¹) := by
          rw [hcomm.symm.inv_left.eq,hcomm.inv_left.eq]
        _ = _ := by group
    _ = cartan p * R.C c * (cartan p)⁻¹ := by rw [←hc]
    _ = R.C (.ofAdd (c.toAdd*a)) := by
      change cartan p * R.C (.ofAdd c.toAdd) * (cartan p)⁻¹ = R.C (.ofAdd (c.toAdd*a))
      simpa only [hpC,hu2,mul_comm] using hwC p c.toAdd


include hB ht hwB hA hC hAi hwA hwC in
/-- The trace commutator forces that scalar into the same fixed field. -/
theorem secondReflection_AC_fixedScalar
    (rel : FourPositive.Relations E σ hσ R) (hDi : Function.Injective R.D)
    (ht2 : (t.val : X ⧸ Q.D) * t.val = 1) :
    ∃ c : (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ), c ≠ 0 ∧
      (∀ a : E, (t.val : X ⧸ Q.D)⁻¹ * R.A (.ofAdd a) * t.val = R.C (.ofAdd ((c : E)*a))) ∧
      (∀ a : E, (t.val : X ⧸ Q.D)⁻¹ * R.C (.ofAdd a) * t.val = R.A (.ofAdd ((c : E)⁻¹*a))) := by
  obtain ⟨c,hc0,hca⟩ := secondReflection_A_scalar Q split i j σ hσ R cartan hB ht hwB hA hC hAi hwA hwC t
  have htinv : (t.val : X ⧸ Q.D)⁻¹ = t.val := inv_eq_of_mul_eq_one_right ht2
  have hcb (a : E) : (t.val : X ⧸ Q.D)⁻¹ * R.C (.ofAdd a) * t.val = R.A (.ofAdd (c⁻¹*a)) := by
    have he := hca (c⁻¹*a)
    rw [←mul_assoc,mul_inv_cancel₀ hc0,one_mul] at he
    have hh := congrArg (fun y : X ⧸ Q.D => (t.val : X ⧸ Q.D)⁻¹*y*t.val) he
    rw [htinv] at hh ⊢
    have hinv : (t.val : X ⧸ Q.D) * ((t.val : X ⧸ Q.D)*R.A (.ofAdd (c⁻¹*a))*t.val) * t.val = R.A (.ofAdd (c⁻¹*a)) := by
      calc
        _ = ((t.val : X ⧸ Q.D)*t.val)*R.A (.ofAdd (c⁻¹*a))*((t.val : X ⧸ Q.D)*t.val) := by group
        _ = _ := by rw [ht2,one_mul,mul_one]
    exact hh.symm.trans hinv
  have htr : FourPositive.traceParameter E σ hσ 1 1 = 0 := by
    apply Subtype.ext
    change (1 : E)*σ 1+σ 1*1 = 0
    simp only [map_one,mul_one,CharTwo.add_self_eq_zero]
  have hcomm : Commute (R.A (.ofAdd (1 : E))) (R.C (.ofAdd (1 : E))) := by
    have hh := rel.CA 1 1
    simp only [htr,ofAdd_zero,map_one,mul_one] at hh
    exact hh.symm
  have hccomm := hcomm.map (MulAut.conj (t.val : X ⧸ Q.D)⁻¹).toMonoidHom
  simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] at hccomm
  rw [hca,hcb,mul_one,mul_one] at hccomm
  have htrace : FourPositive.traceParameter E σ hσ c⁻¹ c = 0 := by
    have hh := rel.CA c⁻¹ c
    rw [hccomm.eq] at hh
    have he : R.D (.ofAdd (FourPositive.traceParameter E σ hσ c⁻¹ c)) = 1 := by
      apply mul_right_cancel (b := R.C (.ofAdd c))
      apply mul_left_cancel (a := R.A (.ofAdd c⁻¹))
      simpa only [mul_assoc,mul_one,one_mul] using hh.symm
    exact Multiplicative.ofAdd.injective (hDi (he.trans (map_one R.D).symm))
  have hfixed : σ c = c := by
    have he := congrArg Subtype.val htrace
    change c⁻¹*σ c+σ (c⁻¹)*c = 0 at he
    rw [map_inv₀] at he
    have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc0
    field_simp at he
    apply CharTwo.sq_injective
    apply CharTwo.add_eq_zero.mp
    linear_combination he
  refine ⟨⟨c,hfixed⟩,fun hh => hc0 (congrArg Subtype.val hh),hca,hcb⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
