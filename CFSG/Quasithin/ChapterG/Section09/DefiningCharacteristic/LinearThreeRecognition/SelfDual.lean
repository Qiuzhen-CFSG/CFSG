module
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.FieldDescent
public import Mathlib.RepresentationTheory.Character
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.RingTheory.AlgebraTower

/-!
# Non-self-duality of the half-field SL₃ tensor

A determinant-one companion matrix has trace zero on the twisted tensor,
while its inverse has trace equal to an arbitrary quadratic norm. Norm
surjectivity and the nonzero field trace produce unequal binary traces.
The scalar-restriction trace formula and the actual descended action transfer
this obstruction to the original representation, including its dual.

Source: Aschbacher--Smith G.9.3(17) and the self-dual row sieve in G.11.7,
printed pp.354,366--367.
-/

@[expose] public noncomputable section
open Matrix Representation
open scoped MatrixGroups TensorProduct
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

private theorem trace_restrict {k K V : Type*} [Field k] [Field K]
    [Algebra k K] [FiniteDimensional k K] [AddCommGroup V] [Module K V]
    [Module k V] [IsScalarTower k K V] [FiniteDimensional K V]
    (f : Module.End K V) :
    LinearMap.trace k V (f.restrictScalars k) =
      Algebra.trace k K (LinearMap.trace K V f) := by
  classical
  let b := Module.Free.chooseBasis k K
  let c := Module.Free.chooseBasis K V
  rw [LinearMap.trace_eq_matrix_trace k (b.smulTower c),
    LinearMap.trace_eq_matrix_trace K c]
  simp only [Matrix.trace, map_sum]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, Module.Basis.smulTower_apply,
    Module.Basis.smulTower_repr, LinearMap.restrictScalars_apply, map_smul,
    Finsupp.smul_apply, smul_eq_mul]
  rw [←Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Algebra.trace_eq_matrix_trace b]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_apply]
  congr 1
  ext i
  rw [mul_comm]
  simp only [LinearMap.toMatrix_apply,Algebra.coe_lmul_eq_mul,LinearMap.mul_apply']

variable {K : Type*} [Field K] [CharP K 2]
private def separator (a : K) : SL(3,K) :=
  ⟨!![0,0,1; 1,0,a; 0,1,0],by simp [Matrix.det_fin_three]⟩
private def separatorInv (a : K) : SL(3,K) :=
  ⟨!![a,1,0; 0,0,1; 1,0,0],by simp [Matrix.det_fin_three]⟩
private theorem separator_inv (a : K) : (separator a)⁻¹ = separatorInv a := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (separator a).val * (separatorInv a).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [separator,separatorInv,Matrix.mul_apply,Fin.sum_univ_three,CharTwo.add_self_eq_zero]

omit [CharP K 2] in
private theorem natural_character (g : SL(3,K)) :
    (specialLinearNatural (k := K) 3).character g = Matrix.trace g.val := by
  rw [Representation.character, LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin 3))]
  congr 1
  ext i j
  simp [specialLinearNatural_apply]

open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
omit [CharP K 2] in
private theorem tensor_character (σ : K ≃+* K) (g : SL(3,K)) :
    (twistedTensor K σ).character g = Matrix.trace g.val * σ (Matrix.trace g.val) := by
  rw [twistedTensor,Representation.char_tensor]
  change (specialLinearNatural 3).character g *
    (specialLinearNatural 3).character (Matrix.SpecialLinearGroup.map σ.toRingHom g) = _
  rw [natural_character,natural_character]
  congr 1
  exact (map_sum σ _ _).symm

omit [CharP K 2] in
private theorem separator_character (σ : K ≃+* K) (a : K) :
    (twistedTensor K σ).character (separator a) = 0 := by
  rw [tensor_character]
  simp [separator,Matrix.trace,Fin.sum_univ_three]
private theorem separator_inv_character (σ : K ≃+* K) (a : K) :
    (twistedTensor K σ).character (separator a)⁻¹ = a * σ a := by
  rw [separator_inv,tensor_character]
  simp [separatorInv,Matrix.trace,Fin.sum_univ_three]

omit [CharP K 2] in
private theorem norm_formula [Finite K] (S : Subfield K)
    (hdegree : Module.finrank S K = 2) (σ : K ≃+* K)
    (hσ : ∀ a, σ a = a ^ Nat.card S) (a : K) :
    algebraMap S K (Algebra.norm S a) = a * σ a := by
  rw [FiniteField.algebraMap_norm_eq_prod_pow, hdegree, hσ]
  simp [Finset.prod_range_succ]

variable [Finite K]
local instance (S : Subfield K) : Algebra (ZMod 2) S := ZMod.algebra S 2
private theorem exists_nonzero_trace (S : Subfield K) :
    ∃ b : S, Algebra.trace (ZMod 2) S b ≠ 0 := by
  by_contra! hh
  have hnd := traceForm_nondegenerate (ZMod 2) S
  exact one_ne_zero (hnd.1 1 (by simpa only [Algebra.traceForm_apply,one_mul] using hh))

private theorem restriction_not_selfDual
    (S : Subfield K) (σ : K ≃+* K) (hdegree : Module.finrank S K = 2)
    (hσ : ∀ a, σ a = a ^ Nat.card S)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [Module S V] [IsScalarTower (ZMod 2) S V]
    (τ : Representation S SL(3,K) V)
    (hext : Nonempty ((extendScalars K τ).Equiv (twistedTensor K σ)) ∨
      Nonempty ((extendScalars K τ).Equiv (twistedTensor K σ).dual)) :
    ¬ Nonempty ((restrictScalars (k := ZMod 2) τ).Equiv
      (restrictScalars (k := ZMod 2) τ).dual) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : FiniteDimensional S V := Module.Finite.of_finite
  obtain ⟨b,hb⟩ := exists_nonzero_trace S
  obtain ⟨a,ha⟩ := FiniteField.norm_surjective S K b
  have hnorm : algebraMap S K b = a * σ a := ha ▸ norm_formula S hdegree σ hσ a
  have hchar (g : SL(3,K)) :
      (restrictScalars (k := ZMod 2) τ).character g = Algebra.trace (ZMod 2) S (τ.character g) :=
    trace_restrict (τ g)
  have hbase (g : SL(3,K)) :
      (extendScalars K τ).character g = algebraMap S K (τ.character g) :=
    LinearMap.trace_baseChange _ _
  rintro ⟨e⟩
  have hself := congrFun (Representation.char_iso e) (separator a)
  rw [Representation.char_dual,hchar,hchar] at hself
  rcases hext with h | h
  · obtain ⟨c⟩ := h
    have hzero : τ.character (separator a) = 0 := by
      apply (algebraMap S K).injective
      rw [map_zero,←hbase,congrFun (Representation.char_iso c),separator_character]
    have hone : τ.character (separator a)⁻¹ = b := by
      apply (algebraMap S K).injective
      rw [←hbase,congrFun (Representation.char_iso c),separator_inv_character,hnorm]
    rw [hzero,hone,map_zero] at hself
    exact hb hself.symm
  · obtain ⟨c⟩ := h
    have hzero : τ.character (separator a)⁻¹ = 0 := by
      apply (algebraMap S K).injective
      rw [map_zero,←hbase,congrFun (Representation.char_iso c),Representation.char_dual,
        inv_inv,separator_character]
    have hone : τ.character (separator a) = b := by
      apply (algebraMap S K).injective
      rw [←hbase,congrFun (Representation.char_iso c),Representation.char_dual,
        separator_inv_character,hnorm]
    rw [hzero,hone,map_zero] at hself
    exact hb hself

open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

/-- The actual half-field SL₃ tensor, including either duality choice, is not
binary self-dual. The original absolute-model witness is retained. -/
theorem not_selfDual_absolute_twisted
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(3,K) V) [IsIrreducible ρ]
    (r : ℕ) (hr : 0 < r) (hcard : Nat.card K = 2^(2*r))
    (hschur : schurDegree ρ = r) (h : HasAbsoluteTwistedModel ρ r) :
    ¬ Nonempty (ρ.Equiv ρ.dual) := by
  obtain ⟨σ,hσ,_,_,S,_,hS,m,τ,hrho,hext,_⟩ :=
    descend_absolute_twisted ρ r hr hcard hschur h
  let : Module S V := m
  let : IsScalarTower (ZMod 2) S V :=
    IsScalarTower.of_algebraMap_smul (fun a w => by
      fin_cases a
      · change algebraMap (ZMod 2) S (0 : ZMod 2) • w = (0 : ZMod 2) • w
        simp only [map_zero,zero_smul]
      · change algebraMap (ZMod 2) S (1 : ZMod 2) • w = (1 : ZMod 2) • w
        simp only [map_one,one_smul])
  have hdegree : Module.finrank S K = 2 := by
    have he := Module.natCard_eq_pow_finrank (K := S) (V := K)
    rw [hcard,hS,←Nat.pow_mul] at he
    have hpow := Nat.pow_right_injective (by decide : 1<2) he
    nlinarith
  rw [←hrho]
  exact restriction_not_selfDual S σ hdegree (by intro a; rw [hS]; exact hσ a) τ hext
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
