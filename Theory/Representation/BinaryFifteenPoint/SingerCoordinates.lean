module
public import Theory.Representation.BinaryFifteenPoint.InvariantLattice
public import Theory.Representation.BinaryEndpointInduction.ParabolicSeedMarking

/-!
# The marked endpoint Singer element on the fifteen right cosets

The literal SL₄(2) element has packed rows [1,4,8,6]. Its lower-right
block has characteristic polynomial X³+X+1. Exact parabolic corrections
certify the right-coset action. Converted left actions use its inverse.
-/
@[expose] public section
namespace BinaryFifteenPoint
open Matrix Thompson.BinaryMatrix BinaryEndpointInduction
open scoped MatrixGroups

/-- The exact endpoint Singer actor diag(1,S), with S rows 010,001,110. -/
def singerActor : SL(4,ZMod 2) := ⟨decode 4 #[1,4,8,6],by decide +kernel⟩

/-- The actor belongs to the literal row-e0 stabilizer. -/
theorem singerActor_mem_endpoint : singerActor ∈ endpointParabolic := by
  change ∀ j : Fin 4, singerActor.val 0 j=if j=0 then 1 else 0
  decide +kernel

/-- The same marked actor has order seven. -/
theorem singerActor_order : orderOf singerActor=7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

/-- Transition indices for right multiplication by the marked Singer actor. -/
def singerTransitionData : Array ℕ := #[0, 3, 4, 5, 9, 2, 8, 12, 11, 10, 1, 14, 6, 7, 13]

def singerTransitionIndex (i : Fin 15) : Fin 15 :=
  ⟨singerTransitionData[i.val]! % 15, Nat.mod_lt _ (by decide)⟩

def singerCorrectionRows : Array (Array ℕ) := #[#[1, 4, 8, 6], #[1, 2, 9, 4], #[1, 2, 11, 4], #[1, 12, 2, 8], #[1, 5, 8, 6], #[1, 8, 2, 4], #[1, 3, 4, 8], #[1, 5, 6, 13], #[1, 5, 6, 11], #[1, 7, 3, 8], #[1, 7, 3, 8], #[1, 2, 6, 8], #[1, 14, 2, 8], #[1, 7, 4, 8], #[1, 13, 11, 3]]

theorem singerCorrection_det : ∀ i : Fin 15,
    (decode 4 singerCorrectionRows[i.val]!).det=1 := by decide +kernel

/-- Actual left corrections, in the original ordering of right cosets. -/
def singerCorrection (i : Fin 15) : SL(4,ZMod 2) :=
  ⟨decode 4 singerCorrectionRows[i.val]!,singerCorrection_det i⟩

/-- The checked exact actor equation rᵢs=pᵢrⱼ. -/
theorem singer_coset_transition : ∀ i : Fin 15,
    cosetRepresentative i*singerActor=
      singerCorrection i*cosetRepresentative (singerTransitionIndex i) := by decide +kernel

/-- Every correction fixes the same endpoint seed. -/
theorem singerCorrection_mem_endpoint : ∀ i : Fin 15,
    singerCorrection i ∈ endpointParabolic := by
  change ∀ i : Fin 15, ∀ j : Fin 4, (singerCorrection i).val 0 j=if j=0 then 1 else 0
  decide +kernel

def singerRows : Array ℕ := #[1, 8, 16, 32, 512, 4, 256, 4096, 2048, 1024, 2, 16384, 64, 128, 8192]

/-- Right-row permutation action of the actual marked Singer actor. -/
def singerMatrix : Matrix (Fin 15) (Fin 15) (ZMod 2) := decode 15 singerRows

private theorem singer_entry_bits : ∀ i j : Fin 15,
    singerRows[i.val]!.testBit j.val=decide (singerTransitionIndex i=j) := by decide +kernel

/-- Exact matrix marking by the checked right-coset transitions. -/
theorem singerMatrix_entry (i j : Fin 15) :
    singerMatrix i j=if singerTransitionIndex i=j then 1 else 0 := by
  change (if singerRows[i.val]!.testBit j.val then (1 : ZMod 2) else 0)=_
  rw [singer_entry_bits]
  simp

/-- Basis vectors follow the literal right-coset permutation. -/
theorem singerMatrix_single (i : Fin 15) :
    Pi.single i (1 : ZMod 2) ᵥ* singerMatrix=Pi.single (singerTransitionIndex i) 1 := by
  ext j
  rw [Matrix.single_one_vecMul]
  change singerMatrix i j=_
  rw [singerMatrix_entry]
  simp [Pi.single_apply,eq_comm]

def singerAdaptedRows : Array ℕ := #[1, 10338, 24624, 40, 104, 112, 16, 3470, 7288, 17978, 7832, 20532, 74, 22630, 12384]

def singerAdapted : Matrix (Fin 15) (Fin 15) (ZMod 2) := decode 15 singerAdaptedRows

private theorem singer_intertwine_check : ∀ i : Fin 15,
    rowProduct changeRows[i.val]! singerRows 15=
      rowProduct singerAdaptedRows[i.val]! changeRows 15 := by decide +kernel

/-- The Singer action uses the same frozen primary coordinate change. -/
theorem singer_intertwine : changeMatrix*singerMatrix=singerAdapted*changeMatrix := by
  ext i j
  change (∑ k : Fin 15, bit changeRows[i.val]! k.val*bit singerRows[k.val]! j.val)=
    ∑ k : Fin 15, bit singerAdaptedRows[i.val]! k.val*bit changeRows[k.val]! j.val
  rw [Fin.sum_univ_eq_sum_range (fun k => bit changeRows[i.val]! k*bit singerRows[k]! j.val),
    Fin.sum_univ_eq_sum_range (fun k => bit singerAdaptedRows[i.val]! k*bit changeRows[k]! j.val),
    ←bit_rowProduct,←bit_rowProduct,singer_intertwine_check]

/-- Any map with the original endpoint-fixed seed coordinates intertwines
the marked Singer right action with the inverse of the original left actor. -/
theorem singer_intertwining_of_seed
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) SL(4,ZMod 2) W) (w : W)
    (hfix : ∀ p : endpointParabolic, τ p.val w=w)
    (F : (Fin 15 → ZMod 2) →ₗ[ZMod 2] W)
    (hF : ∀ i : Fin 15, F (Pi.single i 1)=τ (cosetRepresentative i)⁻¹ w)
    (x : Fin 15 → ZMod 2) : F (x ᵥ* singerMatrix)=τ singerActor⁻¹ (F x) := by
  suffices he : F.comp singerMatrix.vecMulLinear=(τ singerActor⁻¹).comp F by
    exact LinearMap.congr_fun he x
  apply (Pi.basisFun (ZMod 2) (Fin 15)).ext
  intro i
  simp only [Pi.basisFun_apply,LinearMap.comp_apply,Matrix.vecMulLinear_apply,
    singerMatrix_single,hF]
  have hc := hfix (⟨(singerCorrection i)⁻¹,
    endpointParabolic.inv_mem (singerCorrection_mem_endpoint i)⟩ : endpointParabolic)
  change τ (singerCorrection i)⁻¹ w=w at hc
  calc
    τ (cosetRepresentative (singerTransitionIndex i))⁻¹ w =
      τ (cosetRepresentative (singerTransitionIndex i))⁻¹ (τ (singerCorrection i)⁻¹ w) :=
        congrArg (τ (cosetRepresentative (singerTransitionIndex i))⁻¹) hc.symm
    _ = τ singerActor⁻¹ (τ (cosetRepresentative i)⁻¹ w) := by
      rw [←Module.End.mul_apply,←τ.map_mul,←Module.End.mul_apply,←τ.map_mul]
      have he := congrArg (fun g : SL(4,ZMod 2) => g⁻¹) (singer_coset_transition i)
      simp only [_root_.mul_inv_rev] at he
      exact congrArg (fun g => τ g w) he.symm

end BinaryFifteenPoint
