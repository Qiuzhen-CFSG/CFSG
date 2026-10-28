module

public import Theory.Representation.InvertedFiveTensor.Scalars
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Tensor coordinates for an inverted order-five action

Over the four-element field recovered from r+r⁻¹, a dihedral module is the
tensor product of the concrete natural plane and its inverter-fixed space.
The pair map is (a,b) ↦ a+r(b); its inverse has second coordinate
ω⁻¹(v+s(v)). Both maps and their equivariance are proved explicitly.

Source: Aschbacher–Smith, Proposition 8.2.8(5), printed pp.718–719,
the two dihedral rows. The scalar relation here is constructed from binary
fixed-point-freeness by `omega_smul`, and the literal B/U is marked
in the Chapter 8 application. No tensor-recognition premise is assumed.
-/

public section
open scoped TensorProduct

namespace InvertedFiveTensor
variable {V : Type*} [AddCommGroup V] [Module F V]
variable (σ : Representation F D V)
variable (hq : ∀ v, omega • v = σ rot v + (σ rot ^ 4) v)

private theorem double (v : V) : v + v = 0 := by
  simpa only [show (1 : F) + 1 = 0 by decide +kernel, zero_smul, one_smul] using
    (add_smul (1 : F) 1 v).symm

section Fixed

@[expose] def fixedSpace : Submodule F V := (σ invt).fixedSubmodule

theorem mem_fixedSpace (v : V) : v ∈ fixedSpace σ ↔ σ invt v = v := Iff.rfl

private theorem invt_apply (v : V) : σ invt (σ invt v) = v := by
  change (σ invt * σ invt) v = v
  rw [← map_mul, invt_square, map_one, Module.End.one_apply]

private theorem invt_rot_apply (v : V) : σ invt (σ rot v) = (σ rot ^ 4) (σ invt v) := by
  change (σ invt * σ rot) v = (σ rot ^ 4 * σ invt) v
  rw [← map_mul, ← map_pow, ← map_mul, invt_rot]

include hq in
private theorem rot_four_apply (v : V) : (σ rot ^ 4) v = omega • v + σ rot v := by
  rw [hq]
  have hh := double (σ rot v)
  symm
  calc
    _ = (σ rot v + σ rot v) + (σ rot ^ 4) v := by abel
    _ = (σ rot ^ 4) v := by rw [hh, zero_add]

def second (v : V) : fixedSpace σ :=
  ⟨omega⁻¹ • (v + σ invt v), by
    change σ invt (omega⁻¹ • (v + σ invt v)) = _
    rw [map_smul, map_add]
    rw [invt_apply, add_comm]⟩

private theorem second_scalar (v : V) : omega • (second σ v : V) = v + σ invt v := by
  change omega • (omega⁻¹ • (v + σ invt v)) = _
  rw [smul_smul, mul_inv_cancel₀ omega_ne_zero, one_smul]

def first (v : V) : fixedSpace σ :=
  ⟨v + σ rot (second σ v), by
    change σ invt (v + σ rot (second σ v)) = _
    rw [map_add, invt_rot_apply, (mem_fixedSpace σ _).mp (second σ v).property,
      rot_four_apply σ hq, second_scalar]
    have hh := double (σ invt v)
    calc
      _ = v + (σ invt v + σ invt v) + σ rot (second σ v) := by abel
      _ = _ := by rw [hh, add_zero]⟩

def pairEquiv : (fixedSpace σ × fixedSpace σ) ≃ₗ[F] V where
  toFun p := p.1.val + σ rot p.2.val
  invFun v := (first σ hq v, second σ v)
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]; abel
  map_smul' a x := by
    change a • x.1.val + σ rot (a • x.2.val) = _
    rw [map_smul, smul_add]
    rfl
  right_inv v := by
    change (v + σ rot (second σ v)) + σ rot (second σ v) = v
    rw [add_assoc, double, add_zero]
  left_inv p := by
    have hs : (second σ (p.1.val + σ rot p.2.val) : V) = p.2.val := by
      change omega⁻¹ • ((p.1.val + σ rot p.2.val) + σ invt (p.1.val + σ rot p.2.val)) = p.2.val
      rw [map_add, (mem_fixedSpace σ _).mp p.1.property, invt_rot_apply,
        (mem_fixedSpace σ _).mp p.2.property, rot_four_apply σ hq]
      have he : (p.1.val + σ rot p.2.val) + (p.1.val + (omega • p.2.val + σ rot p.2.val)) =
          omega • p.2.val := by
        calc
          _ = (p.1.val + p.1.val) + (σ rot p.2.val + σ rot p.2.val) + omega • p.2.val := by abel
          _ = _ := by rw [double, double, zero_add, zero_add]
      rw [he, smul_smul, inv_mul_cancel₀ omega_ne_zero, one_smul]
    apply Prod.ext <;> apply Subtype.ext
    · change (p.1.val + σ rot p.2.val) + σ rot (second σ (p.1.val + σ rot p.2.val)) = p.1.val
      rw [hs, add_assoc, double, add_zero]
    · exact hs

end Fixed

/-- The companion matrix of a primitive fifth root over F₄. -/
def rotation : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, omega], by decide +kernel⟩

/-- The inverter fixing the first coordinate line. -/
def reflection : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, omega; 0, 1], by decide +kernel⟩

def naturalElement : D → Matrix.SpecialLinearGroup (Fin 2) F
  | .r i => rotation ^ i.val
  | .sr i => reflection * rotation ^ i.val

def naturalHom : D →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun := naturalElement
  map_one' := by decide +kernel
  map_mul' := by
    exact (by decide +kernel : ∀ g h : D, naturalElement (g * h) = naturalElement g * naturalElement h)

def natural : Representation F D (Fin 2 → F) :=
  (Representation.specialLinearNatural 2).comp naturalHom

theorem natural_rot (v : Fin 2 → F) : natural rot v = ![v 1, v 0 + omega * v 1] := by
  have he : naturalHom rot = rotation := by decide +kernel
  change Representation.specialLinearNatural 2 (naturalHom rot) v = _
  rw [he]
  change rotation.val.mulVec v = _
  funext i
  fin_cases i <;> simp [rotation,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem natural_invt (v : Fin 2 → F) : natural invt v = ![v 0 + omega * v 1, v 1] := by
  have he : naturalHom invt = reflection := by decide +kernel
  change Representation.specialLinearNatural 2 (naturalHom invt) v = _
  rw [he]
  change reflection.val.mulVec v = _
  funext i
  fin_cases i <;> simp [reflection,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]


private noncomputable def tensorCoordinates :
    (Fin 2 → F) ⊗[F] fixedSpace σ ≃ₗ[F] (fixedSpace σ × fixedSpace σ) :=
  (TensorProduct.congr (LinearEquiv.finTwoArrow F F) (LinearEquiv.refl F _)).trans
    ((TensorProduct.prodLeft F F F F (fixedSpace σ)).trans
      ((TensorProduct.lid F _).prodCongr (TensorProduct.lid F _)))

private theorem tensorCoordinates_tmul (n : Fin 2 → F) (b : fixedSpace σ) :
    tensorCoordinates σ (n ⊗ₜ[F] b) = (n 0 • b, n 1 • b) := by
  simp [tensorCoordinates]

/-- The tensor equivalence obtained from the actual inverter-fixed space. -/
noncomputable def tensorEquiv : (Fin 2 → F) ⊗[F] fixedSpace σ ≃ₗ[F] V :=
  (tensorCoordinates σ).trans (pairEquiv σ hq)

theorem tensorEquiv_tmul (n : Fin 2 → F) (b : fixedSpace σ) :
    tensorEquiv σ hq (n ⊗ₜ[F] b) = n 0 • b.val + n 1 • σ rot b.val := by
  change pairEquiv σ hq (tensorCoordinates σ _) = _
  rw [tensorCoordinates_tmul]
  change n 0 • b.val + σ rot (n 1 • b.val) = _
  rw [map_smul]

include hq in
private theorem rot_squared (v : V) : σ rot (σ rot v) = v + omega • σ rot v := by
  have h5 : σ rot ^ 5 = 1 := by rw [← map_pow, rot_fifth, map_one]
  have hp : (σ rot ^ 4) (σ rot v) = v := by
    change (σ rot ^ 4 * σ rot) v = v
    rw [← pow_succ, h5, Module.End.one_apply]
  have h := hq (σ rot v)
  rw [hp] at h
  rw [h]
  symm
  have hh := double v
  calc
    _ = (v + v) + σ rot (σ rot v) := by abel
    _ = _ := by rw [hh, zero_add]

include hq in
private theorem tensorEquiv_rot (n : Fin 2 → F) (b : fixedSpace σ) :
    tensorEquiv σ hq (natural rot n ⊗ₜ[F] b) = σ rot (tensorEquiv σ hq (n ⊗ₜ[F] b)) := by
  rw [tensorEquiv_tmul, tensorEquiv_tmul, natural_rot]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [map_add, map_smul, map_smul, rot_squared σ hq, add_smul, mul_smul, smul_add]
  rw [smul_comm (n 1) omega]
  abel

include hq in
private theorem tensorEquiv_invt (n : Fin 2 → F) (b : fixedSpace σ) :
    tensorEquiv σ hq (natural invt n ⊗ₜ[F] b) = σ invt (tensorEquiv σ hq (n ⊗ₜ[F] b)) := by
  rw [tensorEquiv_tmul, tensorEquiv_tmul, natural_invt]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [map_add, map_smul, map_smul, (mem_fixedSpace σ _).mp b.property,
    invt_rot_apply, (mem_fixedSpace σ _).mp b.property, rot_four_apply σ hq,
    add_smul, mul_smul, smul_add, smul_comm (n 1) omega]
  abel

/-- Equivariance for every element of the genuine dihedral group. -/
theorem tensorEquiv_dihedral (g : D) (n : Fin 2 → F) (b : fixedSpace σ) :
    tensorEquiv σ hq (natural g n ⊗ₜ[F] b) = σ g (tensorEquiv σ hq (n ⊗ₜ[F] b)) := by
  have hm (g h : D)
      (hg : ∀ n, tensorEquiv σ hq (natural g n ⊗ₜ[F] b) = σ g (tensorEquiv σ hq (n ⊗ₜ[F] b)))
      (hh : ∀ n, tensorEquiv σ hq (natural h n ⊗ₜ[F] b) = σ h (tensorEquiv σ hq (n ⊗ₜ[F] b))) (n) :
      tensorEquiv σ hq (natural (g*h) n ⊗ₜ[F] b) = σ (g*h) (tensorEquiv σ hq (n ⊗ₜ[F] b)) := by
    simp only [map_mul, Module.End.mul_apply, hg, hh]
  have hp (j : ℕ) (n) : tensorEquiv σ hq (natural (rot^j) n ⊗ₜ[F] b) =
      σ (rot^j) (tensorEquiv σ hq (n ⊗ₜ[F] b)) := by
    induction j generalizing n with
    | zero => simp only [pow_zero, map_one, Module.End.one_apply]
    | succ j ih => exact hm _ _ ih (fun n => tensorEquiv_rot σ hq n b) n
  cases g with
  | r j =>
    have hj : (DihedralGroup.r j : D) = rot ^ j.val := by simp
    rw [hj]
    exact hp _ n
  | sr j =>
    have hj : (DihedralGroup.sr j : D) = invt * rot ^ j.val := by simp
    rw [hj]
    exact hm _ _ (fun n => tensorEquiv_invt σ hq n b) (hp _) n

end InvertedFiveTensor
