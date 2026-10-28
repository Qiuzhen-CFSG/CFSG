module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.Models
public import Theory.Representation.ExtendScalars
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Tactic.Ring

open Representation
open scoped MatrixGroups TensorProduct

/-!
# The central kernels of the twisted SL₃ tensor modules

A central matrix `a I` acts on `N ⊗ N^σ` by the scalar `a * σ(a)`.
Faithful scalar extension and an actual module equivalence identify this
kernel with the given covering map's kernel. Since `a³ = 1`, square
Frobenius kills the whole center, whereas fourth-power Frobenius kills
only the identity. Duality does not change the kernel.

Consequently the r=1 case of G.9.3(17) has component PSL₃(4), while r=2
has component SL₃(16). The statements below retain the actual field and
covering map, and take the scalar-extension equivalence as an explicit
input. Existence and exhaustiveness of the descended modules are separate
obligations; they are not supplied by this kernel calculation.

Source: Aschbacher--Smith, G.9.3(17), printed p.354; GLS III 2.8.6,
2.8.8 and 2.8.10(c).
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
variable {F : Type*} [Field F]

private theorem natural_scalar (g : SL(3,F)) (a : F)
    (hg : g.val = Matrix.scalar (Fin 3) a) :
    specialLinearNatural 3 g = a • (1 : Module.End F (Fin 3 → F)) := by
  apply LinearMap.ext
  intro v
  funext i
  simp [specialLinearNatural_apply, hg, Matrix.scalar, Matrix.mulVec, dotProduct, Matrix.diagonal]

theorem tensor_scalar (σ : F ≃+* F) (g : SL(3,F)) (a : F)
    (hg : g.val = Matrix.scalar (Fin 3) a) :
    twistedTensor F σ g = (a * σ a) • 1 := by
  have hmap : (Matrix.SpecialLinearGroup.map σ.toRingHom g).val =
      Matrix.scalar (Fin 3) (σ a) := by
    change g.val.map σ = _
    rw [hg]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar, Matrix.diagonal, hij]
  change TensorProduct.map (specialLinearNatural 3 g)
    (specialLinearNatural 3 (Matrix.SpecialLinearGroup.map σ.toRingHom g)) = _
  rw [natural_scalar g a hg, natural_scalar _ (σ a) hmap,
    TensorProduct.map_smul_left, TensorProduct.map_smul_right, TensorProduct.map_one,
    smul_smul]

theorem tensor_scalar_eq_one (σ : F ≃+* F) (g : SL(3,F)) (a : F)
    (hg : g.val = Matrix.scalar (Fin 3) a) :
    twistedTensor F σ g = 1 ↔ a * σ a = 1 := by
  rw [tensor_scalar σ g a hg]
  have hinj := FaithfulSMul.algebraMap_injective F
    (Module.End F ((Fin 3 → F) ⊗[F] (Fin 3 → F)))
  constructor
  · intro h
    apply hinj
    simpa [Algebra.algebraMap_eq_smul_one] using h
  · intro h
    rw [h, one_smul]

private theorem equiv_eq_one_iff {G U W : Type*} [Group G]
    [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W]
    {ρ : Representation F G U} {τ : Representation F G W}
    (e : ρ.Equiv τ) (g : G) : ρ g = 1 ↔ τ g = 1 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
    have hh := IntertwiningMap.isIntertwining ρ τ e.toIntertwiningMap g v
    rw [h] at hh
    convert hh.symm using 1 <;> rfl
  · intro h
    apply LinearMap.ext
    intro v
    apply e.toLinearEquiv.injective
    have hh := IntertwiningMap.isIntertwining ρ τ e.toIntertwiningMap g v
    rw [h] at hh
    convert hh using 1 <;> rfl

private theorem dual_eq_one_iff {G U : Type*} [Group G]
    [AddCommGroup U] [Module F U] (ρ : Representation F G U) (g : G) :
    ρ.dual g = 1 ↔ ρ g = 1 := by
  have hinv : ρ g⁻¹ = 1 ↔ ρ g = 1 := by
    constructor
    · intro h
      have hh := ρ.map_mul g g⁻¹
      rw [mul_inv_cancel, map_one, h, mul_one] at hh
      exact hh.symm
    · intro h
      have hh := ρ.map_mul g⁻¹ g
      rw [inv_mul_cancel, map_one, h, mul_one] at hh
      exact hh.symm
  rw [← hinv]
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    apply Module.eval_apply_injective F
    ext f
    exact congrArg (fun q : Module.End F (Module.Dual F U) => q f v) h
  · intro h
    rw [dual_apply, h]
    rfl


private theorem quotient_kernel_tensor {E L V : Type*} [Field E] [Algebra E F]
    [Group L] [AddCommGroup V] [Module E V]
    (π : SL(3,F) →* L) (ρ : Representation E L V) (hρ : Function.Injective ρ)
    (σ : F ≃+* F) (e : (extendScalars F (ρ.comp π)).Equiv (twistedTensor F σ))
    (g : SL(3,F)) : g ∈ π.ker ↔ twistedTensor F σ g = 1 := by
  have hf := (extendScalars_faithful_iff F ρ).mp hρ
  rw [← equiv_eq_one_iff e g]
  change π g = 1 ↔ extendScalars F ρ (π g) = 1
  rw [← (extendScalars F ρ).map_one, hf.eq_iff]

theorem quotient_kernel_tensor_or_dual {E L V : Type*} [Field E] [Algebra E F]
    [Group L] [AddCommGroup V] [Module E V]
    (π : SL(3,F) →* L) (ρ : Representation E L V) (hρ : Function.Injective ρ)
    (σ : F ≃+* F)
    (h : Nonempty ((extendScalars F (ρ.comp π)).Equiv (twistedTensor F σ)) ∨
      Nonempty ((extendScalars F (ρ.comp π)).Equiv (twistedTensor F σ).dual))
    (g : SL(3,F)) : g ∈ π.ker ↔ twistedTensor F σ g = 1 := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    exact quotient_kernel_tensor π ρ hρ σ e g
  · obtain ⟨e⟩ := h
    have hf := (extendScalars_faithful_iff F ρ).mp hρ
    rw [← dual_eq_one_iff (twistedTensor F σ) g, ← equiv_eq_one_iff e g]
    change π g = 1 ↔ extendScalars F ρ (π g) = 1
    rw [← (extendScalars F ρ).map_one, hf.eq_iff]

theorem tensor_cover_kernel_square {E L V : Type*} [Field E] [Algebra E F]
    [Group L] [AddCommGroup V] [Module E V]
    (π : SL(3,F) →* L) (hcentral : π.ker ≤ Subgroup.center SL(3,F))
    (ρ : Representation E L V) (hρ : Function.Injective ρ)
    (σ : F ≃+* F) (hσ : ∀ a, σ a = a ^ 2)
    (h : Nonempty ((extendScalars F (ρ.comp π)).Equiv (twistedTensor F σ)) ∨
      Nonempty ((extendScalars F (ρ.comp π)).Equiv (twistedTensor F σ).dual)) :
    π.ker = Subgroup.center SL(3,F) := by
  apply le_antisymm hcentral
  intro g hg
  obtain ⟨a, ha, hga⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have ha3 : a ^ 3 = 1 := by simpa using ha
  rw [quotient_kernel_tensor_or_dual π ρ hρ σ h g, tensor_scalar_eq_one σ g a hga.symm, hσ]
  calc
    a * a ^ 2 = a ^ 3 := by ring
    _ = 1 := ha3

theorem tensor_cover_kernel_fourth {E L V : Type*} [Field E] [Algebra E F]
    [Group L] [AddCommGroup V] [Module E V]
    (π : SL(3,F) →* L) (hcentral : π.ker ≤ Subgroup.center SL(3,F))
    (ρ : Representation E L V) (hρ : Function.Injective ρ)
    (σ : F ≃+* F) (hσ : ∀ a, σ a = a ^ 4)
    (h : Nonempty ((extendScalars F (ρ.comp π)).Equiv (twistedTensor F σ)) ∨
      Nonempty ((extendScalars F (ρ.comp π)).Equiv (twistedTensor F σ).dual)) :
    π.ker = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  intro g hg
  obtain ⟨a, ha, hga⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hcentral hg)
  have ha3 : a ^ 3 = 1 := by simpa using ha
  have hn := (quotient_kernel_tensor_or_dual π ρ hρ σ h g).mp hg
  rw [tensor_scalar_eq_one σ g a hga.symm, hσ] at hn
  have ha4 : a ^ 4 = a := by rw [show 4 = 3 + 1 from rfl, pow_succ, ha3, one_mul]
  rw [ha4, ← pow_two] at hn
  have ha1 : a = 1 := by
    calc
      a = a ^ 2 * a := by rw [hn, one_mul]
      _ = a ^ 3 := by ring
      _ = 1 := ha3
  change g = 1
  apply Subtype.ext
  rw [← hga, ha1]
  simp


/-- The two possible half-field exponents give different actual component
isomorphisms, determined by the faithful descended action. -/
theorem twisted_cover_recognition {E L V : Type*} [Field E] [Algebra E F]
    [Group L] [AddCommGroup V] [Module E V]
    (π : SL(3,F) →* L) (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center SL(3,F))
    (ρ : Representation E L V) (hρ : Function.Injective ρ)
    {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (σ : F ≃+* F) (hσ : ∀ a, σ a = a ^ (2 ^ r))
    (h : Nonempty ((extendScalars F (ρ.comp π)).Equiv (twistedTensor F σ)) ∨
      Nonempty ((extendScalars F (ρ.comp π)).Equiv (twistedTensor F σ).dual)) :
    (r = 1 ∧ π.ker = Subgroup.center SL(3,F) ∧ Nonempty (L ≃* PSL(3,F))) ∨
      (r = 2 ∧ π.ker = ⊥ ∧ Nonempty (L ≃* SL(3,F))) := by
  rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
  · have hk := tensor_cover_kernel_square π hcentral ρ hρ σ (by simpa using hσ) h
    exact Or.inl ⟨rfl, hk, ⟨(QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hk)⟩⟩
  · have hk := tensor_cover_kernel_fourth π hcentral ρ hρ σ (by simpa using hσ) h
    exact Or.inr ⟨rfl, hk, ⟨(MulEquiv.ofBijective π ⟨π.ker_eq_bot_iff.mp hk, hπ⟩).symm⟩⟩

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
