module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.PointRadical
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Tactic.FinCases

/-!
# Coordinates for the literal natural tensor module

The S₃ augmentation plane is identified with its first two coordinates; the
third is their sum. Tensoring with the three-dimensional natural module gives
three rows of this plane. We verify the action formula on pure tensors and
identify cyclic fixed codimension with displacement rank.

These coordinate calculations support Aschbacher–Smith 13.8.21(1), printed
p.957, without making the source's ambient or critical-pair assumptions.
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

@[expose] public section
open Matrix Representation Representation.BinaryOffender TensorProduct
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.TensorFacts

abbrev Coordinates := Fin 3 → Fin 2 → ZMod 2

def s3Coordinates : S3Natural ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun v := ![v.val 0, v.val 1]
  invFun x := ⟨![x 0,x 1,x 0+x 1], by
    simp [BinaryPermutation.mem_core, Fin.sum_univ_three]
    generalize x 0 = a, x 1 = b
    revert a b
    decide⟩
  left_inv v := by
    apply Subtype.ext
    have hv := v.property
    rw [BinaryPermutation.mem_core, Fin.sum_univ_three] at hv
    ext i
    fin_cases i <;> simp
    have hh : ∀ a b c : ZMod 2, a + b + c = 0 → a + b = c := by decide
    exact hh _ _ _ hv
  right_inv x := by ext i; fin_cases i <;> rfl
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' c v := by ext i; fin_cases i <;> rfl

noncomputable def coordinates : TensorSpace ≃ₗ[ZMod 2] Coordinates :=
  ((TensorProduct.comm (ZMod 2) BinaryLinearThree.Vector S3Natural).trans
    (TensorProduct.piScalarRight (ZMod 2) (ZMod 2) S3Natural (Fin 3))).trans
      (LinearEquiv.piCongrRight fun _ => s3Coordinates)

@[simp] theorem coordinates_tmul (v : BinaryLinearThree.Vector) (w : S3Natural) :
    coordinates (v ⊗ₜ[ZMod 2] w) = fun i => v i • s3Coordinates w := by
  ext i k
  simp [coordinates, TensorProduct.piScalarRightHom_tmul, LinearEquiv.piCongrRight_apply]

abbrev expand (x : Fin 2 → ZMod 2) : Fin 3 → ZMod 2 := ![x 0, x 1, x 0 + x 1]

def s3Action (p : Equiv.Perm (Fin 3)) (x : Fin 2 → ZMod 2) : Fin 2 → ZMod 2 :=
  fun k => expand x (p.symm k.castSucc)

lemma s3Coordinates_action (p : Equiv.Perm (Fin 3)) (w : S3Natural) :
    s3Coordinates (BinaryPermutation.coreRepresentation (Fin 3) p w) =
      s3Action p (s3Coordinates w) := by
  have h := congrArg Subtype.val (s3Coordinates.symm_apply_apply w)
  change expand (s3Coordinates w) = w.val at h
  ext k
  fin_cases k <;> exact (congrFun h _).symm

def matrixAction (m : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (p : Equiv.Perm (Fin 3)) (x : Coordinates) : Coordinates :=
  fun i k => ∑ j, m i j * s3Action p (x j) k

private lemma s3Action_smul (p : Equiv.Perm (Fin 3)) (c : ZMod 2) (x : Fin 2 → ZMod 2) :
    s3Action p (c • x) = c • s3Action p x := by
  ext k
  dsimp [s3Action, expand]
  have h : expand (c • x) = c • expand x := by
    ext j; fin_cases j <;> simp [expand, mul_add]
  exact congrFun h (p.symm k.castSucc)

private lemma s3Action_add (p : Equiv.Perm (Fin 3)) (x y : Fin 2 → ZMod 2) :
    s3Action p (x + y) = s3Action p x + s3Action p y := by
  ext k
  have h : expand (x + y) = expand x + expand y := by
    ext j; fin_cases j <;> simp [expand] <;> ring
  exact congrFun h (p.symm k.castSucc)

private lemma s3Action_zero (p : Equiv.Perm (Fin 3)) : s3Action p 0 = 0 := by
  have := s3Action_smul p 0 0
  simpa using this

lemma coordinates_action (g : TensorGroup) (z : TensorSpace) :
    coordinates (naturalTensor g z) = matrixAction g.1.val g.2 (coordinates z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    ext i k
    simp [matrixAction, s3Action_zero]
  | tmul v w =>
    change coordinates ((BinaryLinearThree.W g.1 v) ⊗ₜ[ZMod 2]
      (BinaryPermutation.coreRepresentation (Fin 3) g.2 w)) = _
    simp only [coordinates_tmul, s3Coordinates_action]
    ext i k
    change (∑ j, g.1.val i j * v j) * s3Action g.2 (s3Coordinates w) k = _
    simp [matrixAction, s3Action_smul, Finset.sum_mul, mul_assoc]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ext i k
    simp [matrixAction, s3Action_add, mul_add, Finset.sum_add_distrib]

theorem finrank_tensorSpace : Module.finrank (ZMod 2) TensorSpace = 6 := by
  rw [coordinates.finrank_eq]
  simp [Coordinates, Module.finrank_pi_fintype]


lemma mem_fixedSpace_zpowers {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (g : G) (v : V) :
    v ∈ fixedSpace ρ (Subgroup.zpowers g) ↔ ρ g v = v := by
  exact Representation.mem_invariants_iff_of_forall_mem_zpowers
    (ρ.comp (Subgroup.zpowers g).subtype) ⟨g, Subgroup.mem_zpowers g⟩
    (fun x => by obtain ⟨n, hn⟩ := x.property; exact ⟨n, Subtype.ext hn⟩) v

lemma fixedCodim_zpowers_eq_range (g : TensorGroup) :
    fixedCodim naturalTensor (Subgroup.zpowers g) =
      Module.finrank (ZMod 2) (LinearMap.range (naturalTensor g - 1)) := by
  have hk : fixedSpace naturalTensor (Subgroup.zpowers g) =
      LinearMap.ker (naturalTensor g - 1) := by
    ext v
    simp [mem_fixedSpace_zpowers, LinearMap.mem_ker, sub_eq_zero]
  unfold fixedCodim
  rw [hk]
  exact (LinearMap.quotKerEquivRange _).finrank_eq

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.TensorFacts
