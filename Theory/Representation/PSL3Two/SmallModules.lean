module

public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.SpecificGroups.PSL3Two.Parabolics.Fano
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.BinaryPermutation
public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.FinCases

/-!
# Small binary modules for SL₃(2)

The natural module W, the augmentation core U₂ on the seven nonzero vectors,
and the trace-zero adjoint module S are concrete representations of SL₃(2).
The canonical isomorphism with PSL₃(2) is in `Matrix.PSL3Two.equiv`.

The line radical consists of the four shears fixing the plane v₂ = 0
pointwise. Its regular orbit on the other four points gives a nonzero second
displacement on U₂. Consequently a quadratic subgroup of this radical has
rank at most one. No classification of all binary modules is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.6.1–5,
printed pp.386–388, and the core obstruction in 13.8.19, printed p.953.
-/

@[expose] public section
open Matrix Representation
open Representation.BinaryOffender
namespace BinaryLinearThree
abbrev Group := Matrix.PSL3Two.SL
abbrev Vector := Matrix.PSL3Two.Fano.Vector
abbrev Point := Matrix.PSL3Two.Fano.Point
abbrev W : Representation (ZMod 2) Group Vector := specialLinearNatural 3

def pointPerm : Group →* Equiv.Perm Point where
  toFun g :=
    { toFun p := ⟨g • p.val, by
        intro h
        apply p.property
        have := congrArg (fun v : Vector => g⁻¹ • v) h
        simpa using this⟩
      invFun p := ⟨g⁻¹ • p.val, by
        intro h
        apply p.property
        have := congrArg (fun v : Vector => g • v) h
        simpa using this⟩
      left_inv p := by apply Subtype.ext; simp
      right_inv p := by apply Subtype.ext; simp }
  map_one' := by ext p : 1; apply Subtype.ext; simp
  map_mul' g h := by ext p : 1; apply Subtype.ext; simp [mul_smul]

abbrev Core := BinaryPermutation.core Point
def U₂ : Representation (ZMod 2) Group Core :=
  (BinaryPermutation.coreRepresentation Point).comp pointPerm

noncomputable def traceZero : Subrepresentation (W.linHom W) where
  toSubmodule := (LinearMap.trace (ZMod 2) Vector).ker
  apply_mem_toSubmodule g f hf := by
    change LinearMap.trace (ZMod 2) Vector (W g ∘ₗ f ∘ₗ W g⁻¹) = 0
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    have hh : W g⁻¹ ∘ₗ W g = LinearMap.id := by
      rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hh, LinearMap.comp_id]
    exact hf
noncomputable abbrev Steinberg := traceZero.toSubmodule
noncomputable def S : Representation (ZMod 2) Group Steinberg := traceZero.toRepresentation

/-- Two independent elements of the line radical. -/
private def a : Group := ⟨!![1,0,1; 0,1,0; 0,0,1], by decide⟩
private def b : Group := ⟨!![1,0,0; 0,1,1; 0,0,1], by decide⟩
def shear : Multiplicative (ZMod 2 × ZMod 2) →* Group where
  toFun c := ⟨!![1,0,c.toAdd.1; 0,1,c.toAdd.2; 0,0,1], by
    simp [Matrix.det_fin_three]⟩
  map_one' := by apply Subtype.ext; decide
  map_mul' c d := by
    apply Subtype.ext
    change !![1,0,c.toAdd.1+d.toAdd.1; 0,1,c.toAdd.2+d.toAdd.2; 0,0,1] =
      !![1,0,c.toAdd.1; 0,1,c.toAdd.2; 0,0,1] *
        !![1,0,d.toAdd.1; 0,1,d.toAdd.2; 0,0,1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]
def R : Subgroup Group := shear.range

theorem shear_injective : Function.Injective shear := by
  intro c d h
  have h0 := congrArg (fun g : Group => g.val 0 2) h
  have h1 := congrArg (fun g : Group => g.val 1 2) h
  exact Prod.ext h0 h1

theorem card_R : Nat.card R = 4 := by
  change Nat.card shear.range = 4
  rw [← Nat.card_congr (MonoidHom.ofInjective shear_injective).toEquiv, Nat.card_eq_fintype_card]
  decide

private theorem a_mem_R : a ∈ R := ⟨Multiplicative.ofAdd (1,0), rfl⟩
private theorem b_mem_R : b ∈ R := ⟨Multiplicative.ofAdd (0,1), rfl⟩

private def outside : Point := ⟨![0,0,1], by decide⟩
private def inside : Point := ⟨![1,0,0], by decide⟩
private def seed : Core := ⟨Pi.single outside 1 + Pi.single inside 1, by
  simp [BinaryPermutation.core, LinearMap.mem_ker, map_add,
    BinaryPermutation.augmentation, outside, inside]
  decide⟩

private theorem a_inv : a⁻¹ = a := by
  apply inv_eq_of_mul_eq_one_right
  decide
private theorem b_inv : b⁻¹ = b := by
  apply inv_eq_of_mul_eq_one_right
  decide

private theorem displacement_nonzero : U₂ a (U₂ b seed - seed) ≠ U₂ b seed - seed := by
  intro he
  have hh := congrArg (fun v : Core => v.val outside) he
  change seed.val ((pointPerm b).symm ((pointPerm a).symm outside)) -
      seed.val ((pointPerm a).symm outside) =
        seed.val ((pointPerm b).symm outside) - seed.val outside at hh
  change seed.val (pointPerm b⁻¹ (pointPerm a⁻¹ outside)) -
      seed.val (pointPerm a⁻¹ outside) =
        seed.val (pointPerm b⁻¹ outside) - seed.val outside at hh
  rw [a_inv,b_inv] at hh
  have hn : seed.val (pointPerm b (pointPerm a outside)) -
      seed.val (pointPerm a outside) ≠ seed.val (pointPerm b outside) - seed.val outside := by
    decide
  exact hn hh

theorem R_not_quadratic : ¬ IsQuadratic U₂ R := by
  intro h
  exact displacement_nonzero (h a a_mem_R
    b b_mem_R seed)

theorem quadratic_rank_le_one (A : Subgroup Group) (hA : A ≤ R)
    (hq : IsQuadratic U₂ A) : rank A ≤ 1 := by
  have hne : A ≠ R := by intro he; exact R_not_quadratic (he ▸ hq)
  have hc : Nat.card A < 4 := by
    have hle := Subgroup.card_le_of_le hA
    rw [card_R] at hle
    have hneq : Nat.card A ≠ 4 := by
      intro he
      apply hne
      exact Subgroup.eq_of_le_of_card_ge hA (by rw [card_R, he])
    omega
  have hlog := Nat.log_lt_of_lt_pow' (b := 2) (by decide : 2 ≠ 0) hc
  exact Nat.le_of_lt_succ hlog
end BinaryLinearThree

