module
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic.Group
/-!
# Solvability of stabilizers in central conjugation sections

For an actor subgroup R, fixing the coordinate of w means that [w,R]
lies in the coordinate kernel. When that kernel is centralized by the
actor, these commutators define a homomorphism. Its kernel embeds into
C_R(w), so a solvable point centralizer and a solvable coordinate kernel
make the quotient-vector stabilizer solvable. This does not identify
fixing a coset with centralizing its representative, or require the section
numerator to lie in R.

Source application: Aschbacher–Smith, proof of 12.6.26, printed p.832,
lifting the point stabilizer on U_H/V₁ to the original component.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
open BinaryNaturalDual.VectorStabilizers
variable {G : Type*} [Group G] {H A B : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W}
/-- Fixing a quotient vector gives a central-kernel commutator homomorphism;
its kernel embeds into the original point centralizer. -/
theorem stabilizer_isSolvable_of_central_kernel
    (d : BinaryConjugationSection H A B ρ)
    (hc : H ≤ centralizer (B : Set G)) [Group.IsSolvable B]
    (R : Subgroup G) (hR : R ≤ H)
    (w : A) [Group.IsSolvable ((centralizer ({(w : G)} : Set G)).subgroupOf R)] :
    Group.IsSolvable (representationStabilizer (ρ.comp (inclusion hR)) (d.coordinates w).toAdd) := by
  let P := representationStabilizer (ρ.comp (inclusion hR)) (d.coordinates w).toAdd
  have hcomm (x : P) : ⁅(w : G),(x.val : G)⁆ ∈ B := by
    have hcoord := d.equivariant (inclusion hR x.val) w
    change (d.coordinates ⟨(x.val : G)*w*(x.val : G)⁻¹,_⟩).toAdd =
      ρ (inclusion hR x.val) (d.coordinates w).toAdd at hcoord
    rw [show ρ (inclusion hR x.val) (d.coordinates w).toAdd = (d.coordinates w).toAdd from x.property] at hcoord
    let v : A := ⟨(x.val : G)*w*(x.val : G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized (hR x.val.property)) w).mp w.property⟩
    have hv : (v : G)*(w : G)⁻¹ ∈ B := by
      apply (d.coordinates_eq_one_iff (v*w⁻¹)).mp
      rw [map_mul,map_inv,show d.coordinates v = d.coordinates w from hcoord,mul_inv_cancel]
    have hh : ⁅(x.val : G),(w : G)⁆ ∈ B := hv
    rw [←commutatorElement_inv]
    exact B.inv_mem hh
  let χ : P →* B := {
    toFun x := ⟨⁅(w : G),(x.val : G)⁆,hcomm x⟩
    map_one' := Subtype.ext (by simp)
    map_mul' x y := by
      apply Subtype.ext
      change ⁅(w : G),(x.val : G)*(y.val : G)⁆ =
        ⁅(w : G),(x.val : G)⁆*⁅(w : G),(y.val : G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hh := hc (hR x.val.property) _ (hcomm y)
      calc
        _ = ⁅(w : G),(x.val : G)⁆*((x.val : G)*⁅(w : G),(y.val : G)⁆)*(x.val : G)⁻¹ := by group
        _ = _ := by rw [←hh]; group }
  let C := (centralizer ({(w : G)} : Set G)).subgroupOf R
  let f : χ.ker →* C := {
    toFun x := ⟨x.val.val,by
      have he : ⁅(w : G),(x.val.val : G)⁆ = 1 := congrArg Subtype.val x.property
      exact mem_centralizer_singleton_iff.mpr
        (commutatorElement_eq_one_iff_mul_comm.mp he).symm⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : C => v.val) h
  let : Group.IsSolvable χ.ker := Group.isSolvable_of_isSolvable_injective hf
  exact Group.isSolvable_of_ker_le_range χ.ker.subtype χ (by rw [range_subtype])
end Representation.BinaryConjugationSection
