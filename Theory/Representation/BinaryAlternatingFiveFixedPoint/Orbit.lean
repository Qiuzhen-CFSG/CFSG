module
public import Theory.Representation.BinaryAlternatingFiveFixedPoint
-- Internal proof extension: reuse the existing five-point orbit map without
-- exposing its choice of point representatives in the public API.
import all Theory.Representation.BinaryAlternatingFiveFixedPoint

/-!
# A Borel-fixed vector in the five-point augmentation module

The five translates of a Borel-fixed vector define the usual permutation
module map. If the target has no global fixed vectors, their sum is zero.
Thus the original vector belongs to the image of the augmentation core;
irreducibility of that core makes the map injective. No irreducibility of
the target is required. The point-stabilizer version retains the specified
A₅ marking and vector.

This is the module argument used in Aschbacher–Smith 5.1.19 and the
field-four branch of 14.3.6(1). The internal import shares the existing
orbit-map implementation; no private choice is exposed in the statements.
-/

public noncomputable section
open Representation BinaryPermutation
namespace Representation.BinaryAlternatingFiveFixedPoint
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- With no global fixed vectors, a nonzero Borel-fixed vector lies in an
actual embedded five-point augmentation module, even if the target is reducible. -/
theorem core_embedding_of_borel_fixed
    (ρ : Representation (ZMod 2) A5 W) (v : W)
    (hv : ∀ b : BinaryPermutation.AlternatingFiveBorel.B, ρ b.val v = v)
    (hv0 : v ≠ 0) (hfixed : ρ.invariants = ⊥) :
    ∃ f : IntertwiningMap (alternatingCoreRepresentation (Fin 5)) ρ,
      Function.Injective f ∧ v ∈ LinearMap.range f.toLinearMap := by
  have hmove : ∃ g, ρ g v ≠ v := by
    by_contra! hall
    exact hv0 (hfixed.le hall)
  let : (alternatingCoreRepresentation (Fin 5)).IsIrreducible :=
    coreNaturalEquiv.irreducible_of_euqiv (alternatingNatural_isIrreducible (by decide))
  let f := orbitMap ρ v hv
  have hf : Function.Injective f :=
    (IsIrreducible.injective_or_eq_zero f).resolve_right (orbitMap_ne_zero ρ v hv hmove)
  have hsum : (∑ i : Fin 5, value ρ v i) = 0 := by
    apply hfixed.le
    intro g
    rw [map_sum]
    simp only [← value_equivariant ρ v hv]
    exact Equiv.sum_comp g.val (value ρ v)
  let a : core (Fin 5) := ⟨(fun _ => 1) - Pi.single 4 1, by
    norm_num [mem_core, Finset.sum_sub_distrib]
    decide⟩
  refine ⟨f,hf,a,?_⟩
  change (∑ i : Fin 5, ((1 : ZMod 2) - (Pi.single (4 : Fin 5) (1 : ZMod 2) : Fin 5 → ZMod 2) i) • value ρ v i) = v
  simp only [sub_smul,one_smul,Finset.sum_sub_distrib,hsum]
  simp only [Pi.single_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',
    Finset.mem_univ,if_true,zero_sub,value_four ρ v hv]
  rw [← neg_one_smul (ZMod 2), show (-1 : ZMod 2) = 1 by decide, one_smul]

/-- The embedded orthogonal module contains the specified fixed vector for
any point Borel, retaining the original representation and group marking. -/
theorem core_embedding_of_point_fixed
    (ρ : Representation (ZMod 2) A5 W) (v : W)
    (hv0 : v ≠ 0) (hfixed : ρ.invariants = ⊥) (i : Fin 5)
    (hi : ∀ g : A5, g.val i = i → ρ g v = v) :
    ∃ f : IntertwiningMap (alternatingCoreRepresentation (Fin 5)) ρ,
      Function.Injective f ∧ v ∈ LinearMap.range f.toLinearMap := by
  let a := mover i
  let w := ρ a⁻¹ v
  have hw : w ≠ 0 := by
    intro hz
    apply hv0
    have hh := congrArg (ρ a) hz
    simpa only [w, ρ.self_inv_apply, map_zero] using hh
  have hB : ∀ b : BinaryPermutation.AlternatingFiveBorel.B, ρ b.val w = w := by
    intro b
    have hbi : (a * b.val * a⁻¹).val i = i := by
      change a.val (b.val.val (a.val.symm i)) = i
      have hai : a.val.symm i = 4 := a.val.symm_apply_eq.mpr (mover_apply i).symm
      rw [hai, show b.val.val 4 = 4 from b.property]
      exact mover_apply i
    have hh := congrArg (ρ a⁻¹) (hi (a * b.val * a⁻¹) hbi)
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel_left] at hh
    simpa only [w, map_mul, Module.End.mul_apply] using hh
  obtain ⟨f,hf,u,hu⟩ := core_embedding_of_borel_fixed ρ w hB hw hfixed
  refine ⟨f,hf,alternatingCoreRepresentation (Fin 5) a u,?_⟩
  exact (IntertwiningMap.isIntertwining _ _ f a u).trans
    ((congrArg (ρ a) hu).trans (ρ.self_inv_apply a v))
end Representation.BinaryAlternatingFiveFixedPoint
