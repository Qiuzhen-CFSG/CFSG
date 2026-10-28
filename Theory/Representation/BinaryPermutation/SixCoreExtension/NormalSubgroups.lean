module
public import Theory.Representation.BinaryPermutation.SixCoreExtension.Residual.Transport
public import Mathlib.Algebra.Module.ZMod
/-!
# Normal subgroups meeting the binary six-coordinate radical

A normal subgroup of the augmentation-core semidirect product by A₆ that
contains a nonconstant vector contains the whole radical. The same conclusion
holds if it contains every commutator of such a vector: the three displayed
even permutations detect constant vectors. The proof uses the actual binary
module lattice and a small six-coordinate certificate.

This supplies the literal normal-subgroup calculation for the binary M₂₂
hexad in Aschbacher--Smith I.2.2(6), p.412, and 2.3.9(7), p.526.
-/

public section
open Subgroup
open BinaryPermutation
namespace BinaryPermutation.SixCoreExtension
noncomputable section
/-- A normal subgroup containing a nonconstant vector contains the radical. -/
theorem normal_vector_range_of_nonconstant (N : Subgroup Model) [N.Normal] (v : V)
    (hv : coreToNatural (Fin 6) v ≠ 0)
    (hvn : vector (Multiplicative.ofAdd v) ∈ N) : vector.range ≤ N := by
  let D : Submodule (ZMod 2) V := AddSubgroup.toZModSubmodule 2 (N.comap vector).toAddSubgroup'
  let W := D.map (core (Fin 6)).subtype
  have hW : ∀ g : A, ∀ w ∈ W, representation (Fin 6) g.val w ∈ W := by
    intro g w hw
    obtain ⟨x,hx,rfl⟩ := hw
    refine ⟨coreRepresentation (Fin 6) g.val x, ?_, rfl⟩
    change vector (Multiplicative.ofAdd (coreRepresentation (Fin 6) g.val x)) ∈ N
    rw [← conj_vector]
    exact (inferInstance : N.Normal).conj_mem _ hx _
  rcases invariant_le_constants_or_core_le (by decide : 5 ≤ Fintype.card (Fin 6)) W hW with hc | hc
  · have hh := hc (show v.val ∈ W from ⟨v,hvn,rfl⟩)
    exact (hv (Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr hh))).elim
  · rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy,he⟩ := hc x.toAdd.property
    have he' : y = x.toAdd := Subtype.ext he
    rw [he'] at hy
    exact hy
private def a : A := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by simp [Equiv.Perm.mem_alternatingGroup]⟩
private def b : A := ⟨Equiv.swap 0 2 * Equiv.swap 4 5, by simp [Equiv.Perm.mem_alternatingGroup]⟩
private def c : A := ⟨Equiv.swap 0 3 * Equiv.swap 1 5, by simp [Equiv.Perm.mem_alternatingGroup]⟩

private theorem displacement_detection : ∀ (v : Full (Fin 6)) (x y z : ZMod 2),
    x • allOne (Fin 6) = representation (Fin 6) a.val v - v →
    y • allOne (Fin 6) = representation (Fin 6) b.val v - v →
    z • allOne (Fin 6) = representation (Fin 6) c.val v - v →
    v = v 0 • allOne (Fin 6) := by decide

/-- Killing the commutators of any nonconstant vector kills the whole core. -/
theorem normal_vector_range_of_displacements (N : Subgroup Model) [N.Normal] (v : V)
    (hv : coreToNatural (Fin 6) v ≠ 0)
    (hN : ∀ g : A, vector (Multiplicative.ofAdd
      (coreRepresentation (Fin 6) g.val v - v)) ∈ N) : vector.range ≤ N := by
  by_contra hn
  have hconst (g : A) :
      representation (Fin 6) g.val v.val - v.val ∈ constants (Fin 6) := by
    have he : coreToNatural (Fin 6) (coreRepresentation (Fin 6) g.val v - v) = 0 := by
      by_contra he
      exact hn (normal_vector_range_of_nonconstant N _ he (hN g))
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val he)
  obtain ⟨x,hx⟩ := Submodule.mem_span_singleton.mp (hconst a)
  obtain ⟨y,hy⟩ := Submodule.mem_span_singleton.mp (hconst b)
  obtain ⟨z,hz⟩ := Submodule.mem_span_singleton.mp (hconst c)
  apply hv
  apply Subtype.ext
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.mem_span_singleton.mpr ⟨v.val 0,(displacement_detection v.val x y z hx hy hz).symm⟩

/-- An equivalent group-theoretic formulation, using the literal semidirect product. -/
theorem normal_vector_range_of_commutators (N : Subgroup Model) [N.Normal] (v : V)
    (hv : coreToNatural (Fin 6) v ≠ 0)
    (hN : ∀ g : Model, g * vector (Multiplicative.ofAdd v) * g⁻¹ *
      (vector (Multiplicative.ofAdd v))⁻¹ ∈ N) : vector.range ≤ N := by
  apply normal_vector_range_of_displacements N v hv
  intro a
  have h := hN (SemidirectProduct.inr a)
  change MulAut.conj (SemidirectProduct.inr a) (vector (Multiplicative.ofAdd v)) *
    (vector (Multiplicative.ofAdd v))⁻¹ ∈ N at h
  rw [conj_vector, ← map_inv, ← map_mul] at h
  simpa only [sub_eq_add_neg, ofAdd_add, ofAdd_neg] using h

end
end BinaryPermutation.SixCoreExtension
