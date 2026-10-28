module

public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryOffender.Defs

/-!
# Quadratic Klein four actions on five-point permutation quotients

Two double transpositions on four of the five points have a second displacement
of a coordinate vector equal to the weight-four vector. If they act quadratically
on a quotient, this vector is in its kernel. Alternating invariance then forces
the augmentation core into the kernel, so the quotient action is trivial.

This is the last module contradiction of Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 13.8.20, printed p.955
(combined manuscript, 1 March 2004). The noncentrality in 13.8.4(5) matters:
a nonzero trivial quotient of the permutation module does exist.
-/

public section

namespace BinaryPermutation.FiveQuadratic
open Representation.BinaryOffender

private abbrev a : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3
private abbrev b : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3
private def w : Full (Fin 5) := ![1, 1, 1, 1, 0]

private theorem displacement :
    representation (Fin 5) a (representation (Fin 5) b (Pi.single 0 1) - Pi.single 0 1) -
      (representation (Fin 5) b (Pi.single 0 1) - Pi.single 0 1) = w := by
  ext i
  fin_cases i <;> decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A quotient on which the two marked double transpositions have zero
second displacement has trivial symmetric-group action. -/
theorem quotient_action_trivial
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 5)) V)
    (f : Full (Fin 5) →ₗ[ZMod 2] V) (hf : Function.Surjective f)
    (heq : ∀ g v, f (representation (Fin 5) g v) = ρ g (f v))
    (hquad : ∀ v,
      ρ (Equiv.swap 0 1 * Equiv.swap 2 3)
        (ρ (Equiv.swap 0 2 * Equiv.swap 1 3) v - v) =
          ρ (Equiv.swap 0 2 * Equiv.swap 1 3) v - v) :
    ∀ g v, ρ g v = v := by
  have hw : w ∈ f.ker := by
    rw [LinearMap.mem_ker, ← displacement, map_sub, heq, map_sub, heq]
    exact sub_eq_zero.mpr (hquad _)
  have h_inv : ∀ g : alternatingGroup (Fin 5), ∀ v ∈ f.ker,
      representation (Fin 5) g.val v ∈ f.ker := by
    intro g v hv
    rw [LinearMap.mem_ker, heq, LinearMap.mem_ker.mp hv, map_zero]
  have hcore : core (Fin 5) ≤ f.ker := by
    rcases invariant_le_constants_or_core_le (by decide : 5 ≤ Fintype.card (Fin 5))
        f.ker h_inv with h | h
    · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h hw)
      have hc0 := congrFun hc 0
      have hc4 := congrFun hc 4
      norm_num [allOne, w] at hc0 hc4
      exact (zero_ne_one (hc4.symm.trans hc0)).elim
    · exact h
  intro g v
  obtain ⟨u, rfl⟩ := hf v
  have hm : representation (Fin 5) g u - u ∈ core (Fin 5) := by
    change augmentation (Fin 5) _ = 0
    rw [map_sub, augmentation_permute, sub_self]
  have hz := LinearMap.mem_ker.mp (hcore hm)
  rw [map_sub, heq] at hz
  exact sub_eq_zero.mp hz

/-- Transport through an actual identification with S₅. A subgroup containing
the marked Klein four cannot act quadratically on a noncentral quotient of the
five-point permutation module. The marking must be supplied by the caller. -/
theorem not_quadratic_of_noncentral_quotient
    {H : Type*} [Group H] (e : H ≃* Equiv.Perm (Fin 5))
    (ρ : Representation (ZMod 2) H V)
    (f : Full (Fin 5) →ₗ[ZMod 2] V) (hf : Function.Surjective f)
    (heq : ∀ g v, f (representation (Fin 5) g v) = ρ (e.symm g) (f v))
    (hnoncentral : ∃ h v, ρ h v ≠ v) (A : Subgroup H)
    (ha : e.symm (Equiv.swap 0 1 * Equiv.swap 2 3) ∈ A)
    (hb : e.symm (Equiv.swap 0 2 * Equiv.swap 1 3) ∈ A) :
    ¬ IsQuadratic ρ A := by
  intro hquad
  let σ : Representation (ZMod 2) (Equiv.Perm (Fin 5)) V := ρ.comp e.symm.toMonoidHom
  have htrivial := quotient_action_trivial σ f hf heq
    (fun v => hquad _ ha _ hb v)
  obtain ⟨h, v, hv⟩ := hnoncentral
  have ht := htrivial (e h) v
  change ρ (e.symm (e h)) v = v at ht
  exact hv (by simpa only [e.symm_apply_apply] using ht)

end BinaryPermutation.FiveQuadratic
