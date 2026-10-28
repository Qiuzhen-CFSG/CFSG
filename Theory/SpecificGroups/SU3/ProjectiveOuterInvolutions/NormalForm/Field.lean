module

public import BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Algebra.ZMod

/-!
# The field involution in the unitary normal form

Automorphisms of a finite field form a cyclic group, by identifying them with
its Galois group over the prime field. The two cardinalities in the unitary
setup ensure that the stored Hermitian conjugation is nontrivial, so it is the
unique nontrivial automorphism whose square is one.

This supplies the finite-field step of GLS, Volume 3, Theorem 2.5.12(d), with
matrix-field order `q²` and fixed-field order `q` as in Section 2.7.
-/

namespace BenderSuzuki.MatrixGroups.HermitianForm

public theorem finiteFieldAut_isCyclic {E : Type*} [Field E] [Finite E] : IsCyclic (E ≃+* E) := by
  obtain ⟨p, hp⟩ := CharP.exists E
  let := hp
  let : Fact p.Prime := ⟨CharP.char_is_prime E p⟩
  let := ZMod.algebra E p
  let f : (E ≃+* E) →* (E ≃ₐ[ZMod p] E) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) (fun z => by
        exact congrArg (fun f : ZMod p →+* E => f z)
          (Subsingleton.elim (σ.toRingHom.comp (algebraMap (ZMod p) E))
            (algebraMap (ZMod p) E)))
      map_one' := by ext; rfl
      map_mul' := by intros; ext; rfl }
  exact isCyclic_of_injective f (fun σ τ h => RingEquiv.ext fun x =>
    congrArg (fun f : E ≃ₐ[ZMod p] E => f x) h)

variable {E : Type*} [Field E] (J : HermitianForm 3 E)

public theorem conj_ne_one_of_card (n : ℕ) (hn : 2 ≤ n) [Finite E]
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {z:E // J.conj z=z} = 2^n) : J.conj ≠ 1 := by
  intro h
  let e : {z:E // J.conj z=z} ≃ E :=
    { toFun := Subtype.val
      invFun := fun z => ⟨z, by rw [h]; rfl⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Nat.card_congr e
  rw [hcard, hfixed] at he
  have := Nat.one_lt_two_pow (show n ≠ 0 by omega)
  nlinarith

public theorem field_involution_eq_conj [Finite E] (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {z:E // J.conj z=z} = 2^n)
    (σ : E ≃+* E) (hσ : σ^2 = 1) (hσne : σ ≠ 1) : σ = J.conj := by
  classical
  let := finiteFieldAut_isCyclic (E := E)
  let : Finite (E ≃+* E) := Finite.of_injective (fun σ : E ≃+* E => (σ : E → E))
    DFunLike.coe_injective
  let := Fintype.ofFinite (E ≃+* E)
  have hJne := conj_ne_one_of_card J n hn hcard hfixed
  have hJsq : J.conj^2 = 1 := by ext z; exact J.conj_involutive z
  by_contra hne
  have hsub : ({1, σ, J.conj} : Finset (E ≃+* E)) ⊆ {τ ∈ (Finset.univ : Finset (E ≃+* E)) | τ^2 = 1} := by
    intro τ hτ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hτ with rfl | rfl | rfl
    · simp
    · exact hσ
    · exact hJsq
  have hle := (Finset.card_le_card hsub).trans
    (IsCyclic.card_pow_eq_one_le (α := E ≃+* E) (n := 2) (by decide))
  simp [hne, Ne.symm hσne, Ne.symm hJne] at hle

end BenderSuzuki.MatrixGroups.HermitianForm
