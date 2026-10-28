module

public import CFSG.Quasithin.Chapter1.Section03.Basic.FrattiniAction
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Finite-field powers and their passage to the Frattini quotient

Regard a ring automorphism as an automorphism over the prime field and use
the Frobenius generator of its Galois group. On a torus, a concrete coordinate
calculation can then turn this uniform field power into a group power.
The separate conjugation lemma passes a proved ambient formula to B/Φ(B).

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511; the finite-field Galois theorem is in Mathlib.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions

/-- Each automorphism of a finite binary field is a single uniform
Frobenius power on all its elements. -/
theorem binary_field_power {F : Type*} [Field F] [Finite F] [CharP F 2]
    (σ : F ≃+* F) : ∃ k : ℕ, ∀ x, σ x = x ^ (2 ^ k) := by
  let _ := ZMod.algebra F 2
  let a : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := σ) (fun z => by
    exact congrArg (fun f : ZMod 2 →+* F => f z)
      (Subsingleton.elim (σ.toRingHom.comp (algebraMap (ZMod 2) F))
        (algebraMap (ZMod 2) F)))
  obtain ⟨k, hk⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 F a
  refine ⟨k, fun x => ?_⟩
  have hx := hk x
  change σ x = x ^ (Nat.card (ZMod 2) ^ k) at hx
  simpa only [Nat.card_eq_fintype_card, ZMod.card] using hx

/-- An actual ambient conjugation formula descends to the Frattini quotient.
The exponent may depend on the actor. -/
theorem frattini_action_pow {G : Type*} [Group G] (B S : Subgroup G)
    (hSB : S ≤ normalizer B)
    (hp : ∀ s : S, ∃ k : ℕ, ∀ b : B,
      (s : G) * (b : G) * (s : G)⁻¹ = (b : G) ^ k) :
    ∀ (s : S) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction S B hSB s v ∈ zpowers v := by
  let _ := conjMulDistribMulActionOfLeNormalizer S B hSB
  intro s v
  obtain ⟨k, hk⟩ := hp s
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (frattini B) v
  have he : MulDistribMulAction.toMulAut S B s b = b ^ k := Subtype.ext (hk b)
  change quotientAut (frattini B) (MulDistribMulAction.toMulAut S B s)
    (QuotientGroup.mk' (frattini B) b) ∈ _
  rw [quotientAut_apply_mk, he, map_pow]
  exact pow_mem (mem_zpowers _) _

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions
