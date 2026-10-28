module

public import Theory.GroupAction.CyclicAuxiliaryIndex
public import Theory.GroupAction.CyclicCommutatorTransport

/-!
# Transporting the full marked cyclic commutator

An equivariant homomorphism into an ambient conjugation action maps the
entire cyclic-action commutator onto the corresponding group commutator.
Its proof uses every power of the original actor. Injective maps preserve
the intrinsic two-core quotient, and surjective maps cannot increase its
order. These facts let a local index bound descend through a quotient and
then restrict to the genuine component carrier.

Source application: Aschbacher–Smith 13.8.20, printed p.954/PDF p.971.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupAction.CyclicAuxiliaryIndex
variable {D E : Type*} [Group D] [Group E]

/-- The intrinsic two-core quotient cannot grow under a surjection. -/
theorem quotient_twoCore_card_le_of_surjective [Finite D] [Finite E]
    (f : D →* E) (hf : Function.Surjective f) :
    Nat.card (E ⧸ pCore 2 E) ≤ Nat.card (D ⧸ pCore 2 D) := by
  have hn : ((pCore 2 D).map f).Normal := (inferInstance : (pCore 2 D).Normal).map f hf
  have hc : (pCore 2 D).map f ≤ pCore 2 E := le_sSup ⟨hn, pCore_isPGroup.map f⟩
  have hh : pCore 2 D ≤ (pCore 2 E).comap f := map_le_iff_le_comap.mp hc
  exact Nat.card_le_card_of_surjective (QuotientGroup.map _ _ f hh)
    (QuotientGroup.map_surjective_of_surjective _ _ f
      ((QuotientGroup.mk'_surjective _).comp hf) hh)

/-- An embedding preserves the intrinsic two-core quotient of its image. -/
theorem quotient_twoCore_card_map_of_injective (f : D →* E) (hf : Function.Injective f)
    (A : Subgroup D) :
    Nat.card (A ⧸ pCore 2 A) = Nat.card (A.map f ⧸ pCore 2 (A.map f)) := by
  let e := equivMapOfInjective A f hf
  exact Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv

/-- Every power of the marked actor is retained in this image identity. -/
theorem map_cyclic_commutator_conjugation [Finite D] [Finite E]
    (f : D →* E) (a : MulAut D) (t : E) (B : Subgroup D)
    (hB : B.map a.toMonoidHom = B)
    (heq : ∀ x : D, f (a x) = t * f x * t⁻¹) :
    (commutatorSubgroup (zpowers a) D B).map f = ⁅B.map f, zpowers t⁆ := by
  have hn (n : ℕ) (x : D) : f ((a ^ n) x) = t ^ n * f x * (t ^ n)⁻¹ := by
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, heq, ih, pow_succ']
      group
  have ht : t ∈ normalizer (B.map f : Set E) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      change t * f x * t⁻¹ ∈ B.map f
      rw [← heq]
      exact mem_map_of_mem f (hB.le (mem_map_of_mem a.toMonoidHom hx))
    · exact (card_map_of_injective (K := B.map f) (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective).symm.le
  apply le_antisymm
  · rw [commutatorSubgroup, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨b, x, hx, rfl⟩, rfl⟩
    obtain ⟨n, hn'⟩ := mem_powers_iff_mem_zpowers.mpr b.property
    change f (x⁻¹ * b.val x) ∈ (⁅B.map f, zpowers t⁆ : Subgroup E)
    rw [← hn', map_mul, map_inv, hn]
    have hh := commutator_mem_commutator
      ((B.map f).inv_mem (mem_map_of_mem f hx)) (pow_mem (mem_zpowers t) n)
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using hh
  · apply commutator_zpowers_le_of_generator_normalizes (B.map f) _ t ht
    rintro _ ⟨x, hx, rfl⟩
    have hh : x * a x⁻¹ ∈ commutatorSubgroup (zpowers a) D B := by
      simpa only [inv_inv] using
        (Theory.GroupAction.OddCommutatorImage.generator_displacement_mem B a ⟨x⁻¹, B.inv_mem hx⟩)
    have hm := mem_map_of_mem f hh
    simpa only [map_mul, heq, map_inv, mul_inv_rev, inv_inv, commutatorElement_def, mul_assoc] using hm

end Theory.GroupAction.CyclicAuxiliaryIndex
