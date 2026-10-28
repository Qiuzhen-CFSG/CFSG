module

public import Theory.Character.ConjClassFunction
public import Mathlib.GroupTheory.Coset.Basic

/-!
# Inflation of irreducible conjugacy-class characters

Pullback along a surjective homomorphism of finite groups preserves character
realizations and the normalized character inner product. Every fiber has the
cardinality of the kernel, so its multiplicity cancels against the group order.
This is the quotient-character transfer used in Brauer, Desarguesian planes II,
p. 128; it requires no centrality assumption on the kernel. The representation
realizing the inflated character is the original representation composed with
the specified homomorphism, on the same standard complex vector space.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

private theorem sum_comp_surjective
    {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    (quotientMap : G →* H) (hsurj : Function.Surjective quotientMap)
    (value : H → ℂ) :
    (∑ source : G, value (quotientMap source)) =
      (Nat.card quotientMap.ker : ℂ) * ∑ target : H, value target := by
  classical
  rw [← Fintype.sum_fiberwise quotientMap (fun source => value (quotientMap source))]
  have hfiber (target : H) :
      Fintype.card {source : G // quotientMap source = target} =
        Nat.card quotientMap.ker := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hsurj target)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro target _
  have hconst (source : {source : G // quotientMap source = target}) :
      value (quotientMap source) = value target := congrArg value source.property
  simp only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hfiber]

/-- Inflation along a surjection preserves the normalized scalar product,
even for functions that are not constant on conjugacy classes. -/
public theorem scalarProduct_comp_surjective
    {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    (quotientMap : G →* H) (hsurj : Function.Surjective quotientMap)
    (phi psi : ClassFunction H) :
    scalarProduct G (fun g => phi (quotientMap g)) (fun g => psi (quotientMap g)) =
      scalarProduct H phi psi := by
  have hcard : (Nat.card G : ℂ) =
      (Nat.card quotientMap.ker : ℂ) * (Nat.card H : ℂ) := by
    simpa [Nat.card_eq_fintype_card] using
      sum_comp_surjective quotientMap hsurj (fun _ => (1 : ℂ))
  have hker : (Nat.card quotientMap.ker : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  unfold scalarProduct
  rw [sum_comp_surjective quotientMap hsurj (fun h => phi h * star (psi h)), hcard,
    mul_inv_rev]
  simp only [mul_assoc, inv_mul_cancel_left₀ hker]

public theorem classFunctionInner_comp_surjective
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotientMap : G →* H) (hsurj : Function.Surjective quotientMap)
    (chi psi : ConjClassFunction H) :
    classFunctionInner (chi ∘ ConjClasses.map quotientMap)
      (psi ∘ ConjClasses.map quotientMap) = classFunctionInner chi psi := by
  have hcard : (Nat.card G : ℂ) =
      (Nat.card quotientMap.ker : ℂ) * (Nat.card H : ℂ) := by
    simpa [Nat.card_eq_fintype_card] using
      sum_comp_surjective quotientMap hsurj (fun _ => (1 : ℂ))
  have hker : (Nat.card quotientMap.ker : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  change (Nat.card G : ℂ)⁻¹ *
      (∑ source : G, chi (ConjClasses.mk (quotientMap source)) *
        star (psi (ConjClasses.mk (quotientMap source)))) = _
  rw [sum_comp_surjective quotientMap hsurj
    (fun target => chi (ConjClasses.mk target) * star (psi (ConjClasses.mk target))), hcard]
  unfold classFunctionInner
  rw [mul_inv_rev]
  simp only [mul_assoc, inv_mul_cancel_left₀ hker]

public theorem isIrreducibleConjCharacter_comp_surjective
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotientMap : G →* H) (hsurj : Function.Surjective quotientMap)
    {chi : ConjClassFunction H} (hchi : IsIrreducibleConjCharacter chi) :
    IsIrreducibleConjCharacter (chi ∘ ConjClasses.map quotientMap) := by
  refine ⟨?_, (classFunctionInner_comp_surjective quotientMap hsurj chi chi).trans hchi.2⟩
  obtain ⟨degree, representation, hrepresentation⟩ := hchi.1
  refine ⟨degree, representation.comp quotientMap, ?_⟩
  rw [hrepresentation]
  funext conjugacyClass
  obtain ⟨source, rfl⟩ := ConjClasses.exists_rep conjugacyClass
  rfl
