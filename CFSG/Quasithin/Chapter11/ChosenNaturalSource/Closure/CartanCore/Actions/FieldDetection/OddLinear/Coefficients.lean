module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Sylow
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Faithful restriction to the odd-degree coefficient subfield

Take the fixed field of a Sylow two-subgroup of the finite-field Galois
group. Galois correspondence identifies its degree with that Sylow
subgroup's odd index. All coefficient automorphisms preserve this literal
subfield. The kernel of restriction lies in the chosen two-subgroup, so
restriction is injective on every odd-order actor subgroup. Its order
therefore divides the odd subfield degree, and a nonidentity odd actor
remains nonidentity. The tower formula gives the source decomposition
k = 2^a m.

These are coefficient statements, not a classification of components or
a construction of normalizer lifts. `Sections` applies them to the original
I/O₂(I) torus and the original Cartan actor. Source: Aschbacher--Smith,
11.5.6(3), printed p.781. This campaign-specific extension is kept beside
its consumer to avoid changing the shared finite-field foundation.
-/

@[expose] public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

/-- Prime-field linearization of the actual coefficient automorphisms. -/
def primeAutEquiv (F : BinaryField) :
    (F.Carrier ≃+* F.Carrier) ≃* (F.Carrier ≃ₐ[ZMod 2] F.Carrier) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ) (fun x =>
    DFunLike.congr_fun (RingHom.ext_zmod
      (σ.toRingHom.comp (algebraMap (ZMod 2) F.Carrier))
      (algebraMap (ZMod 2) F.Carrier)) x)
  invFun σ := σ.toRingEquiv
  left_inv σ := by ext x; rfl
  right_inv σ := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

/-- A Sylow two-subgroup of the full coefficient Galois group. -/
def fieldTwoSylow (F : BinaryField) : Sylow 2 (F.Carrier ≃ₐ[ZMod 2] F.Carrier) :=
  Classical.choice inferInstance

/-- The literal fixed subfield, retained with its inclusion in F. -/
def oddSubfield (F : BinaryField) : IntermediateField (ZMod 2) F.Carrier :=
  IntermediateField.fixedField (fieldTwoSylow F : Subgroup _)

/-- The subfield degree is the odd index of a Sylow two-subgroup. -/
theorem oddSubfield_degree_odd (F : BinaryField) :
    Odd (Module.finrank (ZMod 2) (oddSubfield F)) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index,
    oddSubfield, IntermediateField.fixingSubgroup_fixedField]
  exact Nat.not_even_iff_odd.mp (fun h =>
    (fieldTwoSylow F).not_dvd_index (even_iff_two_dvd.mp h))

/-- Bundle the constructed subfield without replacing its carrier. -/
def oddField (F : BinaryField) : BinaryField where
  Carrier := oddSubfield F
  binaryAlgebra := inferInstanceAs (Algebra (ZMod 2) (oddSubfield F))
  degree := Module.finrank (ZMod 2) (oddSubfield F)
  degree_pos := Module.finrank_pos
  card_eq := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := oddSubfield F))

/-- The original subfield inclusion. -/
def oddInclusion (F : BinaryField) : (oddField F).Carrier →+* F.Carrier :=
  (oddSubfield F).subtype

/-- Every coefficient automorphism preserves the chosen subfield. -/
theorem oddSubfield_preserved (F : BinaryField)
    (σ : F.Carrier ≃+* F.Carrier) (x : oddSubfield F) :
    σ x.val ∈ oddSubfield F := by
  let := IsCyclic.commGroup (α := F.Carrier ≃ₐ[ZMod 2] F.Carrier)
  apply (IntermediateField.mem_fixedField_iff _ _).mpr
  intro τ hτ
  have he := congrArg (fun a : F.Carrier ≃ₐ[ZMod 2] F.Carrier => a x.val)
    (mul_comm τ (primeAutEquiv F σ))
  change τ (σ x.val) = σ (τ x.val) at he
  rw [he, (IntermediateField.mem_fixedField_iff _ _).mp x.property τ hτ]

/-- Restriction of the original field action to the actual subfield. -/
def oddRestriction (F : BinaryField) :
    (F.Carrier ≃+* F.Carrier) →* ((oddField F).Carrier ≃+* (oddField F).Carrier) where
  toFun σ := {
    toFun x := ⟨σ x.val, oddSubfield_preserved F σ x⟩
    invFun x := ⟨σ.symm x.val, oddSubfield_preserved F σ.symm x⟩
    left_inv x := Subtype.ext (σ.symm_apply_apply x.val)
    right_inv x := Subtype.ext (σ.apply_symm_apply x.val)
    map_mul' x y := Subtype.ext (map_mul σ x.val y.val)
    map_add' x y := Subtype.ext (map_add σ x.val y.val) }
  map_one' := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

/-- Restriction commutes with the literal inclusion. -/
theorem oddRestriction_apply (F : BinaryField) (σ : F.Carrier ≃+* F.Carrier)
    (x : (oddField F).Carrier) :
    oddInclusion F (oddRestriction F σ x) = σ (oddInclusion F x) :=
  rfl

/-- No nontrivial odd-order coefficient subgroup is lost on restriction. -/
theorem oddRestriction_injective (F : BinaryField)
    (A : Subgroup (F.Carrier ≃+* F.Carrier)) (hA : Odd (Nat.card A)) :
    Function.Injective ((oddRestriction F).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro σ hσ
  apply mem_bot.mpr
  apply Subtype.ext
  apply (primeAutEquiv F).injective
  change primeAutEquiv F σ.val = primeAutEquiv F 1
  rw [map_one]
  have hfix : primeAutEquiv F σ.val ∈ (oddSubfield F).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have he := oddRestriction_apply F σ.val ⟨x, hx⟩
    change oddRestriction F σ.val = 1 at hσ
    rw [hσ] at he
    exact he.symm
  have hS : primeAutEquiv F σ.val ∈ (fieldTwoSylow F : Subgroup _) := by
    simpa only [oddSubfield, IntermediateField.fixingSubgroup_fixedField] using hfix
  have ho : Odd (orderOf (primeAutEquiv F σ.val)) := by
    rw [MulEquiv.orderOf_eq]
    exact hA.of_dvd_nat (A.orderOf_dvd_natCard σ.property)
  obtain ⟨k, hk⟩ := (fieldTwoSylow F).isPGroup'.exists_pow_pow_eq_one
    ⟨primeAutEquiv F σ.val, hS⟩
  have hp : (primeAutEquiv F σ.val) ^ (2 ^ k) = 1 :=
    congrArg Subtype.val hk
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (ho.coprime_two_right.pow_right k) dvd_rfl (orderOf_dvd_of_pow_eq_one hp))

/-- In particular, the source moving actor still moves the subfield. -/
theorem oddRestriction_ne_one (F : BinaryField)
    (σ : F.Carrier ≃+* F.Carrier) (ho : Odd (orderOf σ)) (hne : σ ≠ 1) :
    oddRestriction F σ ≠ 1 := by
  have hinj := oddRestriction_injective F (zpowers σ) (by rwa [Nat.card_zpowers])
  intro h
  have he : (⟨σ, mem_zpowers σ⟩ : zpowers σ) = 1 :=
    hinj (by simpa using h)
  exact hne (congrArg Subtype.val he)

/-- The order of the actual odd actor subgroup divides the subfield degree. -/
theorem odd_actor_card_dvd (F : BinaryField)
    (A : Subgroup (F.Carrier ≃+* F.Carrier)) (hA : Odd (Nat.card A)) :
    Nat.card A ∣ (oddField F).degree := by
  have hd := ((oddRestriction F).comp A.subtype).range.card_subgroup_dvd_card
  rw [← Nat.card_congr (MonoidHom.ofInjective (oddRestriction_injective F A hA)).toEquiv,
    FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two (oddField F).card_eq] at hd
  exact hd

/-- The original degree has the required two-power times odd-degree form. -/
theorem degree_eq_two_pow_mul_odd_degree (F : BinaryField) :
    ∃ a : ℕ, F.degree = 2 ^ a * (oddField F).degree := by
  obtain ⟨a, ha⟩ := (fieldTwoSylow F).isPGroup'.exists_card_eq
  have hF : Module.finrank (ZMod 2) F.Carrier = F.degree := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
    simpa only [F.card_eq, ZMod.card, Nat.card_eq_fintype_card] using hh.symm
  refine ⟨a, ?_⟩
  rw [← hF, ← Module.finrank_mul_finrank (ZMod 2) (oddSubfield F) F.Carrier]
  rw [oddSubfield, IntermediateField.finrank_fixedField_eq_card, ha]
  exact Nat.mul_comm _ _

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
