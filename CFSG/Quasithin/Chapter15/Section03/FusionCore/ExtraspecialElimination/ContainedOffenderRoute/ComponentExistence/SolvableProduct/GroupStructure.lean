module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.Preparation
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.SymmetricThree
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.NonQuasisimple

/-!
# Projecting the contained actor onto an internal S₃ factor

The compatible product equivalence supplies literal coordinate maps.  The
selected actor is allowed to meet both factors: a nontrivial projection onto
one S₃ factor gives the cubic commutator identity there.  The canonical choice
uses the first factor when that projection is nontrivial and the second factor
otherwise.  This is the product calculation in B.5.6(3), before the moved
rank and ambient orbit calculations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(3),
printed p.105, and proof of 15.3.49(i), printed pp.1143–1144.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct
open ComponentReduction.FactorGeneration.ClassificationCases
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

variable {D : Type*} [Group D] {A B : Subgroup D}

namespace Product
variable (p : InternalProduct A B)

def firstProjection : D →* A := (MonoidHom.fst A B).comp p.equiv.symm.toMonoidHom

def secondProjection : D →* B := (MonoidHom.snd A B).comp p.equiv.symm.toMonoidHom

theorem inverse_first (a : A) : p.equiv.symm (a : D) = (a, 1) := by
  apply p.equiv.injective
  rw [p.equiv.apply_symm_apply, p.apply_eq, coe_one, mul_one]

theorem inverse_second (b : B) : p.equiv.symm (b : D) = (1, b) := by
  apply p.equiv.injective
  rw [p.equiv.apply_symm_apply, p.apply_eq, coe_one, one_mul]

include p in
theorem commute (a : A) (b : B) : Commute (a : D) (b : D) := by
  apply p.equiv.symm.injective
  simp only [map_mul, inverse_first, inverse_second, Prod.mul_def, mul_one, one_mul]

def swap : InternalProduct B A where
  equiv := (MulEquiv.prodComm : B × A ≃* A × B).trans p.equiv
  apply_eq b a := by
    change p.equiv (a, b) = (b : D) * a
    rw [p.apply_eq, (commute p a b).eq]

include p in
theorem first_normal : A.Normal := by
  have he : (secondProjection p).ker = A := by
    ext x
    constructor
    · intro hx
      have hx' : (p.equiv.symm x).2 = 1 := hx
      have he := p.apply_eq (p.equiv.symm x).1 (p.equiv.symm x).2
      rw [p.equiv.apply_symm_apply, hx', coe_one, mul_one] at he
      rw [he]
      exact (p.equiv.symm x).1.property
    · intro hx
      change (p.equiv.symm x).2 = 1
      rw [show p.equiv.symm x = (⟨x, hx⟩, 1) from inverse_first p ⟨x, hx⟩]
  rw [← he]
  infer_instance

theorem commutator_first (r : A) (x : D) :
    ⁅(r : D), x⁆ = ((⁅r, firstProjection p x⁆ : A) : D) := by
  apply p.equiv.symm.injective
  rw [map_commutatorElement, inverse_first, inverse_first]
  ext <;> simp [commutatorElement_def, firstProjection]

private theorem symmetricThree_cubic_identity :
    ∀ a r : Equiv.Perm (Fin 3), a ^ 2 = 1 → a ≠ 1 →
      r ^ 3 = 1 → ⁅r⁻¹, a⁆ = r := by decide +kernel

/-- A nontrivial projection of an elementary actor onto an S₃ factor
suffices for cubic generation; the actor may meet both factors. -/
theorem threeCore_commutator (X : Subgroup D) (hX : IsElementaryTwo X)
    (e : A ≃* Equiv.Perm (Fin 3))
    (hne : ∃ x ∈ X, firstProjection p x ≠ 1) :
    (pCore 3 A).map A.subtype = ⁅(pCore 3 A).map A.subtype, X⁆ := by
  let R := (pCore 3 A).map A.subtype
  let : A.Normal := first_normal p
  have hn : X ≤ normalizer (R : Set D) := by
    have hh : X ≤ normalizer (A : Set D) := by rw [normalizer_eq_top]; exact le_top
    exact hh.trans (normalizer_le_normalizer_characteristic_image A (pCore 3 A))
  apply le_antisymm _ (le_normalizer_iff_commutator_le_left.mp hn)
  obtain ⟨x, hx, hxne⟩ := hne
  let a := firstProjection p x
  let : IsElementaryAbelian 2 X := hX.2
  have ha2 : e a ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, elemPow_eq_one_of_isElementaryAbelian x hx, map_one, map_one]
  have hae : e a ≠ 1 := fun hh => hxne (e.map_eq_one_iff.mp hh)
  rintro y ⟨r, hr, rfl⟩
  have hc : Nat.Coprime (orderOf (e r)) 2 := by
    rw [e.orderOf_eq]
    simpa only [Subgroup.orderOf_mk] using
      (pCore_isPGroup (p := 3) (G := A)).orderOf_coprime
        (by decide : Nat.Coprime 3 2) (⟨r, hr⟩ : pCore 3 A)
  have hr6 : orderOf (e r) ∣ 6 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
      show Nat.factorial 3 = 6 from by decide] using orderOf_dvd_natCard (e r)
  have hr3 : e r ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_mul_left.mp hr6)
  have he : ⁅r⁻¹, a⁆ = r := by
    apply e.injective
    simpa only [map_commutatorElement, map_inv] using
      symmetricThree_cubic_identity (e a) (e r) ha2 hae hr3
  have heD : ⁅(r : D)⁻¹, x⁆ = (r : D) :=
    (commutator_first p r⁻¹ x).trans (congrArg Subtype.val he)
  change (r : D) ∈ ⁅R, X⁆
  rw [← heD]
  exact commutator_mem_commutator (inv_mem (mem_map_of_mem A.subtype hr)) hx

/-- Choose the first factor whenever the actor has a nontrivial first
projection, and the second factor otherwise. -/
noncomputable def chosen (X : Subgroup D) : Subgroup D := by
  classical
  exact if ∃ x ∈ X, firstProjection p x ≠ 1 then A else B

theorem chosen_eq (X : Subgroup D) : chosen p X = A ∨ chosen p X = B := by
  classical
  unfold chosen
  split_ifs <;> simp

noncomputable def chosenModel (X : Subgroup D)
    (eA : A ≃* Equiv.Perm (Fin 3)) (eB : B ≃* Equiv.Perm (Fin 3)) :
    chosen p X ≃* Equiv.Perm (Fin 3) := by
  classical
  by_cases h : ∃ x ∈ X, firstProjection p x ≠ 1
  · exact (MulEquiv.subgroupCongr (show chosen p X = A from if_pos h)).trans eA
  · exact (MulEquiv.subgroupCongr (show chosen p X = B from if_neg h)).trans eB

theorem chosen_normal (X : Subgroup D) : (chosen p X).Normal := by
  rcases chosen_eq p X with h | h
  · rw [h]; exact first_normal p
  · rw [h]; exact first_normal (swap p)

theorem chosen_threeCore_commutator (X : Subgroup D) (hX : IsElementaryTwo X)
    (eA : A ≃* Equiv.Perm (Fin 3)) (eB : B ≃* Equiv.Perm (Fin 3)) :
    (pCore 3 (chosen p X)).map (chosen p X).subtype =
      ⁅(pCore 3 (chosen p X)).map (chosen p X).subtype, X⁆ := by
  classical
  by_cases h : ∃ x ∈ X, firstProjection p x ≠ 1
  · rw [show chosen p X = A from if_pos h]
    exact threeCore_commutator p X hX eA h
  · rw [show chosen p X = B from if_neg h]
    apply threeCore_commutator (swap p) X hX eB
    obtain ⟨x, hx, hxne⟩ : ∃ x ∈ X, x ≠ 1 := by
      by_contra! hh
      exact hX.1 (X.eq_bot_iff_forall.mpr hh)
    refine ⟨x, hx, ?_⟩
    intro hs
    have hf : firstProjection p x = 1 := by
      by_contra hh
      exact h ⟨x, hx, hh⟩
    have hi : p.equiv.symm x = 1 := by
      apply Prod.ext
      · exact hf
      · exact hs
    exact hxne (p.equiv.symm.injective (hi.trans (map_one _).symm))

end Product
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct
