module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.ConjugateObstruction
public import Theory.Representation.BinaryOffender.PermutationConjugacy
import Mathlib.Tactic

/-!
# Quadratic actors in the actual four-plus-three two-core

The intrinsic two-core of S₄ × S₃ is the Klein four on the first block,
with trivial second coordinate. Its image in the seven-point action has
order four. Two marked double transpositions have nonzero second displacement
on e₀+e₆ in the even-weight core, so this four-group is not quadratic.
Consequently a nontrivial elementary quadratic subgroup of the partition
two-core has rank one, also after conjugating the marked actor.

The module hypothesis is an actual equivariant embedding for the same
seven-point action. No core is replaced by a two-residual, and the calculation
does not use the incompatible printed equality with O₂ of a three-cycle group.
The source assembly must still select the natural quotient and establish the
full partition image before applying these results.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed p.959/PDF p.976 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
open Subgroup Equiv BinaryPermutation Representation.BinaryOffender
namespace FourThreeQuadratic
private abbrev R₄ := Theory.SpecificGroups.SymmetricSix.DuadCalculation.core
private abbrev R₀ : Subgroup FourThree := R₄.prod ⊥

private theorem R₀_card : Nat.card R₀ = 4 := by
  rw [Nat.card_congr (Subgroup.prodEquiv R₄ (⊥ : Subgroup (Perm (Fin 3)))).toEquiv,
    Nat.card_prod, Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card]
  simp

private theorem core_map_le {J B : Type*} [Group J] [Group B]
    (f : J →* B) (hf : Function.Surjective f) : (pCore 2 J).map f ≤ pCore 2 B :=
  le_sSup ⟨(inferInstance : (pCore 2 J).Normal).map f hf, pCore_isPGroup.map f⟩

private theorem product_core : pCore 2 FourThree = R₀ := by
  apply le_antisymm
  · intro x hx
    have h4 := core_map_le (MonoidHom.fst (Perm (Fin 4)) (Perm (Fin 3)))
      (fun y => ⟨(y, 1), rfl⟩) (mem_map_of_mem _ hx)
    have h3 := core_map_le (MonoidHom.snd (Perm (Fin 4)) (Perm (Fin 3)))
      (fun y => ⟨(1, y), rfl⟩) (mem_map_of_mem _ hx)
    have hthree : pCore 2 (Perm (Fin 3)) = ⊥ := by
      have h := ker_eq_twoCore_of_surjective_perm_three
        (MonoidHom.id (Perm (Fin 3))) Function.surjective_id
        (by simp only [MonoidHom.ker_id]; exact IsPGroup.of_subsingleton 2 _)
      simpa only [MonoidHom.ker_id] using h.symm
    constructor
    · change x.1 ∈ R₄
      rw [← Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq] at h4
      exact h4
    · change x.2 ∈ (⊥ : Subgroup (Perm (Fin 3)))
      rwa [hthree] at h3
  · exact le_sSup ⟨inferInstance, IsPGroup.of_card (n := 2) R₀_card⟩

private def R : Subgroup S7 := (pCore 2 fourThreeStabilizer).map fourThreeStabilizer.subtype

private theorem R_eq : R = R₀.map fourThreeHom := by
  unfold R
  rw [← pCore_map_iso 2 fourThreeEquiv, map_map, product_core]
  rfl

private theorem R_card : Nat.card R = 4 := by
  rw [R_eq, Nat.card_congr (R₀.equivMapOfInjective fourThreeHom
    fourThreeHom_injective).symm.toEquiv, R₀_card]

private abbrev a : S7 := fourThreeHom (Equiv.swap 0 1 * Equiv.swap 2 3, 1)
private abbrev b : S7 := fourThreeHom (Equiv.swap 0 2 * Equiv.swap 1 3, 1)
private def v : BinaryPermutation.core (Fin 7) :=
  ⟨![1, 0, 0, 0, 0, 0, 1], by rw [BinaryPermutation.mem_core]; decide⟩

private theorem a_mem : a ∈ R := by
  rw [R_eq]
  exact mem_map_of_mem _ (show (Equiv.swap 0 1 * Equiv.swap 2 3, 1) ∈ R₀ by
    constructor
    · change Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom _ = 1
      decide
    · rfl)
private theorem b_mem : b ∈ R := by
  rw [R_eq]
  exact mem_map_of_mem _ (show (Equiv.swap 0 2 * Equiv.swap 1 3, 1) ∈ R₀ by
    constructor
    · change Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom _ = 1
      decide
    · rfl)

private theorem displacement :
    (coreRepresentation (Fin 7) a (coreRepresentation (Fin 7) b v - v) -
      (coreRepresentation (Fin 7) b v - v)).val 0 = 1 := by decide

variable {J E : Type*} [Group J] [Finite J] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) J E) (φ : J →* S7) (hφ : Function.Injective φ)

include hφ

omit [Finite J] in
/-- A quadratic subgroup in the literal four-plus-three two-core has order at most two.
Only an equivariantly embedded natural core is needed. -/
theorem card_le_two (P A : Subgroup J) (hP : P.map φ = fourThreeStabilizer)
    (hAP : A ≤ (pCore 2 P).map P.subtype)
    (hmodel : HasNaturalSubmodule ρ φ) (hquad : IsQuadratic ρ A) : Nat.card A ≤ 2 := by
  obtain ⟨j, hj, heq⟩ := hmodel
  let e : P ≃* fourThreeStabilizer :=
    (P.equivMapOfInjective φ hφ).trans (MulEquiv.subgroupCongr hP)
  have hAR : A.map φ ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hAP hx
    have hm : e y ∈ pCore 2 fourThreeStabilizer := by
      rw [← pCore_map_iso 2 e]
      exact mem_map_of_mem _ hy
    exact mem_map_of_mem fourThreeStabilizer.subtype hm
  have hcard : Nat.card (A.map φ) = Nat.card A :=
    Nat.card_congr (A.equivMapOfInjective φ hφ).symm.toEquiv
  by_contra! hlarge
  have hdvd : Nat.card (A.map φ) ∣ 4 := R_card ▸ card_dvd_of_le hAR
  have hle : Nat.card (A.map φ) ≤ 4 := Nat.le_of_dvd (by decide) hdvd
  have hc : Nat.card (A.map φ) = 4 := by
    rw [hcard] at hdvd hle ⊢
    have hc : Nat.card A = 3 ∨ Nat.card A = 4 := by omega
    rcases hc with hc | hc
    · rw [hc] at hdvd; norm_num at hdvd
    · exact hc
  have he : A.map φ = R := eq_of_le_of_card_ge hAR (by rw [R_card, hc])
  obtain ⟨x, hx, hxa⟩ := he.symm ▸ a_mem
  obtain ⟨y, hy, hyb⟩ := he.symm ▸ b_mem
  have hq := hquad x hx y hy (j v)
  have hv : coreRepresentation (Fin 7) a (coreRepresentation (Fin 7) b v - v) =
      coreRepresentation (Fin 7) b v - v := by
    apply hj
    rw [← hxa, ← hyb, heq, map_sub, heq]
    exact hq
  have hz := congrArg (fun w : core (Fin 7) => w.val 0) (sub_eq_zero.mpr hv)
  rw [displacement] at hz
  exact one_ne_zero hz

/-- Nontrivial elementary quadratic actors in the actual partition core have rank one. -/
theorem rank_eq_one (P A : Subgroup J) (hP : P.map φ = fourThreeStabilizer)
    (hAP : A ≤ (pCore 2 P).map P.subtype) (hA : IsElementaryTwo A)
    (hmodel : HasNaturalSubmodule ρ φ) (hquad : IsQuadratic ρ A) : rank A = 1 := by
  have hc := card_le_two ρ φ hφ P A hP hAP hmodel hquad
  have hl := Nat.log_monotone (b := 2) hc
  have hp := hA.rank_pos
  change rank A ≤ Nat.log 2 2 at hl
  norm_num at hl
  omega

/-- The same rank calculation for an actual conjugate of the marked actor.
Quadraticity is transported by the representation operator at the conjugator. -/
theorem rank_eq_one_of_conjugate (P A : Subgroup J) (y : J)
    (hP : P.map φ = fourThreeStabilizer)
    (hAP : A.map (MulAut.conj y).toMonoidHom ≤ (pCore 2 P).map P.subtype)
    (hA : IsElementaryTwo A) (hmodel : HasNaturalSubmodule ρ φ)
    (hquad : IsQuadratic ρ A) : rank A = 1 := by
  have hq : IsQuadratic ρ (A.map (MulAut.conj y).toMonoidHom) := by
    have hinv (v : E) : ρ y⁻¹ (ρ y v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hginv (v : E) : ρ y (ρ y⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
    change ρ (y * a * y⁻¹) (ρ (y * b * y⁻¹) v - v) = ρ (y * b * y⁻¹) v - v
    have h := congrArg (ρ y) (hquad a ha b hb (ρ y⁻¹ v))
    simpa only [map_mul, Module.End.mul_apply, map_sub, hinv, hginv] using h
  have hr := rank_eq_one ρ φ hφ P (A.map (MulAut.conj y).toMonoidHom)
    hP hAP (hA.map_conj y) hmodel hq
  rwa [rank_map_conj] at hr

end FourThreeQuadratic
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
