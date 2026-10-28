module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Regular.Displacement
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Natural fixed spaces of regular elementary eight groups

Regular fixed representatives are affine binary functions: one constant and a
linear functional on the three-dimensional acting group. Their dimension is
four. The sum of all elements of binary three-space is zero, so all these
functions have even weight. Factoring out constants gives fixed dimension
three and codimension three on the actual natural section.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(3), printed pp.83–84.
-/

public section

open BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterB.Offenders
private theorem elementaryEight_finrank (E : Type*) [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hcard : Nat.card E = 8) :
    Module.finrank (ZMod 2) (Additive E) = 3 := by
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive E) = 2 ^ 3 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hsize
    simpa only [Nat.card_zmod, hcard, show (2 : ℕ) ^ 3 = 8 by decide] using hsize.symm
  exact Nat.pow_right_injective (by decide : 1 < 2) hpow

theorem regularEight_displacement_finrank {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) :
    Module.finrank (ZMod 2) (eightDisplacementSpace A) = 4 := by
  classical
  let : IsElementaryAbelian 2 A := hA.1.2
  let e : A ≃ Fin 8 := Equiv.ofBijective (fun a : A => a.val 0)
    (regularEight_eval_bijective hA 0)
  have he (a : A) : e.symm (a.val 0) = a := e.symm_apply_apply a
  have he0 : e.symm 0 = 1 := he 1
  let f₀ : (ZMod 2 × Module.Dual (ZMod 2) (Additive A)) →ₗ[ZMod 2] Full (Fin 8) :=
    { toFun := fun p i => p.1 + p.2 (Additive.ofMul (e.symm i))
      map_add' := by intro p q; ext i; simp; ring
      map_smul' := by intro c p; ext i; simp [mul_add] }
  have hf₀ (p : ZMod 2 × Module.Dual (ZMod 2) (Additive A)) :
      f₀ p ∈ eightDisplacementSpace A := by
    apply (regularEight_displacement_iff_affine hA 0 (f₀ p)).mpr
    refine ⟨p.2.toAddMonoidHom, ?_⟩
    intro a
    change p.1 + p.2 (Additive.ofMul (e.symm (a.val 0))) =
      p.1 + p.2 (Additive.ofMul (e.symm 0)) + p.2 (Additive.ofMul a)
    rw [he, he0]
    simp
  let f := f₀.codRestrict (eightDisplacementSpace A) hf₀
  have hinj : Function.Injective f := by
    intro p q hpq
    have hfun : f₀ p = f₀ q := congrArg Subtype.val hpq
    have hconst : p.1 = q.1 := by
      have := congrFun hfun 0
      simpa [f₀, he0] using this
    apply Prod.ext hconst
    ext a
    have := congrFun hfun (a.toMul.val 0)
    simpa [f₀, he, hconst] using this
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨χ, hχ⟩ := (regularEight_displacement_iff_affine hA 0 v.val).mp v.property
    let φ : Module.Dual (ZMod 2) (Additive A) :=
      { χ with map_smul' := ZMod.map_smul χ }
    refine ⟨(v.val 0, φ), ?_⟩
    apply Subtype.ext
    ext i
    change v.val 0 + χ (Additive.ofMul (e.symm i)) = v.val i
    have hi := hχ (e.symm i)
    have heval : (e.symm i).val 0 = i := e.apply_symm_apply i
    simpa only [heval] using hi.symm
  let ef := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  rw [← ef.finrank_eq, Module.finrank_prod, Module.finrank_self,
    Subspace.dual_finrank_eq, elementaryEight_finrank A hA.2.1]

theorem regularEight_displacement_le_core {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) : eightDisplacementSpace A ≤ core (Fin 8) := by
  classical
  let : IsElementaryAbelian 2 A := hA.1.2
  let : Fintype A := Fintype.ofFinite A
  let e : Additive A ≃ Fin 8 := Equiv.ofBijective (fun a : Additive A => a.toMul.val 0)
    (regularEight_eval_bijective hA 0)
  have hdim := elementaryEight_finrank A hA.2.1
  let coords : Additive A ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    (Module.finBasisOfFinrankEq (ZMod 2) (Additive A) hdim).equivFun
  have hsum : ∑ a : Additive A, a = 0 := by
    apply coords.injective
    rw [map_sum, map_zero]
    rw [← Equiv.sum_comp coords.toEquiv.symm (fun a : Additive A => coords a)]
    change (∑ w : Fin 3 → ZMod 2, coords (coords.symm w)) = 0
    simp only [LinearEquiv.apply_symm_apply]
    decide
  intro v hv
  obtain ⟨χ, hχ⟩ := (regularEight_displacement_iff_affine hA 0 v).mp hv
  rw [mem_core, ← Equiv.sum_comp e v]
  have hv' (a : Additive A) : v (e a) = v 0 + χ a := hχ a.toMul
  simp_rw [hv']
  rw [Finset.sum_add_distrib, ← map_sum, hsum, map_zero, add_zero]
  have hcard : Fintype.card (Additive A) = 8 := by
    simpa [Nat.card_eq_fintype_card] using hA.2.1
  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  rw [show ((8 : ℕ) : ZMod 2) = 0 by decide, zero_mul]

theorem fixedSpace_natural_regularEight_finrank {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) :
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 8)) A) = 3 := by
  have h := eightDisplacementSpace_finrank_eq_natural_add_one A
    (regularEight_displacement_le_core hA)
  rw [regularEight_displacement_finrank hA] at h
  omega

theorem fixedCodim_natural_regularEight {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) :
    fixedCodim (naturalRepresentation (Fin 8)) A = 3 := by
  apply fixedCodim_eq_of_finrank_fixedSpace _ A (d := 6) (k := 3)
  · simpa using finrank_natural_even (Fin 8) (by decide : Even 8)
  · exact fixedSpace_natural_regularEight_finrank hA

end CFSG.Quasithin.ChapterB.Offenders
