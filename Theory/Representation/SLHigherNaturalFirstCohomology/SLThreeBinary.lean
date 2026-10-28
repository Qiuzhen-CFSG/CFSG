module

public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeBinary.Certificate
public import Theory.Representation.FirstCohomologyCyclic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# First cohomology of the binary special-linear natural module

For SL₃(2), the natural first cohomology has dimension one. The explicit
nonprincipal cocycle is constructed and checked against the matrix action in
`SLThreeBinary.Certificate`. The upper bound follows from elementary relations:
the three-index relation identifies spare coordinates within a row, and the
braid relation identifies them after swapping the two indices. Subtracting a
scalar multiple of the exceptional cocycle therefore leaves row-supported
values, which are principal.

A field isomorphism transports the natural action, cocycles, and principal
cocycles semilinearly. This gives the same calculation over every
characteristic-two field of cardinality two.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(4), printed p.408 (PDF p.419).
-/

open Matrix Matrix.SpecialLinearGroup

namespace Representation.OneCohomology.SLHigherNatural.SLThreeBinary

private abbrev C := cocycles (specialLinearNatural (k := ZMod 2) 3)

private lemma column_zero (f : C) (i j : Fin 3) (hij : i ≠ j) (a : ZMod 2) :
    f.val (transvection hij a) j = 0 := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  exact cocycle_off_diagonal f hij hkj hkj.symm hij.symm hki a

private lemma spare_row (f : C) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    f.val (transvection hij 1) k = f.val (transvection hik 1) j := by
  have h := congrArg (fun g => f.val g j) (transvection_chain hij hjk hik (1 : ZMod 2) 1)
  have hf : ∀ g t, f.val (g * t) = specialLinearNatural 3 g (f.val t) + f.val g := f.property
  simp only [one_mul, hf, map_mul, Module.End.mul_apply, action_transvection, Pi.add_apply] at h
  simp only [Pi.single_eq_of_ne hij.symm, Pi.single_eq_same, Pi.single_eq_of_ne hik.symm,
    column_zero f i k hik 1, add_zero] at h
  linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h

private lemma spare_swap (f : C) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    f.val (transvection hij 1) k = f.val (transvection hij.symm 1) k := by
  have hb : ∀ (i j : Fin 3) (hij : i ≠ j),
      SpecialLinearGroup.transvection hij (1 : ZMod 2) * transvection hij.symm 1 * transvection hij 1 =
        transvection hij.symm 1 * transvection hij 1 * transvection hij.symm 1 := by decide +kernel
  have h := congrArg (fun g => f.val g k) (hb i j hij)
  have hf : ∀ g t, f.val (g * t) = specialLinearNatural 3 g (f.val t) + f.val g := f.property
  simp only [hf, map_mul, Module.End.mul_apply, action_transvection, Pi.add_apply,
    Pi.single_eq_of_ne hik.symm, Pi.single_eq_of_ne hjk.symm, add_zero] at h
  linear_combination h

private lemma spare_eq (f : C) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    f.val (transvection hij 1) k = f.val (transvection (show (0 : Fin 3) ≠ 1 by decide) 1) 2 := by
  have h₀ := spare_row f 0 1 2 (by decide) (by decide) (by decide)
  have h₁ := spare_row f 1 0 2 (by decide) (by decide) (by decide)
  have h₂ := spare_row f 2 0 1 (by decide) (by decide) (by decide)
  have h₃ := spare_swap f 0 1 2 (by decide) (by decide) (by decide)
  have h₄ := spare_swap f 0 2 1 (by decide) (by decide) (by decide)
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first | exact False.elim (hij rfl) | exact False.elim (hik rfl) |
      exact False.elim (hjk rfl) | simp_all

/-- Every cocycle is a multiple of the exceptional one plus a principal cocycle. -/
public lemma normal_form (f : cocycles (specialLinearNatural (k := ZMod 2) 3)) :
    ∃ a : ZMod 2, ∃ v : Fin 3 → ZMod 2, f = a • exceptional + principal (specialLinearNatural 3) v := by
  let a := f.val (transvection (show (0 : Fin 3) ≠ 1 by decide) 1) 2
  obtain ⟨v, hv⟩ := exists_principal_of_support (by decide : 3 ≤ 3) (f - a • exceptional) (by
    intro i j hij c
    ext r
    by_cases hri : r = i
    · subst r; simp
    · rw [Pi.single_eq_of_ne hri]
      change f.val (transvection hij c) r - a * exceptional.val (transvection hij c) r = 0
      have hc : c = 0 ∨ c = 1 := by revert c; decide
      rcases hc with rfl | rfl
      · have hz (t : C) : t.val 1 = 0 := by
          have h := t.property 1 1
          simpa using h.symm
        simp [hz]
      · by_cases hrj : r = j
        · subst r
          rw [column_zero f, column_zero exceptional]
          simp
        · rw [spare_eq f i j r hij (Ne.symm hri) (Ne.symm hrj),
            exceptional_spare i j r hij (Ne.symm hri) (Ne.symm hrj)]
          simp [a])
  exact ⟨a, v, by rw [← hv]; module⟩

private lemma finrank_eq_one :
    Module.finrank (ZMod 2) (H1 (specialLinearNatural (k := ZMod 2) 3)) = 1 :=
  finrank_H1_of_cyclicNormalForm _ exceptional exceptional_not_principal normal_form

variable {K : Type*} [Field K] (e : ZMod 2 ≃+* K)

local instance : RingHomInvPair (e : ZMod 2 →+* K) (e.symm : K →+* ZMod 2) :=
  RingHomInvPair.of_ringEquiv e
local instance : RingHomInvPair (e.symm : K →+* ZMod 2) (e : ZMod 2 →+* K) :=
  RingHomInvPair.of_ringEquiv_symm e

private noncomputable def groupEquiv :
    SpecialLinearGroup (Fin 3) (ZMod 2) ≃* SpecialLinearGroup (Fin 3) K where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by
    apply Subtype.ext
    ext i j
    exact e.symm_apply_apply (g i j)
  right_inv g := by
    apply Subtype.ext
    ext i j
    exact e.apply_symm_apply (g i j)
  map_mul' := (Matrix.SpecialLinearGroup.map e.toRingHom).map_mul

private noncomputable def vectorEquiv : (Fin 3 → ZMod 2) ≃ₛₗ[(e : ZMod 2 →+* K)] (Fin 3 → K) where
  toFun v := fun i => e (v i)
  invFun v := fun i => e.symm (v i)
  left_inv v := by ext i; exact e.symm_apply_apply (v i)
  right_inv v := by ext i; exact e.apply_symm_apply (v i)
  map_add' v w := by ext i; exact e.map_add (v i) (w i)
  map_smul' r v := by ext i; exact e.map_mul r (v i)

private lemma intertwine (g : SpecialLinearGroup (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    vectorEquiv e (specialLinearNatural 3 g v) =
      specialLinearNatural 3 (groupEquiv e g) (vectorEquiv e v) := by
  ext i
  change e (∑ j, g i j * v j) = ∑ j, e (g i j) * e (v j)
  simp only [map_sum, map_mul]

private noncomputable def fieldCocycleEquiv :
    cocycles (specialLinearNatural (k := ZMod 2) 3) ≃ₛₗ[(e : ZMod 2 →+* K)]
      cocycles (specialLinearNatural (k := K) 3) where
  toFun f := ⟨fun h => vectorEquiv e (f.val ((groupEquiv e).symm h)), by
    intro g h
    dsimp only
    rw [map_mul, f.property, map_add, intertwine, (groupEquiv e).apply_symm_apply]⟩
  invFun f := ⟨fun g => (vectorEquiv e).symm (f.val (groupEquiv e g)), by
    intro g h
    apply (vectorEquiv e).injective
    simp only [map_add, LinearEquiv.apply_symm_apply, intertwine]
    rw [map_mul]
    exact f.property _ _⟩
  left_inv f := by ext g; simp
  right_inv f := by ext g; simp
  map_add' f t := by
    apply Subtype.ext
    funext g
    exact (vectorEquiv e).map_add _ _
  map_smul' r f := by
    apply Subtype.ext
    funext g
    exact (vectorEquiv e).map_smulₛₗ r _

private lemma fieldCocycleEquiv_principal (v : Fin 3 → ZMod 2) :
    fieldCocycleEquiv e (principal (specialLinearNatural (k := ZMod 2) 3) v) =
      principal (specialLinearNatural (k := K) 3) (vectorEquiv e v) := by
  apply Subtype.ext
  funext h
  change vectorEquiv e (specialLinearNatural 3 ((groupEquiv e).symm h) v - v) =
    specialLinearNatural 3 h (vectorEquiv e v) - vectorEquiv e v
  rw [map_sub, intertwine, (groupEquiv e).apply_symm_apply]

include e in
/-- A field isomorphism transports the binary natural cohomology calculation. -/
public theorem finrank_eq_one_of_ringEquiv :
    Module.finrank K (H1 (specialLinearNatural (k := K) 3)) = 1 := by
  apply finrank_H1_of_cyclicNormalForm _ (fieldCocycleEquiv e exceptional)
  · rintro ⟨v, hv⟩
    apply exceptional_not_principal
    refine ⟨(vectorEquiv e).symm v, (fieldCocycleEquiv e).injective ?_⟩
    rw [fieldCocycleEquiv_principal, LinearEquiv.apply_symm_apply, hv]
  · intro f
    obtain ⟨a, v, hv⟩ := normal_form ((fieldCocycleEquiv e).symm f)
    refine ⟨e a, vectorEquiv e v, ?_⟩
    have h := congrArg (fieldCocycleEquiv e) hv
    simpa only [LinearEquiv.apply_symm_apply, map_add, LinearEquiv.map_smulₛₗ,
      fieldCocycleEquiv_principal, RingEquiv.coe_toRingHom] using h

private lemma finrank_eq_one_of_card_two [CharP K 2] (hcard : Nat.card K = 2) :
    Module.finrank K (H1 (specialLinearNatural (k := K) 3)) = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite K
  apply finrank_eq_one_of_ringEquiv
    (ZMod.ringEquiv K (by simpa [Nat.card_eq_fintype_card] using hcard))

end Representation.OneCohomology.SLHigherNatural.SLThreeBinary

namespace Representation.OneCohomology.SLHigherNatural

/-- The exceptional binary natural first cohomology has dimension one. -/
public theorem finrank_H1_sl3_two :
    Module.finrank (ZMod 2) (H1 (specialLinearNatural (k := ZMod 2) 3)) = 1 :=
  SLThreeBinary.finrank_eq_one

/-- The natural first cohomology has dimension one over any two-element
characteristic-two field. -/
public theorem finrank_H1_sl3_card_two {K : Type*} [Field K] [CharP K 2]
    (hcard : Nat.card K = 2) :
    Module.finrank K (H1 (specialLinearNatural (k := K) 3)) = 1 :=
  SLThreeBinary.finrank_eq_one_of_card_two hcard

end Representation.OneCohomology.SLHigherNatural
