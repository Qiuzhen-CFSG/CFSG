/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/PrimitiveIndexTwoSimplicity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveConjugateGenerators
public import Theory.AtlasPort.OtherSporadic.GroupTheory.IndexTwoInvariantNormals
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Simplicity of the derived subgroup at index two

A primitive conjugacy action and an outside involution make proper normal
subgroups of the derived group split into swapped factors. Their fixed-point
cardinality contradicts the non-square order hypothesis.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/PrimitiveIndexTwoSimplicity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
-/

@[expose] public section

set_option linter.style.haveILetI false

namespace Atlas.GroupTheory
open MulAction

/-- An index-two subgroup is transitive whenever the outside involution fixes
the chosen basepoint of a transitive action. -/
theorem index_two_transitive_of_outside_fixed {J X : Type*} [Group J]
    [MulAction J X] [IsPretransitive J X] (K : Subgroup J) (hi : K.index=2)
    (d : J) (hd : d ∉ K) (hdd : d*d=1) (x : X) (hdx : d • x=x) :
    IsPretransitive K X := by
  apply IsPretransitive.mk
  intro y z
  obtain ⟨g,hg⟩ := exists_smul_eq J x y
  obtain ⟨h,hh⟩ := exists_smul_eq J x z
  obtain ⟨k,hk | hk⟩ := index_two_involution_normal_form K hi d hd hdd g <;>
    obtain ⟨l,hl | hl⟩ := index_two_involution_normal_form K hi d hd hdd h
  all_goals
    have hy : k • x=y := by
      change k.val • x=y
      simpa [hk,mul_smul,hdx] using hg
    have hz : l • x=z := by
      change l.val • x=z
      simpa [hl,mul_smul,hdx] using hh
    refine ⟨l*k⁻¹,?_⟩
    rw [← hy,mul_smul,inv_smul_smul,hz]

/-- For an injective conjugation-equivariant family, the stabilizer of a
label is the fixed subgroup of conjugation by its corresponding element. -/
theorem conjNormal_fixed_iff_stabilizer {J X : Type*} [Group J] [MulAction J X]
    (K : Subgroup J) [K.Normal] (t : X → J) (hinj : Function.Injective t)
    (ht : ∀ g x, t (g • x)=g*t x*g⁻¹) (x : X) (k : K) :
    MulAut.conjNormal (t x) k = k ↔ k • x=x := by
  constructor
  · intro h
    apply hinj
    change t (k.val • x)=t x
    rw [ht]
    have hv := congrArg Subtype.val h
    change t x * k.val * (t x)⁻¹ = k.val at hv
    have hc := (mul_inv_eq_iff_eq_mul).mp hv
    rw [← hc,mul_assoc,mul_inv_cancel,mul_one]
  · intro h
    apply Subtype.ext
    change t x * k.val * (t x)⁻¹ = k.val
    have hv := congrArg t h
    change t (k.val • x)=t x at hv
    rw [ht] at hv
    have hc := (mul_inv_eq_iff_eq_mul).mp hv
    rw [← hc,mul_assoc,mul_inv_cancel,mul_one]

/-- The index-two alternative of the primitive conjugate-involution
simplicity argument, with all structural hypotheses visible. -/
theorem simple_derived_of_primitive_involutions {J X : Type*}
    [Group J] [Finite J] [MulAction J X] [FaithfulSMul J X]
    [IsPreprimitive J X] [Nontrivial (commutator J)]
    (t : X → J) (hinj : Function.Injective t)
    (ht : ∀ g x, t (g • x)=g*t x*g⁻¹)
    (hgen : Subgroup.closure (Set.range t)=⊤) (x : X)
    (hi : (commutator J).index=2) (hout : t x ∉ commutator J)
    (hsq : t x * t x=1)
    (hneq : Nat.card (commutator J) ≠ (Nat.card X)^2) :
    IsSimpleGroup (commutator J) := by
  let K := commutator J
  let a : K ≃* K := MulAut.conjNormal (t x)
  have ha : Function.Involutive a := by
    intro k
    apply Subtype.ext
    change t x * (t x * k.val * (t x)⁻¹) * (t x)⁻¹ = k.val
    have hd : (t x)⁻¹=t x := inv_eq_of_mul_eq_one_left hsq
    rw [hd]
    calc
      t x * (t x * k.val * t x) * t x = (t x*t x)*k.val*(t x*t x) := by simp only [mul_assoc]
      _ = k.val := by rw [hsq]; simp
  have hminJ (L : Subgroup J) (hL : L.Normal) : L=⊥ ∨ K ≤ L := by
    letI := hL
    by_cases hb : L=⊥
    · exact Or.inl hb
    · exact Or.inr (commutator_le_normal_of_primitive_generators t ht hgen x L hb)
  have hmin (H : Subgroup K) (hH : H.Normal) (hh : H.map a.toMonoidHom=H) : H=⊥ ∨ H=⊤ :=
    index_two_invariant_normal_dichotomy K hi (t x) hout hsq hminJ H hH hh
  have hdx : t x • x=x := by
    apply hinj
    rw [ht]
    simp
  letI := index_two_transitive_of_outside_fixed K hi (t x) hout hsq x hdx
  constructor
  intro N hN
  by_cases hb : N=⊥
  · exact Or.inl hb
  by_cases hh : N=⊤
  · exact Or.inr hh
  exfalso
  have hcard := card_eq_sq_fixed_of_normal_factors a ha hmin N hb hh
  have hfix : Nat.card {k : K // a k=k} = Nat.card (stabilizer K x) := by
    apply Nat.card_congr
    exact Equiv.setCongr (Set.ext fun k => conjNormal_fixed_iff_stabilizer K t hinj ht x k)
  rw [hfix] at hcard
  have horbit : Nat.card (orbit K x)=Nat.card X := by
    rw [orbit_eq_univ]
    exact Nat.card_congr (Equiv.Set.univ X)
  have hmul := Nat.card_congr (orbitProdStabilizerEquivGroup K x)
  rw [Nat.card_prod,horbit] at hmul
  have hpos : 0 < Nat.card (stabilizer K x) := Nat.card_pos
  have he : Nat.card X=Nat.card (stabilizer K x) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    simpa [pow_two] using hmul.trans hcard
  exact hneq (hcard.trans (congrArg (fun n : ℕ => n^2) he.symm))

/-- The primitive conjugacy-class index-two criterion without a separately
assumed outside generator: generation and index two force it automatically. -/
theorem simple_derived_of_primitive_involution_class {J X : Type*}
    [Group J] [Finite J] [MulAction J X] [FaithfulSMul J X]
    [IsPreprimitive J X] [Nontrivial (commutator J)]
    (t : X → J) (hinj : Function.Injective t)
    (ht : ∀ g x, t (g • x)=g*t x*g⁻¹)
    (hgen : Subgroup.closure (Set.range t)=⊤) (x : X)
    (hi : (commutator J).index=2) (hsq : t x * t x=1)
    (hneq : Nat.card (commutator J) ≠ (Nat.card X)^2) :
    IsSimpleGroup (commutator J) := by
  have hout : t x ∉ commutator J := by
    intro hm
    have hc : Subgroup.closure (Set.range t) ≤ commutator J := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨y,rfl⟩
      obtain ⟨g,hg⟩ := exists_smul_eq J x y
      rw [← hg,ht]
      exact (inferInstance : (commutator J).Normal).conj_mem _ hm g
    have he : commutator J=⊤ := top_unique (hgen ▸ hc)
    rw [he,Subgroup.index_top] at hi
    exact (by decide : (1 : ℕ) ≠ 2) hi
  exact simple_derived_of_primitive_involutions t hinj ht hgen x hi hout hsq hneq

end Atlas.GroupTheory
