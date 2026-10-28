module

public import Theory.Representation.BinaryPermutation
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!+# The minus quadratic form on the five-point augmentation core

On the even-weight core of the binary permutation module, the sum of all
coordinate products has value zero precisely at weights zero and four.
Consequently two distinct nonzero singular vectors have nonsingular sum:
every nonzero totally singular subgroup is a point. The small coordinate
identities below are checked by the kernel on the 32 binary words.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §B.3 and the orthogonal A₅-module used in
§13.2 and Lemma 13.6.24 (printed p.933).
-/

@[expose] public section

namespace BinaryPermutation.FiveGeometry

/-- The permutation-invariant quadratic polynomial restricted to the core. -/
def form : QuadraticForm (ZMod 2) (core (Fin 5)) :=
  (∑ i : Fin 5, ∑ j : Fin 5 with i < j,
    (QuadraticMap.proj i j : QuadraticForm (ZMod 2) (Full (Fin 5)))).comp
      (core (Fin 5)).subtype

theorem finrank_core : Module.finrank (ZMod 2) (core (Fin 5)) = 4 := by
  simpa using BinaryPermutation.finrank_core (Fin 5)

/-- The nonzero singular vectors are exactly the five weight-four words. -/
theorem singular_iff (x : core (Fin 5)) :
    form x = 0 ↔ x = 0 ∨ (Finset.univ.filter fun i => x.val i ≠ 0).card = 4 := by
  have h : ∀ x : Full (Fin 5), (∑ i, x i) = 0 →
      ((∑ i : Fin 5, ∑ j : Fin 5 with i < j, x i * x j) = 0 ↔
        x = 0 ∨ (Finset.univ.filter fun i => x i ≠ 0).card = 4) := by decide
  change (∑ i : Fin 5, ∑ j : Fin 5 with i < j, x.val i * x.val j) = 0 ↔ _
  simpa only [Subtype.ext_iff, Submodule.coe_zero] using h x.val x.property

/-- This is the Witt-index-one calculation, without assuming a dimension bound. -/
theorem singular_add (x y : core (Fin 5))
    (hx : form x = 0) (hy : form y = 0) (hxy : form (x + y) = 0) :
    x = 0 ∨ y = 0 ∨ x = y := by
  have h : ∀ x y : Full (Fin 5), (∑ i, x i) = 0 → (∑ i, y i) = 0 →
      (∑ i : Fin 5, ∑ j : Fin 5 with i < j, x i * x j) = 0 →
      (∑ i : Fin 5, ∑ j : Fin 5 with i < j, y i * y j) = 0 →
      (∑ i : Fin 5, ∑ j : Fin 5 with i < j, (x + y) i * (x + y) j) = 0 →
      x = 0 ∨ y = 0 ∨ x = y := by decide
  rcases h x.val y.val x.property y.property hx hy hxy with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))

/-- A nontrivial subgroup in genuine core coordinates, all of whose vectors
are singular, has order two. -/
theorem card_eq_two_of_singular
    {G : Type*} [Group G] (V A : Subgroup G) (hAV : A ≤ V)
    (e : V ≃* Multiplicative (core (Fin 5))) (hA : A ≠ ⊥)
    (hsing : ∀ a : A, form (e ⟨a.val, hAV a.property⟩).toAdd = 0) :
    Nat.card A = 2 := by
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  apply (Nat.card_eq_two_iff' (1 : A)).mpr
  refine ⟨a, ha, ?_⟩
  intro b hb
  let f : A →* Multiplicative (core (Fin 5)) := e.toMonoidHom.comp (Subgroup.inclusion hAV)
  have hf : Function.Injective f := e.injective.comp (Subgroup.inclusion_injective hAV)
  have hfa : (f a).toAdd ≠ 0 := by
    intro h
    apply ha
    apply hf
    exact h.trans (map_one f).symm
  have hfb : (f b).toAdd ≠ 0 := by
    intro h
    apply hb
    apply hf
    exact h.trans (map_one f).symm
  have hab : form ((f a).toAdd + (f b).toAdd) = 0 := by
    have h := hsing (a * b)
    change form (f (a * b)).toAdd = 0 at h
    rw [map_mul] at h
    exact h
  have heq := ((singular_add _ _ (hsing a) (hsing b) hab).resolve_left hfa).resolve_left hfb
  exact (hf heq).symm

end BinaryPermutation.FiveGeometry
