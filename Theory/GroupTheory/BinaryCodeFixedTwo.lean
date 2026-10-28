module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Binary codes with at most two trivial coordinates

A faithful binary sign representation in which every nonidentity element is
trivial in at most two coordinates has order at most eight. At order eight,
it contains the sign vector that is nontrivial in every coordinate.

Evaluation on any three coordinates is injective. In the equality case it is
surjective, so lift the three unit vectors. Each lift is nontrivial at every
remaining coordinate; their product is the required vector.

This is the finite combinatorial step in the proof of Aschbacher--Smith,
*The Classification of Quasithin Groups*, Lemma A.1.28, printed p.26. The
representation-theoretic consumer supplies the coordinates and fixed bound.
-/

namespace BinaryCodeFixedTwo

private theorem binary_card : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  simp [Nat.card_eq_fintype_card]

private theorem binary_ne_one (x : Multiplicative (ZMod 2)) (hx : x ≠ 1) :
    x = Multiplicative.ofAdd 1 := by
  change x.toAdd = 1
  change x.toAdd ≠ 0 at hx
  have h : x.toAdd = 0 ∨ x.toAdd = 1 := by
    generalize x.toAdd = y
    fin_cases y
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact h.resolve_left hx

variable {A I : Type*} [Group A] [Finite I]

private theorem three_fixed_eq_one
    (f : A →* (I → Multiplicative (ZMod 2)))
    (hfix : ∀ a : A, a ≠ 1 → Nat.card {i : I // f a i = 1} ≤ 2)
    (a : A) (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : f a i = 1) (hj : f a j = 1) (hk : f a k = 1) : a = 1 := by
  classical
  by_contra ha
  let := Fintype.ofFinite {i : I // f a i = 1}
  have hthree : 2 < Fintype.card {i : I // f a i = 1} := by
    apply Fintype.two_lt_card_iff.mpr
    refine ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩, ?_, ?_, ?_⟩
    · exact fun h => hij (congrArg Subtype.val h)
    · exact fun h => hik (congrArg Subtype.val h)
    · exact fun h => hjk (congrArg Subtype.val h)
  have := hfix a ha
  rw [Nat.card_eq_fintype_card] at this
  omega

private def restrictThree (f : A →* (I → Multiplicative (ZMod 2)))
    (e : Fin 3 ↪ I) : A →* (Fin 3 → Multiplicative (ZMod 2)) where
  toFun a j := f a (e j)
  map_one' := by ext j; simp
  map_mul' a b := by ext j; simp

private theorem restrictThree_injective
    (f : A →* (I → Multiplicative (ZMod 2)))
    (hfix : ∀ a : A, a ≠ 1 → Nat.card {i : I // f a i = 1} ≤ 2)
    (e : Fin 3 ↪ I) : Function.Injective (restrictThree f e) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  apply three_fixed_eq_one f hfix a (e 0) (e 1) (e 2)
  · exact e.injective.ne (by decide)
  · exact e.injective.ne (by decide)
  · exact e.injective.ne (by decide)
  · exact congrFun ha 0
  · exact congrFun ha 1
  · exact congrFun ha 2

/-- A faithful binary code with at most two trivial coordinates per nonidentity
word has order at most eight. -/
public theorem card_le_eight
    (f : A →* (I → Multiplicative (ZMod 2))) (hf : Function.Injective f)
    (hfix : ∀ a : A, a ≠ 1 → Nat.card {i : I // f a i = 1} ≤ 2) :
    Nat.card A ≤ 8 := by
  classical
  let := Fintype.ofFinite I
  by_cases hI : 3 ≤ Fintype.card I
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card (Fin 3) ≤ Fintype.card I by simpa using hI)
    have h := Nat.card_le_card_of_injective _ (restrictThree_injective f hfix e)
    simpa [Nat.card_fun, binary_card] using h
  · have h := Nat.card_le_card_of_injective f hf
    rw [Nat.card_fun, binary_card, Nat.card_eq_fintype_card (α := I)] at h
    have hI' : Fintype.card I ≤ 2 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hI'
    omega

/-- At order eight, the code contains the vector whose every coordinate is the
nonidentity binary sign. -/
public theorem exists_all_nontrivial_of_card_eight
    (f : A →* (I → Multiplicative (ZMod 2))) (hf : Function.Injective f)
    (hfix : ∀ a : A, a ≠ 1 → Nat.card {i : I // f a i = 1} ≤ 2)
    (hA : Nat.card A = 8) :
    ∃ a : A, ∀ i : I, f a i = Multiplicative.ofAdd 1 := by
  classical
  let := Fintype.ofFinite I
  have hI : 3 ≤ Fintype.card I := by
    by_contra hI
    have h := Nat.card_le_card_of_injective f hf
    rw [hA, Nat.card_fun, binary_card, Nat.card_eq_fintype_card] at h
    have hI' : Fintype.card I ≤ 2 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hI'
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 3) ≤ Fintype.card I by simpa using hI)
  have hs : Function.Surjective (restrictThree f e) :=
    ((restrictThree_injective f hfix e).bijective_of_nat_card_le (by
      simp [hA])).2
  have hlift (j : Fin 3) : ∃ a : A,
      ∀ k : Fin 3, f a (e k) = if k = j then Multiplicative.ofAdd 1 else 1 := by
    obtain ⟨a, ha⟩ := hs (fun k => if k = j then Multiplicative.ofAdd 1 else 1)
    exact ⟨a, fun k => congrFun ha k⟩
  let a (j : Fin 3) := Classical.choose (hlift j)
  have ha (j k : Fin 3) :
      f (a j) (e k) = if k = j then Multiplicative.ofAdd 1 else 1 :=
    Classical.choose_spec (hlift j) k
  have ha_ne (j : Fin 3) : a j ≠ 1 := by
    intro hj
    have h := ha j j
    rw [hj] at h
    have h' : (1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd 1 := by
      simpa using h
    exact zero_ne_one (congrArg Multiplicative.toAdd h')
  have houtside (j : Fin 3) (i : I) (hi : ∀ k : Fin 3, e k ≠ i) :
      f (a j) i = Multiplicative.ofAdd 1 := by
    apply binary_ne_one
    intro hzero
    apply ha_ne j
    fin_cases j
    · exact three_fixed_eq_one f hfix _ (e 1) (e 2) i
        (e.injective.ne (by decide)) (hi 1) (hi 2)
        (by simpa using ha 0 1) (by simpa using ha 0 2) hzero
    · exact three_fixed_eq_one f hfix _ (e 0) (e 2) i
        (e.injective.ne (by decide)) (hi 0) (hi 2)
        (by simpa using ha 1 0) (by simpa using ha 1 2) hzero
    · exact three_fixed_eq_one f hfix _ (e 0) (e 1) i
        (e.injective.ne (by decide)) (hi 0) (hi 1)
        (by simpa using ha 2 0) (by simpa using ha 2 1) hzero
  refine ⟨a 0 * a 1 * a 2, ?_⟩
  intro i
  simp only [map_mul, Pi.mul_apply]
  by_cases hi : ∃ k : Fin 3, e k = i
  · obtain ⟨k, rfl⟩ := hi
    rw [ha 0 k, ha 1 k, ha 2 k]
    fin_cases k <;> simp
  · have hi' : ∀ k : Fin 3, e k ≠ i := by simpa using hi
    rw [houtside 0 i hi', houtside 1 i hi', houtside 2 i hi']
    decide

end BinaryCodeFixedTwo
