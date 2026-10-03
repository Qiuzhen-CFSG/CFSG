module

public import Theory.GroupTheory.PGroup.HomocyclicFourTorsionCoordinates
public import Theory.ElementaryAbelian.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring

/-!
# The matrix bound for homocyclic actions faithful on four-torsion

An involutory matrix modulo eight which is the identity modulo two has the
form `I + 2M`; its equation `A² = I` implies that `M` modulo two is idempotent.
Normalization is additive on the congruence subgroup, and its kernel is exactly
the matrices which are the identity modulo four. In an additive group of
idempotent binary two-by-two matrices, trace together with the upper-left entry
is injective, giving the bound four.

This module proves that matrix calculation independently of the coordinate
identification for automorphisms of two equal cyclic two-groups. The scalar
congruences modulo eight are finite calculations checked by the Lean kernel.

Source context: the homocyclic case of the MacWilliams–Sah bound, quoted in Janko–Thompson, Math. Z. 113 (1970), 1.1,
printed p.385; see
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace HomocyclicFourTorsion

private abbrev BM := Matrix (Fin 2) (Fin 2) (ZMod 2)

private theorem matrix_zero (M : BM) (h : M * M = M) (ht : Matrix.trace M = 0) (h00 : M 0 0 = 0) :
    M = 0 := by
  have h11 : M 1 1 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two, h00] using ht
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, h00, h11, zero_mul, mul_zero,
    add_zero] at h01 h10
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01.symm
  · exact h10.symm
  · exact h11


/-- An injective homomorphism into the additive binary matrices, all of whose
values are idempotent as matrices, has domain of cardinality at most four. -/
public theorem card_le_four_of_idempotent_binary_matrix_image {G : Type*} [Group G]
    (f : G →* Multiplicative (Matrix (Fin 2) (Fin 2) (ZMod 2))) (hi : Function.Injective f)
    (hp : ∀ g, (f g).toAdd * (f g).toAdd = (f g).toAdd) : Nat.card G ≤ 4 := by
  let t : G →* Multiplicative (ZMod 2 × ZMod 2) :=
    { toFun := fun g => Multiplicative.ofAdd (Matrix.trace (f g).toAdd, (f g).toAdd 0 0)
      map_one' := by simp
      map_mul' := by intro x y; simp [Matrix.trace_add]; rfl }
  have ht : Function.Injective t := by
    apply t.ker_eq_bot_iff.mp
    apply bot_unique
    intro g hg
    have hz : (Matrix.trace (f g).toAdd, (f g).toAdd 0 0) = (0, 0) := hg
    have hf : (f g).toAdd = 0 := matrix_zero _ (hp g)
      (congrArg Prod.fst hz) (congrArg Prod.snd hz)
    change g = 1
    apply hi
    simpa using congrArg Multiplicative.ofAdd hf
  have hc := Nat.card_le_card_of_injective t ht
  simpa [Nat.card_eq_fintype_card] using hc

private def r2 : ZMod 8 →+* ZMod 2 := ZMod.castHom (by decide) _
private def r4 : ZMod 8 →+* ZMod 4 := ZMod.castHom (by decide) _
private def half (x : ZMod 8) : ZMod 2 := (x.val / 2 : ℕ)

set_option maxRecDepth 4096 in
private theorem half_add : ∀ x y : ZMod 8, r2 x = 0 → r2 y = 0 →
    half (x + y) = half x + half y := by decide
set_option maxRecDepth 4096 in
private theorem half_mul : ∀ x y : ZMod 8, r2 x = 0 → r2 y = 0 →
    half (x * y) = 0 := by decide
set_option maxRecDepth 4096 in
private theorem half_diag : ∀ a b c : ZMod 8, r2 a = 0 → r2 b = 0 → r2 c = 0 →
    2*a + a*a + b*c = 0 → half a * half a + half b * half c = half a := by decide
set_option maxRecDepth 4096 in
private theorem half_offdiag : ∀ a b d : ZMod 8, r2 a = 0 → r2 b = 0 → r2 d = 0 →
    2*b + a*b + b*d = 0 → half a * half b + half b * half d = half b := by decide
set_option maxRecDepth 4096 in
private theorem half_zero : ∀ x : ZMod 8, r2 x = 0 → (half x = 0 ↔ r4 x = 0) := by decide

private abbrev M8 := Matrix (Fin 2) (Fin 2) (ZMod 8)
private def halves (N : M8) : BM := N.map half
private def EvenM (N : M8) : Prop := ∀ i j, r2 (N i j) = 0

private theorem even_add (N P : M8) (hn : EvenM N) (hp : EvenM P) : EvenM (N+P) := by
  intro i j
  change r2 (N i j + P i j) = 0
  rw [map_add, hn, hp, add_zero]

private theorem even_mul (N P : M8) (hn : EvenM N) : EvenM (N*P) := by
  intro i j
  simp [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, hn i 0, hn i 1]

private theorem halves_add (N P : M8) (hn : EvenM N) (hp : EvenM P) :
    halves (N+P) = halves N + halves P := by
  ext i j
  exact half_add _ _ (hn i j) (hp i j)

private theorem halves_mul (N P : M8) (hn : EvenM N) (hp : EvenM P) :
    halves (N*P) = 0 := by
  ext i j
  change half ((N*P) i j) = 0
  rw [Matrix.mul_apply, Fin.sum_univ_two, half_add]
  · rw [half_mul _ _ (hn i 0) (hp 0 j), half_mul _ _ (hn i 1) (hp 1 j), add_zero]
  · rw [map_mul, hn, zero_mul]
  · rw [map_mul, hn, zero_mul]

private theorem halves_idempotent (N : M8) (hn : EvenM N) (hs : N + N + N*N = 0) :
    halves N * halves N = halves N := by
  have hs' (i j : Fin 2) := congrFun (congrFun hs i) j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at hs'
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, halves, Matrix.map_apply]
  fin_cases i <;> fin_cases j
  · apply half_diag _ _ _ (hn 0 0) (hn 0 1) (hn 1 0)
    linear_combination hs' 0 0
  · apply half_offdiag _ _ _ (hn 0 0) (hn 0 1) (hn 1 1)
    linear_combination hs' 0 1
  · have he : 2*N 1 0 + N 0 0*N 1 0 + N 1 0*N 1 1 = 0 := by
      linear_combination hs' 1 0
    change half (N 1 0) * half (N 0 0) + half (N 1 1) * half (N 1 0) = half (N 1 0)
    calc
      _ = half (N 0 0) * half (N 1 0) + half (N 1 0) * half (N 1 1) := by ring
      _ = _ := half_offdiag _ _ _ (hn 0 0) (hn 1 0) (hn 1 1) he
  · have he : 2*N 1 1 + N 1 1*N 1 1 + N 0 1*N 1 0 = 0 := by
      linear_combination hs' 1 1
    change half (N 1 0) * half (N 0 1) + half (N 1 1) * half (N 1 1) = half (N 1 1)
    calc
      _ = half (N 1 1) * half (N 1 1) + half (N 0 1) * half (N 1 0) := by ring
      _ = _ := half_diag _ _ _ (hn 1 1) (hn 0 1) (hn 1 0) he

private theorem even_sub_one (A : M8) (hA : A.map r2 = 1) : EvenM (A-1) := by
  change r2.mapMatrix A = 1 at hA
  have hh : (A-1).map r2 = 0 := by
    change r2.mapMatrix (A-1) = 0
    rw [map_sub, hA, map_one, sub_self]
  intro i j
  exact congrFun (congrFun hh i) j

private theorem normalized_mul (A B : M8) (hA : A.map r2 = 1) (hB : B.map r2 = 1) :
    halves (A*B-1) = halves (A-1) + halves (B-1) := by
  have hn := even_sub_one A hA
  have hp := even_sub_one B hB
  have he : A*B-1 = ((A-1)+(B-1))+(A-1)*(B-1) := by noncomm_ring
  rw [he, halves_add _ _ (even_add _ _ hn hp) (even_mul _ _ hn),
    halves_add _ _ hn hp, halves_mul _ _ hn hp, add_zero]

/-- An involutory matrix action modulo eight, trivial modulo two and faithful
modulo four, has domain of cardinality at most four. No separate finiteness
hypothesis on the domain is needed. -/
public theorem card_le_four_of_mod_eight_matrix_action {G : Type*} [Group G]
    (f : G →* Matrix (Fin 2) (Fin 2) (ZMod 8))
    (hfix : ∀ g, (f g).map (ZMod.castHom (show 2 ∣ 8 by decide) (ZMod 2)) = 1)
    (hsq : ∀ g, f g * f g = 1)
    (hfaith : ∀ g,
      (f g).map (ZMod.castHom (show 4 ∣ 8 by decide) (ZMod 4)) = 1 → g = 1) : Nat.card G ≤ 4 := by
  let t : G →* Multiplicative BM :=
    { toFun := fun g => Multiplicative.ofAdd (halves (f g - 1))
      map_one' := by simp [halves, half]
      map_mul' := by
        intro x y
        exact congrArg Multiplicative.ofAdd
          (by rw [map_mul]; exact normalized_mul _ _ (hfix x) (hfix y)) }
  apply card_le_four_of_idempotent_binary_matrix_image t
  · apply t.ker_eq_bot_iff.mp
    apply bot_unique
    intro g hg
    change g = 1
    apply hfaith g
    have ht : halves (f g - 1) = 0 := hg
    have hz : (f g - 1).map r4 = 0 := by
      ext i j
      apply (half_zero _ (even_sub_one _ (hfix g) i j)).mp
      exact congrFun (congrFun ht i) j
    change r4.mapMatrix (f g - 1) = 0 at hz
    rw [map_sub, map_one, sub_eq_zero] at hz
    exact hz
  · intro g
    apply halves_idempotent _ (even_sub_one _ (hfix g))
    calc
      (f g-1)+(f g-1)+(f g-1)*(f g-1) = f g*f g-1 := by noncomm_ring
      _ = 0 := by rw [hsq, sub_self]

end HomocyclicFourTorsion

namespace HomocyclicFourTorsion

/-- The elementary automorphism group of a rank-two homocyclic two-group,
when it is faithful on the four-torsion, has order at most four. -/
public theorem card_le_four_of_homocyclic_elementary_four_torsion
    {D : Type*} [Group D] [Finite D] [IsMulCommutative D]
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (B : Subgroup (MulAut D)) [IsElementaryAbelian 2 B]
    (hfix : ∀ a ∈ B, ∀ d : D, d ^ 2 = 1 → a d = d)
    (hfaith : ∀ a ∈ B, (∀ d : D, d ^ 4 = 1 → a d = d) → a = 1) :
    Nat.card B ≤ 4 := by
  obtain ⟨f, hmod2, hmod4⟩ :=
    exists_mod_eight_matrix_action n hn e B hfix hfaith
  apply card_le_four_of_mod_eight_matrix_action f hmod2
  · intro b
    have hb : b ^ 2 = 1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (b : MulAut D) b.property
    simpa [pow_two] using congrArg f hb
  · exact hmod4

end HomocyclicFourTorsion
