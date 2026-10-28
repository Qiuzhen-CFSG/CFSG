module

public import Theory.Representation.G2.TensorClassification.SimpleDistinct
public import Theory.Representation.EndFieldFrobenius
public import Mathlib.Data.List.Rotate

/-!
# Coefficient Frobenius rotates the concrete G₂ tensor word

The actual restricted factors identify coefficient Frobenius with the field
Frobenius action. Trace multiplicativity then gives the character of each
consecutive tensor. The finite-field identity `x^(2^n) = x` closes the last
factor back to the first. Thus left rotation cancels coefficient Frobenius;
irreducible character rigidity supplies a genuine intertwiner to the right
rotation. Distinctness of the actual tensor words identifies the stabilizers.

The period criterion is also stated for the periodic degree word and transported
through an arbitrary tensor-model intertwiner. These are inputs to Schur-field
descent, which is not repeated here. All words, including the trivial word and
boundary weights, are included.

Source: GLS3, 2.8.6 and Remark 2.8.8, used in Aschbacher--Smith G.9.3(10),
printed pp.354,356--357. The trace/rotation argument follows the analogous
checked SL₃ calculation in `BinaryDefiningFactors.FrobeniusPeriod`.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace Atlas.G2.TensorClassification
open Restricted
variable (F : Type*) [Field F] [CharP F 2] [Finite F]

private theorem factor_character (r : ℕ) (a : Factor) (g : Model F) :
    (factorRep F r a).character g = (Restricted.action F a).character g ^ (2 ^ r) := by
  have h := Representation.character_semilinearConjugate
    (iterateFrobeniusEquiv F 2 r) (Restricted.action F a)
    (Restricted.coefficientEquiv F a (iterateFrobeniusEquiv F 2 r)) g
  rw [Restricted.frobeniusConjugate_eq] at h
  exact h

private theorem word_character_cons (r : ℕ) (a : Factor) (w : List Factor) (g : Model F) :
    (wordRep F r (a :: w)).character g =
      (factorRep F r a).character g * (wordRep F (r + 1) w).character g :=
  congrFun (Representation.char_tensor (factorRep F r a) (wordRep F (r + 1) w)) g

private theorem word_character_shift (r : ℕ) (w : List Factor) (g : Model F) :
    (wordRep F r w).character g = (wordRep F 0 w).character g ^ (2 ^ r) := by
  induction w generalizing r with
  | nil =>
    change LinearMap.trace F F (1 : Module.End F F) =
      LinearMap.trace F F (1 : Module.End F F) ^ (2 ^ r)
    simp
  | cons a w ih =>
    simp only [word_character_cons, factor_character, Nat.zero_add,
      ih (r + 1), ih 1, pow_zero, pow_one, mul_pow, ← pow_mul]
    rw [pow_succ, Nat.mul_comm (2 ^ r) 2]

variable (K : Type*) [Field K] [Algebra F K]

private abbrev scalarWord (w : List Factor) :=
  Representation.extendScalars K (wordRep F 0 w)

private theorem scalarWord_character (w : List Factor) (g : Model F) :
    (scalarWord F K w).character g = algebraMap F K ((wordRep F 0 w).character g) :=
  LinearMap.trace_baseChange _ _

private theorem scalarWord_character_nil (g : Model F) :
    (scalarWord F K []).character g = 1 := by
  rw [scalarWord_character]
  change algebraMap F K (LinearMap.trace F F (1 : Module.End F F)) = 1
  simp

private theorem scalarWord_character_cons (a : Factor) (w : List Factor) (g : Model F) :
    (scalarWord F K (a :: w)).character g =
      algebraMap F K ((Restricted.action F a).character g) *
        (scalarWord F K w).character g ^ 2 := by
  simp only [scalarWord_character, word_character_cons, Nat.zero_add,
    factor_character, word_character_shift F 1, pow_zero, pow_one, map_mul, map_pow]

private theorem scalarWord_character_append (w : List Factor) (a : Factor) (g : Model F) :
    (scalarWord F K (w ++ [a])).character g =
      (scalarWord F K w).character g *
        algebraMap F K ((Restricted.action F a).character g) ^ (2 ^ w.length) := by
  induction w with
  | nil => simp [scalarWord_character_cons, scalarWord_character_nil]
  | cons b w ih =>
    simp only [List.cons_append, scalarWord_character_cons, ih, mul_pow,
      List.length_cons, pow_succ, pow_mul]
    ring

private theorem scalarWord_character_rotate_one (w : List Factor)
    (hF : Nat.card F = 2 ^ w.length) (g : Model F) :
    (scalarWord F K (w.rotate 1)).character g ^ 2 = (scalarWord F K w).character g := by
  cases w with
  | nil =>
    have hr := congrArg (fun v => (scalarWord F K v).character g) (List.rotate_nil 1 (α := Factor))
    rw [hr, scalarWord_character_nil, one_pow]
  | cons a w =>
    change Nat.card F = 2 ^ (w.length + 1) at hF
    have hp : algebraMap F K ((Restricted.action F a).character g) ^
        (2 ^ (w.length + 1)) = algebraMap F K ((Restricted.action F a).character g) := by
      rw [← map_pow, ← hF]
      congr 1
      let := Fintype.ofFinite F
      simpa only [Nat.card_eq_fintype_card] using
        FiniteField.pow_card ((Restricted.action F a).character g)
    rw [List.rotate_cons_succ, List.rotate_zero, scalarWord_character_append,
      mul_pow, ← pow_mul, ← pow_succ, hp, scalarWord_character_cons, mul_comm]

private theorem scalarWord_character_rotate (w : List Factor)
    (hF : Nat.card F = 2 ^ w.length) (r : ℕ) (g : Model F) :
    (scalarWord F K (w.rotate r)).character g ^ (2 ^ r) =
      (scalarWord F K w).character g := by
  induction r with
  | zero =>
    rw [pow_zero, pow_one]
    exact congrArg (fun v => (scalarWord F K v).character g) (List.rotate_zero w)
  | succ r ih =>
    rw [pow_succ, mul_comm (2 ^ r), pow_mul, ← List.rotate_rotate]
    rw [scalarWord_character_rotate_one F K _ (by simpa using hF), ih]

/-- Left rotation of a length-`n` restricted word. Coefficient Frobenius
rotates in the opposite direction. -/
@[expose] def rotateWord {n : ℕ} (w : Fin n → Factor) (r : ℕ) : Fin n → Factor :=
  fun i => ((List.ofFn w).rotate r).get (Fin.cast (by simp) i)

@[simp] theorem ofFn_rotateWord {n : ℕ} (w : Fin n → Factor) (r : ℕ) :
    List.ofFn (rotateWord w r) = (List.ofFn w).rotate r := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [rotateWord]

variable [IsAlgClosed K] [CharP K 2]

/-- The actual coefficient twist is equivalent to the right-rotated tensor.
Wraparound is supplied by the finite-field action and its coefficient trace. -/
theorem tensorRep_frobenius_equiv_rotate {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (w : Fin n → Factor) (r : ℕ) :
    Nonempty ((Representation.frobeniusConjugate 2 r (tensorRep F K w)).Equiv
      (tensorRep F K (rotateWord w (n - r % n)))) := by
  let : Representation.IsIrreducible (tensorRep F K w) := tensorRep_irreducible hF w
  let : Representation.IsIrreducible
      (Representation.frobeniusConjugate 2 r (tensorRep F K w)) :=
    Representation.frobeniusConjugate_isIrreducible 2 r _
  let : Representation.IsIrreducible (tensorRep F K (rotateWord w (n - r % n))) :=
    tensorRep_irreducible hF _
  apply (Representation.character_eq_iff_equiv_of_irreducible _ _).mp
  funext g
  rw [Representation.character_frobeniusConjugate]
  change (scalarWord F K (List.ofFn w)).character g ^ (2 ^ r) =
    (scalarWord F K (List.ofFn (rotateWord w (n - r % n)))).character g
  have hr : ((List.ofFn w).rotate (n - r % n)).rotate r = List.ofFn w := by
    apply List.rotate_eq_iff.mpr
    simp only [List.length_ofFn]
  have h := scalarWord_character_rotate F K ((List.ofFn w).rotate (n - r % n))
    (by simpa using hF) r g
  have hh := congrArg (fun v => (scalarWord F K v).character g ^ (2 ^ r)) hr
  have he := congrArg (fun v => (scalarWord F K v).character g)
    (ofFn_rotateWord w (n - r % n))
  exact hh.symm.trans (h.trans he.symm)

/-- Equivalence to the `r`th coefficient twist is exactly invariance of the
actual restricted word under rotation by `r`. -/
theorem tensorRep_frobenius_equiv_iff_rotate {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (w : Fin n → Factor) (r : ℕ) :
    Nonempty ((tensorRep F K w).Equiv
      (Representation.frobeniusConjugate 2 r (tensorRep F K w))) ↔
        (List.ofFn w).rotate r = List.ofFn w := by
  obtain ⟨e⟩ := tensorRep_frobenius_equiv_rotate F K hF w r
  constructor
  · rintro ⟨f⟩
    have hw := tensorRep_equiv_imp_eq hF ⟨f.trans e⟩
    apply List.rotate_eq_iff.mpr
    have hl := congrArg List.ofFn hw
    simpa only [ofFn_rotateWord, List.length_ofFn] using hl
  · intro h
    have hr : w = rotateWord w (n - r % n) := by
      apply List.ofFn_injective
      simpa only [ofFn_rotateWord, List.length_ofFn] using List.rotate_eq_iff.mp h
    have he : Nonempty ((tensorRep F K w).Equiv
        (tensorRep F K (rotateWord w (n - r % n)))) := by
      rw [← hr]
      exact ⟨Representation.Equiv.refl _⟩
    exact he.map (fun f => f.trans e.symm)

/-- A word, extended periodically to the natural numbers. -/
@[expose] def periodicWord {n : ℕ} (hn : 0 < n) (w : Fin n → Factor) (i : ℕ) : Factor :=
  w ⟨i % n, Nat.mod_lt _ hn⟩

/-- The full word length is a period of the actual letters. -/
theorem periodicWord_period {n : ℕ} (hn : 0 < n) (w : Fin n → Factor) (i : ℕ) :
    periodicWord hn w (i + n) = periodicWord hn w i := by
  simp [periodicWord]

private theorem rotate_eq_iff_periodicWord {n : ℕ} (hn : 0 < n)
    (w : Fin n → Factor) (r : ℕ) :
    (List.ofFn w).rotate r = List.ofFn w ↔
      ∀ i, periodicWord hn w (i + r) = periodicWord hn w i := by
  constructor
  · intro h i
    have he := congrArg (fun l : List Factor => l[i % n]?) h
    have hi : i % n < (List.ofFn w).length := by simp [Nat.mod_lt _ hn]
    have hi' : i % n < ((List.ofFn w).rotate r).length := by simpa using hi
    rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi,
      Option.some.injEq, List.getElem_rotate] at he
    simpa [periodicWord, Nat.mod_add_mod] using he
  · intro h
    apply List.ext_getElem
    · simp
    · intro i hi hj
      rw [List.getElem_rotate]
      have hin : i < n := by simpa using hj
      simpa [periodicWord, Nat.mod_eq_of_lt hin] using h i

/-- The coefficient-Frobenius stabilizer is exactly the period set of the
periodic restricted word, in the form consumed by Schur-field descent. -/
theorem tensorRep_frobenius_equiv_iff_period {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 0 < n) (w : Fin n → Factor) (r : ℕ) :
    Nonempty ((tensorRep F K w).Equiv
      (Representation.frobeniusConjugate 2 r (tensorRep F K w))) ↔
        ∀ i, periodicWord hn w (i + r) = periodicWord hn w i :=
  (tensorRep_frobenius_equiv_iff_rotate F K hF w r).trans
    (rotate_eq_iff_periodicWord hn w r)

/-- Factor dimensions distinguish the four letters, so the same exact period
criterion holds for the degree word used in the binary dimension descent. -/
theorem tensorRep_frobenius_equiv_iff_degree_period {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 0 < n) (w : Fin n → Factor) (r : ℕ) :
    Nonempty ((tensorRep F K w).Equiv
      (Representation.frobeniusConjugate 2 r (tensorRep F K w))) ↔
        ∀ i, (periodicWord hn w (i + r)).dimension = (periodicWord hn w i).dimension := by
  rw [tensorRep_frobenius_equiv_iff_period F K hF hn w r]
  exact forall_congr' (fun _ => Restricted.Factor.dimension_injective.eq_iff.symm)

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

private def twistEquiv {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    {ρ : Representation K (Model F) V} {τ : Representation K (Model F) W}
    (e : ρ.Equiv τ) (r : ℕ) :
    (Representation.frobeniusConjugate 2 r ρ).Equiv
      (Representation.frobeniusConjugate 2 r τ) := by
  let a := Representation.frobeniusSemilinearEquiv (K := K) (W := V) 2 r
  let b := Representation.frobeniusSemilinearEquiv (K := K) (W := W) 2 r
  let l : V ≃ₗ[K] W := (a.symm.trans e.toLinearEquiv).trans b
  refine .mk l ?_
  intro g
  ext v
  change b (e (a.symm (a (ρ g (a.symm v))))) =
    b (τ g (b.symm (b (e (a.symm v)))))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact congrArg b (LinearMap.congr_fun (e.isIntertwining' g) (a.symm v))

/-- Periodicity transfers through the actual tensor-model intertwiner, for
arbitrary-universe carriers. This is the input to the existing Schur descent. -/
theorem tensorModel_frobenius_equiv_iff_degree_period {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 0 < n) (w : Fin n → Factor)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ρ : Representation K (Model F) V} (e : ρ.Equiv (tensorRep F K w)) (r : ℕ) :
    Nonempty (ρ.Equiv (Representation.frobeniusConjugate 2 r ρ)) ↔
      ∀ i, (periodicWord hn w (i + r)).dimension = (periodicWord hn w i).dimension := by
  rw [← tensorRep_frobenius_equiv_iff_degree_period F K hF hn w r]
  let t := twistEquiv F K e r
  constructor
  · rintro ⟨f⟩
    exact ⟨e.symm.trans (f.trans t)⟩
  · rintro ⟨f⟩
    exact ⟨e.trans (f.trans t.symm)⟩

end Atlas.G2.TensorClassification

end
