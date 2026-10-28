module

public import Theory.Representation.G2.RestrictedModules
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.List.OfFn
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Concrete Frobenius tensor words for G₂ in characteristic two

The letters are the four actual restricted factors, with dimensions 1, 6, 14
and 64. At position `i` the group action is pulled back along the `i`th actual
finite-field Frobenius. We tensor over the finite field and then extend scalars;
`scalarWordConsEquiv` identifies every step with the tensor of the extended
factors. The empty word is the trivial line.

The dimension formula follows by tensor induction and base change. Tensor-unit
intertwiners remove trivial letters and identify a word with one natural letter
with the genuine trace-zero octonion quotient action, with the field twist at
that position. Finite-field wraparound follows from `x^(2^n) = x`, hence holds
for the actual action before passing to representation equivalence.

These constructions do not assert tensor irreducibility, distinctness or
exhaustion. Those mathematical obligations are separate from the construction.
Source: GLS3, 2.8.3, 2.8.6(a), 2.8.8 and 2.8.10(g), used in Aschbacher--Smith,
G.9.3(10), printed pp.354, 356--357.
-/

@[expose] public noncomputable section

open scoped TensorProduct
namespace Atlas.G2.TensorClassification
open Restricted

variable (F : Type*) [Field F] [CharP F 2] [Finite F]

/-- Pull back a concrete restricted factor along the indicated actual Frobenius. -/
def factorRep (r : ℕ) (a : Factor) : Representation F (Model F) (Restricted.Space F a) :=
  (Restricted.action F a).comp (Restricted.frobeniusAutomorphism F r).toMonoidHom

/-- The finite-field tensor carrier; the empty word is the tensor unit. -/
def WordModule : List Factor → ModuleCat F
  | [] => ModuleCat.of F F
  | a :: w => ModuleCat.of F (Restricted.Space F a ⊗[F] WordModule w)

/-- The carrier of a tensor word, with its canonical module structure. -/
abbrev WordSpace (w : List Factor) := WordModule F w

/-- Tensor words have finite-dimensional carriers. -/
instance wordSpaceFiniteDimensional (w : List Factor) :
    FiniteDimensional F (WordSpace F w) := by
  induction w with
  | nil => change FiniteDimensional F F; infer_instance
  | cons a w ih =>
    change FiniteDimensional F (Restricted.Space F a ⊗[F] WordSpace F w)
    infer_instance

/-- Actual tensor action, with consecutive Frobenius exponents starting at `r`. -/
def wordRep : (r : ℕ) → (w : List Factor) →
    Representation F (Model F) (WordSpace F w)
  | _, [] => Representation.trivial F (Model F) F
  | r, a :: w => (factorRep F r a).tprod (wordRep (r + 1) w)

/-- The product of the dimensions of the concrete factors. -/
def wordDegree (w : List Factor) : ℕ := (w.map Factor.dimension).prod

omit [Finite F] in
/-- The finite-field tensor has exactly the product dimension. -/
@[simp] theorem finrank_wordSpace (w : List Factor) :
    Module.finrank F (WordSpace F w) = wordDegree w := by
  induction w with
  | nil => exact Module.finrank_self F
  | cons a w ih =>
    change Module.finrank F (Restricted.Space F a ⊗[F] WordSpace F w) = _
    rw [Module.finrank_tensorProduct, Restricted.finrank_space, ih]
    simp [wordDegree]

/-- Every factor has positive dimension, including the empty product. -/
theorem wordDegree_pos (w : List Factor) : 0 < wordDegree w := by
  induction w with
  | nil => decide
  | cons a w ih =>
    change 0 < a.dimension * wordDegree w
    apply Nat.mul_pos _ ih
    cases a <;> decide

/-- Product dimension one occurs exactly for the all-trivial word. -/
theorem wordDegree_eq_one_iff (w : List Factor) :
    wordDegree w = 1 ↔ ∀ a ∈ w, a = .trivial := by
  induction w with
  | nil => simp [wordDegree]
  | cons a w ih =>
    change a.dimension * wordDegree w = 1 ↔ _
    cases a <;> simp only [Factor.dimension, List.forall_mem_cons, one_mul] at *
    · simpa using ih
    all_goals constructor
    all_goals intro h
    all_goals simp_all

variable (K : Type*) [Field K] [Algebra F K]

/-- The length-`n` tensor carrier after extending to the coefficient field. -/
abbrev TensorSpace {n : ℕ} (w : Fin n → Factor) := K ⊗[F] WordSpace F (List.ofFn w)

/-- The concrete length-`n` Frobenius tensor over the coefficient field. -/
def tensorRep {n : ℕ} (w : Fin n → Factor) :
    Representation K (Model F) (TensorSpace F K w) :=
  Representation.extendScalars K (wordRep F 0 (List.ofFn w))

omit [Finite F] in
/-- Scalar extension preserves the tensor product dimension formula. -/
@[simp] theorem finrank_tensorSpace {n : ℕ} (w : Fin n → Factor) :
    Module.finrank K (TensorSpace F K w) = ∏ i, (w i).dimension := by
  rw [Module.finrank_baseChange, finrank_wordSpace]
  simp [wordDegree, List.map_ofFn, List.prod_ofFn]

omit [Field F] [CharP F 2] [Finite F] in
/-- There are exactly `q²` words when the field has order `q = 2^n`. -/
theorem tensor_parameter_card (n : ℕ) (hF : Nat.card F = 2 ^ n) :
    Nat.card (Fin n → Factor) = Nat.card F ^ 2 := by
  have hc : Fintype.card Factor = 4 := by decide
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hc, hF]
  calc 4 ^ n = (2 ^ 2) ^ n := rfl
       _ = (2 ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

section Equivalences
variable {F} {G V V' W W' : Type*} [Group G]
  [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']
  [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W']

/-- Tensor two genuine intertwining equivalences. -/
def tensorEquiv {ρ : Representation F G V} {ρ' : Representation F G V'}
    {τ : Representation F G W} {τ' : Representation F G W'}
    (e : ρ.Equiv ρ') (f : τ.Equiv τ') : (ρ.tprod τ).Equiv (ρ'.tprod τ') :=
  .mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv)
    (e.toIntertwiningMap.tensor f.toIntertwiningMap).isIntertwining'
end Equivalences

/-- Every field twist of the trivial factor is the actual trivial line. -/
def trivialFactorEquiv (r : ℕ) :
    (factorRep F r .trivial).Equiv (Representation.trivial F (Model F) F) :=
  Representation.Equiv.refl _

/-- Remove the tensor unit from a one-letter word. -/
def singletonEquiv (r : ℕ) (a : Factor) :
    (wordRep F r [a]).Equiv (factorRep F r a) :=
  Representation.TensorProduct.rid F (factorRep F r a)

/-- Remove all trivial factors, retaining the intertwining equivalence. -/
def trivialWordEquiv (r : ℕ) (w : List Factor) (hw : ∀ a ∈ w, a = .trivial) :
    (wordRep F r w).Equiv (Representation.trivial F (Model F) F) := by
  induction w generalizing r with
  | nil => exact Representation.Equiv.refl _
  | cons a w ih =>
    have ha := hw a (List.mem_cons_self ..)
    subst a
    exact (tensorEquiv (trivialFactorEquiv F r)
      (ih (r + 1) (fun b hb => hw b (List.mem_cons_of_mem _ hb)))).trans
      (Representation.TensorProduct.lid F (Representation.trivial F (Model F) F))

/-- The natural letter is the actual octonion quotient, with its field twist. -/
def naturalFactorEquiv (r : ℕ) :
    (factorRep F r .natural).Equiv
      ((Atlas.G2.Natural.action F).comp
        (Restricted.frobeniusAutomorphism F r).toMonoidHom) :=
  .mk (Restricted.naturalActualEquiv F).toLinearEquiv (fun g =>
    (Restricted.naturalActualEquiv F).isIntertwining' (Restricted.frobeniusAutomorphism F r g))

/-- Remove trivial factors before and after a specified factor. -/
def oneFactorEquiv (r i j : ℕ) (a : Factor) :
    (wordRep F r (List.replicate i .trivial ++ a :: List.replicate j .trivial)).Equiv
      (factorRep F (r + i) a) := by
  induction i generalizing r with
  | zero =>
    change ((factorRep F r a).tprod
      (wordRep F (r + 1) (List.replicate j .trivial))).Equiv (factorRep F r a)
    exact
      (tensorEquiv (Representation.Equiv.refl (factorRep F r a))
        (trivialWordEquiv F (r + 1) (List.replicate j .trivial)
          (by simp))).trans (Representation.TensorProduct.rid F (factorRep F r a))
  | succ i ih =>
    simp only [List.replicate_succ, List.cons_append]
    exact ((tensorEquiv (trivialFactorEquiv F r)
      (Representation.Equiv.refl _)).trans (Representation.TensorProduct.lid F _)).trans
      (by simpa only [Nat.add_assoc, Nat.add_comm 1 i] using ih (r + 1))

/-- The position of the unique natural factor determines its actual field twist. -/
def oneNaturalEquiv (i j : ℕ) :
    (wordRep F 0 (List.replicate i .trivial ++ .natural :: List.replicate j .trivial)).Equiv
      ((Atlas.G2.Natural.action F).comp
        (Restricted.frobeniusAutomorphism F i).toMonoidHom) :=
  (oneFactorEquiv F 0 i j .natural).trans
    (by simpa only [Nat.zero_add] using naturalFactorEquiv F i)

/-- Extend a genuine intertwiner to the coefficient field. -/
def extendEquiv {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    {ρ : Representation F (Model F) V} {τ : Representation F (Model F) W}
    (e : ρ.Equiv τ) :
    (Representation.extendScalars K ρ).Equiv (Representation.extendScalars K τ) :=
  .mk (LinearEquiv.baseChange F K V W e.toLinearEquiv) (by
    intro g
    change (e.toLinearMap.baseChange K).comp ((ρ g).baseChange K) =
      ((τ g).baseChange K).comp (e.toLinearMap.baseChange K)
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, e.isIntertwining' g])

/-- The scalar extension of the trivial line is the actual coefficient-field line. -/
def trivialExtendEquiv :
    (Representation.extendScalars K (Representation.trivial F (Model F) F)).Equiv
      (Representation.trivial K (Model F) K) :=
  .mk (TensorProduct.AlgebraTensorModule.rid F K K) (by intro g; ext; rfl)

/-- The all-trivial word retains its actual intertwining equivalence. -/
def tensorTrivialEquiv {n : ℕ} (w : Fin n → Factor) (hw : ∀ i, w i = .trivial) :
    (tensorRep F K w).Equiv (Representation.trivial K (Model F) K) :=
  (extendEquiv F K (trivialWordEquiv F 0 (List.ofFn w) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hw i))).trans (trivialExtendEquiv F K)

/-- A single natural factor becomes the scalar extension of the genuine
trace-zero octonion quotient action, pulled back along the actual field automorphism. -/
def oneNaturalExtendEquiv (i j : ℕ) :
    (Representation.extendScalars K
      (wordRep F 0 (List.replicate i .trivial ++ .natural :: List.replicate j .trivial))).Equiv
      ((Representation.extendScalars K (Atlas.G2.Natural.action F)).comp
        (Restricted.frobeniusAutomorphism F i).toMonoidHom) := by
  let e := extendEquiv F K (oneNaturalEquiv F i j)
  exact .mk e.toLinearEquiv (fun g => e.isIntertwining' g)

/-- Base change distributes over the actual tensor action. -/
def tensorBaseChangeEquiv {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (ρ : Representation F (Model F) V) (τ : Representation F (Model F) W) :
    (Representation.extendScalars K (ρ.tprod τ)).Equiv
      ((Representation.extendScalars K ρ).tprod (Representation.extendScalars K τ)) :=
  .mk (TensorProduct.AlgebraTensorModule.distribBaseChange F K V W) (by
    intro g
    ext v w
    rfl)

/-- Each recursive step is an actual tensor product of extended factors. -/
def scalarWordConsEquiv (r : ℕ) (a : Factor) (w : List Factor) :
    (Representation.extendScalars K (wordRep F r (a :: w))).Equiv
      ((Representation.extendScalars K (factorRep F r a)).tprod
        (Representation.extendScalars K (wordRep F (r + 1) w))) :=
  tensorBaseChangeEquiv F K _ _

/-- The finite-field Frobenius really wraps at the field degree. -/
theorem frobeniusAutomorphism_period {n : ℕ} (hF : Nat.card F = 2 ^ n) (r : ℕ) :
    Restricted.frobeniusAutomorphism F (r + n) = Restricted.frobeniusAutomorphism F r := by
  have he : iterateFrobeniusEquiv F 2 n = RingEquiv.refl F := by
    apply RingEquiv.ext
    intro x
    change x ^ (2 ^ n) = x
    rw [← hF]
    let := Fintype.ofFinite F
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card x
  apply congrArg Atlas.G2.fieldEquiv
  apply RingEquiv.ext
  intro x
  rw [iterateFrobeniusEquiv_add_apply, he, RingEquiv.refl_apply]

/-- Wraparound holds for the concrete action, before passing to equivalence. -/
theorem factorRep_period {n : ℕ} (hF : Nat.card F = 2 ^ n) (r : ℕ) (a : Factor) :
    factorRep F (r + n) a = factorRep F r a := by
  unfold factorRep
  rw [frobeniusAutomorphism_period F hF]

end Atlas.G2.TensorClassification

end
