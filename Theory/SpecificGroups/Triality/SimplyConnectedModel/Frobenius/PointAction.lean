module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Carrier
public import Theory.AlgebraicGroup.RootSystems.HyperbolicFieldAutomorphisms
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Ordinary Frobenius on the concrete Spin point group

In characteristic two the concrete Clifford Spin cover identifies its point
group with the commutator of the hyperbolic quadratic-isometry group. A field
automorphism acts on this commutator by semilinear coordinate conjugation.
Lifting that action gives a point-group automorphism of the exact Spin carrier.
For the scalar map `t ↦ t^(2^n)` the natural action satisfies the standard
coordinate Frobenius equation. Faithfulness proves the exponent-addition law.

Fixed points inject into matrices over the finite set of roots of
`X^(2^n) - X`, so their subgroup is finite for every `n > 0`, including `n = 1`.
The construction also includes `n = 0`, which acts identically.

These are the point-group and finiteness parts of GLS3, 1.15.4(a) and 2.1.
Regularity on the Spin variety is a separate geometric obligation: the inverse
of the Spin-to-Omega point equivalence is not an algebraic inverse.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup
universe u

namespace Triality.SimplyConnected
open Theory.AlgebraicGroup.HyperbolicFieldAutomorphisms

variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Lift semilinear conjugation on Ω to the concrete Spin point group. -/
def coefficientPointAut (σ : k ≃+* k) : Points k ≃* Points k :=
  (omegaPointEquiv k).trans
    ((MulAut.characteristic (commutator (quadraticIsometrySubgroup (quadraticForm k)))
      (orthogonal 4 σ)).trans (omegaPointEquiv k).symm)

theorem naturalAction_coefficientPointAut (σ : k ≃+* k) (g : Points k)
    (v : QuadraticSpace k) :
    (naturalAction k (coefficientPointAut k σ g)).1 v =
      coordinates 4 σ ((naturalAction k g).1 (coordinates 4 σ.symm v)) := by
  change ((omegaPointEquiv k (coefficientPointAut k σ g)).1.1 v) = _
  simp only [coefficientPointAut, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

/-- Raise each of the eight standard hyperbolic coordinates to `2^n`. -/
def vectorFrobenius (n : ℕ) : QuadraticSpace k ≃+ QuadraticSpace k :=
  coordinates 4 (iterateFrobeniusEquiv k 2 n)

@[simp] theorem vectorFrobenius_fst (n : ℕ) (v : QuadraticSpace k) (i : Fin 4) :
    (vectorFrobenius k n v).1 i = (v.1 i) ^ (2 ^ n) := rfl

@[simp] theorem vectorFrobenius_snd (n : ℕ) (v : QuadraticSpace k) (i : Fin 4) :
    (vectorFrobenius k n v).2 i = (v.2 i) ^ (2 ^ n) := rfl

@[simp] theorem vectorFrobenius_zero (v : QuadraticSpace k) :
    vectorFrobenius k 0 v = v := by ext <;> simp

theorem vectorFrobenius_add (m n : ℕ) (v : QuadraticSpace k) :
    vectorFrobenius k (m + n) v = vectorFrobenius k m (vectorFrobenius k n v) := by
  apply Prod.ext <;> funext i <;>
    exact iterateFrobeniusEquiv_add_apply k 2 m n _

/-- Ordinary Frobenius as an automorphism of the Spin point group. -/
def frobeniusPointAut (n : ℕ) : Points k ≃* Points k :=
  coefficientPointAut k (iterateFrobeniusEquiv k 2 n)

/-- Frobenius is anchored to the standard coordinates of the natural action. -/
theorem frobenius_naturalAction (n : ℕ) (g : Points k) (v : QuadraticSpace k) :
    vectorFrobenius k n ((naturalAction k g).1 v) =
      (naturalAction k (frobeniusPointAut k n g)).1 (vectorFrobenius k n v) := by
  rw [frobeniusPointAut, naturalAction_coefficientPointAut]
  simp only [vectorFrobenius, coordinates_symm_apply]

/-- The coordinate equation uniquely determines the point map. This also
identifies any independently constructed regular lift with this Frobenius. -/
theorem eq_frobeniusPointAut_of_naturalAction (n : ℕ) (f : Points k → Points k)
    (hf : ∀ g v, vectorFrobenius k n ((naturalAction k g).1 v) =
      (naturalAction k (f g)).1 (vectorFrobenius k n v)) :
    f = frobeniusPointAut k n := by
  funext g
  apply naturalAction_injective k
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, rfl⟩ := (vectorFrobenius k n).surjective v
  rw [← hf, frobenius_naturalAction]

theorem frobeniusPointAut_zero_apply (g : Points k) :
    frobeniusPointAut k 0 g = g := by
  apply naturalAction_injective k
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simpa only [vectorFrobenius_zero] using (frobenius_naturalAction k 0 g v).symm

theorem frobeniusPointAut_add_apply (m n : ℕ) (g : Points k) :
    frobeniusPointAut k (m + n) g =
      frobeniusPointAut k m (frobeniusPointAut k n g) := by
  apply naturalAction_injective k
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, rfl⟩ := (vectorFrobenius k (m + n)).surjective v
  rw [← frobenius_naturalAction, vectorFrobenius_add, frobenius_naturalAction,
    frobenius_naturalAction, vectorFrobenius_add]

theorem frobeniusPointAut_bijective (n : ℕ) :
    Function.Bijective (frobeniusPointAut k n) := (frobeniusPointAut k n).bijective

@[simp] theorem frobeniusPointAut_zero :
    frobeniusPointAut k 0 = MulEquiv.refl (Points k) := by
  ext g
  exact frobeniusPointAut_zero_apply k g

theorem frobeniusPointAut_add (m n : ℕ) :
    frobeniusPointAut k (m + n) =
      (frobeniusPointAut k n).trans (frobeniusPointAut k m) := by
  ext g
  exact frobeniusPointAut_add_apply k m n g

/-- The standard basis of the two four-dimensional summands. -/
def hyperbolicBasis : Module.Basis (Fin 4 ⊕ Fin 4) k (QuadraticSpace k) :=
  (Pi.basisFun k (Fin 4)).prod (Pi.basisFun k (Fin 4))

theorem vectorFrobenius_basis (n : ℕ) (i : Fin 4 ⊕ Fin 4) :
    vectorFrobenius k n (hyperbolicBasis k i) = hyperbolicBasis k i := by
  cases i <;> ext j <;>
    simp [hyperbolicBasis, Pi.basisFun_apply, Pi.single_apply, apply_ite]

theorem hyperbolicBasis_repr_vectorFrobenius (n : ℕ) (v : QuadraticSpace k)
    (i : Fin 4 ⊕ Fin 4) :
    (hyperbolicBasis k).repr (vectorFrobenius k n v) i =
      ((hyperbolicBasis k).repr v i) ^ (2 ^ n) := by
  cases i <;> simp [hyperbolicBasis, Pi.basisFun_repr]

/-- Matrix entries of the natural action in the standard hyperbolic basis. -/
def naturalMatrix (g : Points k) (i j : Fin 4 ⊕ Fin 4) : k :=
  (hyperbolicBasis k).repr ((naturalAction k g).1 (hyperbolicBasis k j)) i

theorem naturalMatrix_injective : Function.Injective (naturalMatrix k) := by
  intro g h he
  apply naturalAction_injective k
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (hyperbolicBasis k).ext
  intro j
  apply (hyperbolicBasis k).repr.injective
  ext i
  exact congrFun (congrFun he i) j

theorem naturalMatrix_frobenius (n : ℕ) (g : Points k) (i j : Fin 4 ⊕ Fin 4) :
    naturalMatrix k (frobeniusPointAut k n g) i j =
      naturalMatrix k g i j ^ (2 ^ n) := by
  unfold naturalMatrix
  rw [← hyperbolicBasis_repr_vectorFrobenius, frobenius_naturalAction,
    vectorFrobenius_basis]

/-- The full subgroup fixed by ordinary Frobenius. -/
def frobeniusFixedSubgroup (n : ℕ) : Subgroup (Points k) where
  carrier := {g | frobeniusPointAut k n g = g}
  one_mem' := map_one _
  mul_mem' := by
    intro g h hg hh
    change frobeniusPointAut k n g = g at hg
    change frobeniusPointAut k n h = h at hh
    change frobeniusPointAut k n (g * h) = g * h
    rw [map_mul, hg, hh]
  inv_mem' := by
    intro g hg
    change frobeniusPointAut k n g = g at hg
    change frobeniusPointAut k n g⁻¹ = g⁻¹
    rw [map_inv, hg]

@[simp] theorem mem_frobeniusFixedSubgroup (n : ℕ) (g : Points k) :
    g ∈ frobeniusFixedSubgroup k n ↔ frobeniusPointAut k n g = g := Iff.rfl

/-- Every positive exponent has a finite fixed subgroup, including exponent one. -/
theorem finite_frobeniusFixedSubgroup (n : ℕ) (hn : 0 < n) :
    Finite (frobeniusFixedSubgroup k n) := by
  have hs : Set.Finite {x : k | x ^ (2 ^ n) = x} := by
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero] using
      Polynomial.finite_setOfPred_isRoot
        (FiniteField.X_pow_card_pow_sub_X_ne_zero k hn.ne' (by decide : 1 < 2))
  let : Finite {x : k // x ^ (2 ^ n) = x} := hs.to_subtype
  let f : frobeniusFixedSubgroup k n →
      (Fin 4 ⊕ Fin 4) → (Fin 4 ⊕ Fin 4) → {x : k // x ^ (2 ^ n) = x} :=
    fun g i j => ⟨naturalMatrix k g.1 i j, by
      rw [← naturalMatrix_frobenius, g.2]⟩
  apply Finite.of_injective f
  intro g h he
  apply Subtype.ext
  apply naturalMatrix_injective k
  funext i j
  exact congrArg Subtype.val (congrFun (congrFun he i) j)

end Triality.SimplyConnected
