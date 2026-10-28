module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Coordinates
public import Theory.SpecificGroups.ReeF4.Field
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Linear-algebra reduction for faithfulness on the short F4 coordinates

An equivariant family of operators with image in a pointwise fixed subspace
commutes with the acting matrix. If the common kernel of those operators is
zero, that matrix is the identity. Equivariance propagates from generators to
the subgroup they generate, including inverses.

The final lemma specializes this argument to the short-coordinate comparison
map of `WordRelations.Coordinates`. Its hypotheses are explicit: this module
does not assert the concrete F4 operator calculations. Those require the
integral Cartan-plus-root construction described in
`F4IntegralChevalleyRepresentation` (Geck's construction and Steinberg's
*Lectures on Chevalley Groups*).
-/

@[expose] public section

open scoped Matrix

namespace ReeF4.WordRelations.Faithfulness

variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]

/-- Adjoint equivariance in a form that avoids an inverse on the right. -/
def Equivariant (D : (n → K) → Matrix n n K) (g : (Matrix n n K)ˣ) : Prop :=
  ∀ v, D ((g : Matrix n n K) *ᵥ v) * g = g * D v

/-- Equivariance for a generating set implies equivariance for its subgroup. -/
theorem equivariant_closure (D : (n → K) → Matrix n n K)
    (S : Set (Matrix n n K)ˣ)
    (hS : ∀ g ∈ S, Equivariant D g)
    {g : (Matrix n n K)ˣ} (hg : g ∈ Subgroup.closure S) : Equivariant D g := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hS g hg
  | one => intro v; simp
  | mul g h _ _ hg hh =>
    intro v
    change D (((g : Matrix n n K) * (h : Matrix n n K)) *ᵥ v) *
      ((g : Matrix n n K) * (h : Matrix n n K)) =
      ((g : Matrix n n K) * (h : Matrix n n K)) * D v
    rw [← Matrix.mulVec_mulVec, ← mul_assoc, hg, mul_assoc, hh, ← mul_assoc]
  | inv g _ hg =>
    intro v
    have h := hg ((↑g⁻¹ : Matrix n n K) *ᵥ v)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
    apply (Units.mul_right_inj g).mp
    simp only [← mul_assoc, ← h, Units.mul_inv_cancel_right,
      Units.mul_inv, one_mul]

/-- Fixing coordinate vectors fixes every vector supported on those coordinates. -/
theorem fixes_supported_vector (P : n → Prop) (A : Matrix n n K)
    (hA : ∀ j, P j → ∀ i, A i j = if i = j then 1 else 0)
    (v : n → K) (hv : ∀ j, ¬ P j → v j = 0) : A *ᵥ v = v := by
  classical
  have h : ∀ i j, A i j * v j = (1 : Matrix n n K) i j * v j := by
    intro i j
    by_cases hj : P j
    · rw [hA j hj i, Matrix.one_apply]
    · simp [hv j hj]
  calc
    A *ᵥ v = (1 : Matrix n n K) *ᵥ v := by
      ext i
      exact Finset.sum_congr rfl (fun j _ => h i j)
    _ = v := Matrix.one_mulVec v

/-- Operators supported on a fixed subspace detect every displacement when
 their common kernel is zero. No linearity or injectivity assumption on `D`
 is needed. -/
theorem eq_one_of_equivariant_operators
    {a : Type*} (P : n → Prop) (Q : a → Prop) (c : a → n)
    (hc : ∀ s, Q s → P (c s))
    (D : (n → K) → Matrix n n K) (E : a → Matrix n n K)
    (hD : ∀ s, Q s → D (Pi.single (c s) 1) = E s)
    (himage : ∀ s, Q s → ∀ i, ¬ P i → ∀ j, E s i j = 0)
    (hkernel : ∀ v : n → K, (∀ s, Q s → E s *ᵥ v = 0) → v = 0)
    (g : (Matrix n n K)ˣ) (heq : Equivariant D g)
    (hfix : ∀ j, P j → ∀ i, (g : Matrix n n K) i j = if i = j then 1 else 0) :
    g = 1 := by
  have hcomm (s : a) (hs : Q s) : E s * g = g * E s := by
    have h := heq (Pi.single (c s) 1)
    have hfixed : (g : Matrix n n K) *ᵥ Pi.single (c s) 1 =
        Pi.single (c s) 1 := by
      rw [Matrix.mulVec_single_one]
      ext i
      simpa only [Matrix.col_apply, Pi.single_apply] using hfix (c s) (hc s hs) i
    rwa [hfixed, hD s hs] at h
  have hleft (s : a) (hs : Q s) : (g : Matrix n n K) * E s = E s := by
    ext i j
    exact congrFun (fixes_supported_vector P (g : Matrix n n K) hfix
      (fun k => E s k j) (fun k hk => himage s hs k hk j)) i
  have hright (s : a) (hs : Q s) : E s * (g : Matrix n n K) = E s :=
    (hcomm s hs).trans (hleft s hs)
  apply Units.ext
  have hm : (g : Matrix n n K) - 1 = 0 := by
    ext i j
    have hz := hkernel (fun k => ((g : Matrix n n K) - 1) k j) (by
      intro s hs
      have hprod : E s * ((g : Matrix n n K) - 1) = 0 := by
        rw [mul_sub, hright s hs, mul_one, sub_self]
      exact congrArg (fun A : Matrix n n K => fun k => A k j) hprod)
    exact congrFun hz i
  exact sub_eq_zero.mp hm

open Theory.AlgebraicGroup.StandardRootSystem

noncomputable local instance : Fintype typeF4Roots := Fintype.ofFinite _

/-- Reduction of short-coordinate faithfulness to generator equivariance,
 short-operator image containment, and a trivial common kernel. The concrete
 F4 representation must supply all four operator hypotheses. -/
theorem eq_one_of_short_operator_hypotheses
    (S : Set (Matrix Coordinate Coordinate K)ˣ)
    (D : (Coordinate → K) → Matrix Coordinate Coordinate K)
    (E : typeF4Roots → Matrix Coordinate Coordinate K)
    (hD : ∀ s, IsShortRoot s → D (Pi.single (Sum.inr s) 1) = E s)
    (hgen : ∀ g ∈ S, Equivariant D g)
    (himage : ∀ s, IsShortRoot s → ∀ i, ¬ IsShortCoordinate i → ∀ j, E s i j = 0)
    (hkernel : ∀ v : Coordinate → K,
      (∀ s, IsShortRoot s → E s *ᵥ v = 0) → v = 0)
    (g : (Matrix Coordinate Coordinate K)ˣ) (hg : g ∈ Subgroup.closure S)
    (hfix : (g : Matrix Coordinate Coordinate K) * quotientToIdeal = quotientToIdeal) :
    g = 1 := by
  classical
  exact eq_one_of_equivariant_operators IsShortCoordinate IsShortRoot Sum.inr
    (fun _ hs => hs) D E hD himage hkernel g
    (equivariant_closure D S hgen hg) ((mul_quotientToIdeal_eq_iff _).mp hfix)

end ReeF4.WordRelations.Faithfulness
