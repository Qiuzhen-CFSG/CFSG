module

public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Basic
public import Theory.Representation.ExtendScalars
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Concrete small binary SL₂ module models

The natural module is the column action restricted to the prime field.
The four-dimensional Hermitian module uses the actual fixed half-field
and conjugation action constructed in `OrthogonalFourMinus.FiniteModel`.
The exceptional model is the tensor product of the natural action and
its first two Frobenius twists over the given field of eight elements.

The recognition predicates require genuine intertwining equivalences;
the Hermitian predicate additionally retains a ring equivalence with the
specified extension field. They do not assert exhaustivity. The formulas
below expose all three actions, and the finite-field comparison proves
that the prescribed Hermitian coefficient field can be identified with
any field of the same order.

Source: GLS volume 3, §§2.8.6, 2.8.8, 2.8.10(b); Aschbacher--Smith,
combined manuscript (1 March 2004), G.9.3(6), (7), (16), printed p.354.
The comparison of the Hermitian group with literal minus Omega is a
separate construction, not part of these definitions.
-/

@[expose] public section

open scoped MatrixGroups TensorProduct
namespace Representation.SL2.BinarySmall
noncomputable section
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local instance binaryAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- The two-dimensional column space over the defining field. -/
abbrev NaturalSpace (K : Type*) := Fin 2 → K

/-- Restriction of the natural action to the binary prime field. -/
def natural : Representation (ZMod 2) SL(2,K) (NaturalSpace K) :=
  restrictScalars (specialLinearNatural 2)

/-- Twist by the actual `j`-th Frobenius automorphism of the field. -/
def frobeniusNatural (j : ℕ) : Representation K SL(2,K) (NaturalSpace K) :=
  (specialLinearNatural 2).comp
    (Matrix.SpecialLinearGroup.map (iterateFrobeniusEquiv K 2 j).toRingHom)

/-- The tensor space with three two-dimensional factors. -/
abbrev TripleSpace (K : Type*) [Field K] :=
  ((NaturalSpace K) ⊗[K] (NaturalSpace K)) ⊗[K] (NaturalSpace K)

/-- The tensor action `N ⊗ N^σ ⊗ N^(σ²)`, with `σ(x) = x²`. -/
def triple : Representation K SL(2,K) (TripleSpace K) :=
  ((frobeniusNatural 0).tprod (frobeniusNatural 1)).tprod (frobeniusNatural 2)

open OrthogonalFourMinus.FiniteModel
local instance fixedBinaryAlgebra (s : ℕ) : Algebra (ZMod 2) (fixedField s) :=
  ZMod.algebra (fixedField s) 2
local instance spaceBinaryModule (s : ℕ) [NeZero s] : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The existing Hermitian conjugation action, viewed over the prime field. -/
def hermitian (s : ℕ) [NeZero s] :
    Representation (ZMod 2) SL(2,Field s) (Space s) where
  toFun g := ((action s g).toAddMonoidHom).toZModLinearMap 2
  map_one' := by apply LinearMap.ext; intro v; exact congrArg (fun f => f v) (action s).map_one
  map_mul' g h := by apply LinearMap.ext; intro v; exact congrArg (fun f => f v) ((action s).map_mul g h)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,K) V)

/-- Equivalence to the natural scalar restriction, for this actual group. -/
def IsNatural : Prop := Nonempty (ρ.Equiv (natural (K := K)))

/-- Equivalence to the Hermitian action along an actual field identification. -/
def IsHermitian (s : ℕ) [NeZero s] : Prop :=
  ∃ e : K ≃+* Field s,
    Nonempty (ρ.Equiv ((hermitian s).comp (Matrix.SpecialLinearGroup.map e.toRingHom)))

/-- The scalar extension to the defining field is the actual triple tensor. -/
def IsTriple : Prop := Nonempty ((extendScalars K ρ).Equiv (triple (K := K)))
omit [Finite K] in
/-- The natural binary action is the actual matrix action on columns. -/
theorem natural_apply (g : SL(2,K)) (v : NaturalSpace K) :
    natural g v = Matrix.mulVec g.val v := rfl

/-- A twist applies the specified Frobenius to every matrix entry. -/
theorem frobeniusNatural_apply (j : ℕ) (g : SL(2,K)) (v : NaturalSpace K) :
    frobeniusNatural j g v =
      Matrix.mulVec (g.val.map (iterateFrobeniusEquiv K 2 j)) v := rfl

/-- On pure tensors the three factors have exponents 1, 2 and 4. -/
theorem triple_apply_tmul (g : SL(2,K)) (u v w : NaturalSpace K) :
    triple g ((u ⊗ₜ[K] v) ⊗ₜ[K] w) =
      ((frobeniusNatural 0 g u) ⊗ₜ[K] (frobeniusNatural 1 g v)) ⊗ₜ[K]
        (frobeniusNatural 2 g w) := by
  simp only [triple, Representation.tprod_apply, TensorProduct.map_tmul]

/-- Scalar restriction retains the literal Hermitian conjugation formula. -/
theorem hermitian_apply (s : ℕ) [NeZero s]
    (g : SL(2,Field s)) (X : Space s) :
    (hermitian s g X).val =
      g.val * X.val * OrthogonalFourMinus.adjoint (conjugation s) g.val := rfl

omit [CharP K 2] in
/-- A field of the specified order is genuinely isomorphic to the extension
field used in the Hermitian model. -/
theorem nonempty_hermitianFieldEquiv (s : ℕ) [NeZero s]
    (hcard : Nat.card K = 2 ^ (2 * s)) : Nonempty (K ≃+* Field s) := by
  let : Fintype K := Fintype.ofFinite K
  let : Fintype (Field s) := Fintype.ofFinite (Field s)
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcard]
  exact (GaloisField.card 2 (2 * s) (Nat.mul_ne_zero (by decide) (NeZero.ne s))).symm

end
end Representation.SL2.BinarySmall
