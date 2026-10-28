module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Carrier
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Frobenius.PointAction
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Frobenius.RegularLift
public import Theory.AlgebraicGroup.Automorphisms.Steinberg

/-!
# Frobenius on the concrete split D4 Spin carrier

Over every algebraically closed field of characteristic two, ordinary Frobenius
is a regular endomorphism of the exact closed left-regular Clifford Spin group
of four hyperbolic planes. Its point map is the automorphism characterized by
coordinate Frobenius in the natural eight-dimensional representation.

`RegularLift` proves polynomial regularity using semilinear Clifford
functoriality. Here faithfulness of the natural action identifies the regular
maps and proves their zero and exponent-addition laws. Fixed points inject into
matrices over the roots of `X^(2^n) - X`, giving the Steinberg property for every
`n > 0`, including `n = 1`. The point-group bijection does not assert a regular
inverse. Compatibility with the separately constructed pinning, and composition
with triality, belong to the pinned graph-field assembly.

Source: GLS3, 1.15.1–4 and §§2.1–2.2.
-/

public section
noncomputable section
open Theory.AlgebraicGroup
universe u

namespace Triality.SimplyConnected
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Equality of the regular and abstract Frobenius point homomorphisms. -/
theorem regularFrobeniusLift_onPoints_eq (n : ℕ) :
    (regularFrobeniusLift k n).onPoints = (frobeniusPointAut k n).toMonoidHom :=
  MonoidHom.ext (regularFrobeniusLift_onPoints k n)

/-- The point automorphism has the independently constructed regular realization. -/
theorem regularFrobeniusLift_realizesPointAut (n : ℕ) :
    IsAlgebraicRealization (frobeniusPointAut k n) (regularFrobeniusLift k n) := by
  intro g
  exact (regularFrobeniusLift_onPoints k n g).symm

/-- The regular Frobenius intertwines the natural action with coordinate powers. -/
theorem regularFrobeniusLift_naturalAction (n : ℕ) (g : Points k)
    (v : QuadraticSpace k) :
    vectorFrobenius k n ((naturalAction k g).1 v) =
      (naturalAction k ((regularFrobeniusLift k n).onPoints g)).1
        (vectorFrobenius k n v) := by
  rw [regularFrobeniusLift_onPoints]
  exact frobenius_naturalAction k n g v

/-- Frobenius is bijective on points, including at exponents zero and one. -/
theorem regularFrobeniusLift_bijective (n : ℕ) :
    Function.Bijective (regularFrobeniusLift k n).onPoints := by
  rw [regularFrobeniusLift_onPoints_eq]
  exact frobeniusPointAut_bijective k n

/-- The zeroth Frobenius is the identity as a regular morphism. -/
@[simp] theorem regularFrobeniusLift_zero :
    regularFrobeniusLift k 0 = Morphism.id (groupVariety k) := by
  apply Morphism.ext
  funext g
  change (regularFrobeniusLift k 0).onPoints g = g
  rw [regularFrobeniusLift_onPoints, frobeniusPointAut_zero_apply]

/-- Addition of exponents is composition of regular Frobenius morphisms. -/
theorem regularFrobeniusLift_add (m n : ℕ) :
    regularFrobeniusLift k (m + n) =
      (regularFrobeniusLift k m).comp (regularFrobeniusLift k n) := by
  apply Morphism.ext
  funext g
  change (regularFrobeniusLift k (m + n)).onPoints g =
    (regularFrobeniusLift k m).onPoints ((regularFrobeniusLift k n).onPoints g)
  simp only [regularFrobeniusLift_onPoints, frobeniusPointAut_add_apply]

/-- The regular Frobenius morphisms commute with each other. -/
theorem regularFrobeniusLift_comp_comm (m n : ℕ) :
    (regularFrobeniusLift k m).comp (regularFrobeniusLift k n) =
      (regularFrobeniusLift k n).comp (regularFrobeniusLift k m) := by
  rw [← regularFrobeniusLift_add, ← regularFrobeniusLift_add, Nat.add_comm]

/-- The standard natural-action equation uniquely specifies the regular lift. -/
theorem eq_regularFrobeniusLift_of_naturalAction (n : ℕ)
    (f : Morphism (groupVariety k) (groupVariety k))
    (hf : ∀ g v, vectorFrobenius k n ((naturalAction k g).1 v) =
      (naturalAction k (f.onPoints g)).1 (vectorFrobenius k n v)) :
    f = regularFrobeniusLift k n := by
  apply Morphism.ext
  funext g
  change f.onPoints g = (regularFrobeniusLift k n).onPoints g
  rw [regularFrobeniusLift_onPoints]
  exact congrFun (eq_frobeniusPointAut_of_naturalAction k n f.onPoints hf) g

/-- Positive regular Frobenius has finitely many fixed points. -/
theorem finite_regularFrobeniusLift_fixedPoints (n : ℕ) (hn : 0 < n) :
    Finite {g : Points k | (regularFrobeniusLift k n).onPoints g = g} := by
  have h : Finite {g : Points k | frobeniusPointAut k n g = g} :=
    finite_frobeniusFixedSubgroup k n hn
  simpa only [regularFrobeniusLift_onPoints] using h

/-- Every positive Frobenius, including the squaring Frobenius, is Steinberg. -/
theorem regularFrobeniusLift_isSteinberg (n : ℕ) (hn : 0 < n) :
    IsAlgebraicSteinbergEndomorphism (regularFrobeniusLift k n) :=
  ⟨(regularFrobeniusLift_bijective k n).2,
    finite_regularFrobeniusLift_fixedPoints k n hn⟩

/-- The abstract positive Frobenius belongs to the algebraically realized
Steinberg automorphisms. -/
theorem frobeniusPointAut_mem_steinbergAutomorphismSet (n : ℕ) (hn : 0 < n) :
    frobeniusPointAut k n ∈ SteinbergAutomorphismSet (groupVariety k) :=
  ⟨regularFrobeniusLift k n, regularFrobeniusLift_realizesPointAut k n,
    regularFrobeniusLift_isSteinberg k n hn⟩

end Triality.SimplyConnected
