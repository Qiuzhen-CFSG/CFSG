module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.OrbitTable

/-!
# The local short A2 input and its multiplicity calculation

The adjacent short simple roots of F4 are nodes 2 and 3. A vector of their
sum weight has coefficients `(1,1)` on these nodes. The two lowering orders
`f₀ f₁ v` and `f₁ f₀ v` are independent in characteristic two: `e₁` annihilates
the second and sends the first to the nonzero vector `f₀ v`, while `e₀` detects
the second. The relation `[h₁,f₀] = f₀` is what makes the second image zero.

The lemma below proves this linear-algebra calculation from the five indicated
operator relations. It does not assume the operators exist for an arbitrary
factor. Establishing them from the rational action, and showing the lowering
vectors have full F4 weight zero, remain necessary for the multiplicity bound.

Source: GLS3, Section 1.14, together with the Chevalley commutator relations
for the A2 subsystem on the two short nodes of the diagram in Section 1.8.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

namespace ReeF4.BinaryDegree.ExceptionalTensor.EndNode

universe u

section HighestVector

variable {F : Type u} [Field F] [IsAlgClosed F]

/-- A nonzero vector of full coroot weight `α₂ + α₃`, fixed by the two
positive simple root groups of the short A2 subsystem. -/
@[expose] def IsShortA2HighestVector (B : AlgebraicFactor F) (v : B.Space) : Prop :=
  v ≠ 0 ∧ v ∈ corootWeightSpace B shortA2Weight ∧
    (∀ t : F, (B.action.action (algebraicRootElement (typeF4SimpleRootIndex 2) t) :
      Module.End F B.Space) v = v) ∧
    (∀ t : F, (B.action.action (algebraicRootElement (typeF4SimpleRootIndex 3) t) :
      Module.End F B.Space) v = v)

/-- The representation contains the local A2 highest vector needed for
constructing two zero-weight vectors. This is a separate geometric input. -/
@[expose] def HasShortA2HighestVector (B : AlgebraicFactor F) : Prop :=
  ∃ v, IsShortA2HighestVector B v

end HighestVector

section Lowering

variable {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]

/-- The A2 commutator relations separate the two orders of lowering a highest
vector of coefficients `(1,1)` in characteristic two. Actual root operators
and the full zero-weight equations must still be constructed by the caller. -/
theorem linearIndependent_shortA2_lowerings
    (e₀ e₁ f₀ f₁ h₀ h₁ : Module.End F V)
    (he₀f₀ : e₀ * f₀ - f₀ * e₀ = h₀)
    (he₁f₁ : e₁ * f₁ - f₁ * e₁ = h₁)
    (he₀f₁ : e₀ * f₁ = f₁ * e₀)
    (he₁f₀ : e₁ * f₀ = f₀ * e₁)
    (hh₁f₀ : h₁ * f₀ - f₀ * h₁ = f₀)
    (v : V) (hv : v ≠ 0) (he₀v : e₀ v = 0) (he₁v : e₁ v = 0)
    (hh₀v : h₀ v = v) (hh₁v : h₁ v = v) :
    LinearIndependent F ![f₀ (f₁ v), f₁ (f₀ v)] := by
  have hdouble (x : V) : x + x = 0 := by
    simpa only [Nat.cast_ofNat, two_smul, zero_smul] using
      congrArg (fun c : F => c • x) (CharP.cast_eq_zero F 2)
  have he₀f₀v : e₀ (f₀ v) = v := by
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, he₀v, map_zero,
      sub_zero, hh₀v] using congrArg (fun a : Module.End F V => a v) he₀f₀
  have he₁f₁v : e₁ (f₁ v) = v := by
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, he₁v, map_zero,
      sub_zero, hh₁v] using congrArg (fun a : Module.End F V => a v) he₁f₁
  have hf₀v : f₀ v ≠ 0 := by
    intro h
    exact hv (by simpa only [h, map_zero] using he₀f₀v.symm)
  have hf₁v : f₁ v ≠ 0 := by
    intro h
    exact hv (by simpa only [h, map_zero] using he₁f₁v.symm)
  have hh₁f₀v : h₁ (f₀ v) = 0 := by
    have h : h₁ (f₀ v) - f₀ v = f₀ v := by
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, hh₁v] using
        congrArg (fun a : Module.End F V => a v) hh₁f₀
    exact (sub_eq_iff_eq_add.mp h).trans (hdouble _)
  have he₁f₀v : e₁ (f₀ v) = 0 := by
    simpa only [Module.End.mul_apply, he₁v, map_zero] using
      congrArg (fun a : Module.End F V => a v) he₁f₀
  have hleft : e₁ (f₀ (f₁ v)) = f₀ v := by
    simpa only [Module.End.mul_apply, he₁f₁v] using
      congrArg (fun a : Module.End F V => a (f₁ v)) he₁f₀
  have hright₀ : e₀ (f₁ (f₀ v)) = f₁ v := by
    simpa only [Module.End.mul_apply, he₀f₀v] using
      congrArg (fun a : Module.End F V => a (f₀ v)) he₀f₁
  have hright₁ : e₁ (f₁ (f₀ v)) = 0 := by
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, he₁f₀v,
      map_zero, sub_zero, hh₁f₀v] using
      congrArg (fun a : Module.End F V => a (f₀ v)) he₁f₁
  apply linearIndependent_fin2.mpr
  constructor
  · intro hz
    change f₁ (f₀ v) = 0 at hz
    exact hf₁v (by simpa only [hz, map_zero] using hright₀.symm)
  · intro c hc
    have h := congrArg e₁ hc
    exact hf₀v (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, map_smul, hright₁, smul_zero, hleft] using h.symm)

end Lowering

end ReeF4.BinaryDegree.ExceptionalTensor.EndNode
