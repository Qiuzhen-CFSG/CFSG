module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.RestrictedRelations
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.ProjectiveData

/-!+# Triangular words on the actual simple differential quotient

This module fixes the operators and word spans used in the highest-line
argument. The negative image space is the sum of the images of **all** negative
root operators. Uniform vanishing of sufficiently long negative words makes
this space proper: otherwise vanishing descends one word length at a time,
eventually forcing the identity operator to vanish.

Triangular words have negative factors on the left, simple Cartan commutators
in the middle, and positive factors on the right. Their spanning property and
Cartan stability of the negative image space are separate mathematical inputs;
neither is part of the definitions or inferred from individual square-zero
relations.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §2, especially Curtis 2.7 and the monomials (2.8);
DOI 10.1017/S0027763000011016.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

namespace HighestLine

/-- Every positive root, with no root-length restriction. -/
abbrev PositiveRoot := {r : F4Chevalley.Root // typeF4RootPairing_base.IsPos r}

/-- Every negative root, with no root-length restriction. -/
abbrev NegativeRoot := {r : F4Chevalley.Root // ¬ typeF4RootPairing_base.IsPos r}

end HighestLine

namespace SimpleCyclicQuotient
open HighestLine
variable {B : AlgebraicFactor F} {v : B.Space} (Q : SimpleCyclicQuotient B v)
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- The actual simple-coroot commutator on the quotient. -/
@[expose] def cartanOperator (i : Fin 4) : Module.End F Q.Space :=
  Q.operator (typeF4SimpleRootIndex i) * Q.operator (-typeF4SimpleRootIndex i) -
    Q.operator (-typeF4SimpleRootIndex i) * Q.operator (typeF4SimpleRootIndex i)

/-- The span of all negative-root images, on the quotient itself. -/
@[expose] def negativeImage : Submodule F Q.Space :=
  ⨆ r : NegativeRoot, LinearMap.range (Q.operator r.val)

/-- Every negative-root image belongs to the negative image space. -/
theorem operator_mem_negativeImage (r : NegativeRoot) (w : Q.Space) :
    Q.operator r.val w ∈ Q.negativeImage :=
  Submodule.mem_iSup_of_mem r ⟨w, rfl⟩

/-- A triangular word in the canonical quotient operators. -/
@[expose] def triangularWord (l : List NegativeRoot) (h : List (Fin 4))
    (r : List PositiveRoot) : Module.End F Q.Space :=
  (l.map fun s => Q.operator s.val).prod * (h.map Q.cartanOperator).prod *
    (r.map fun s => Q.operator s.val).prod

/-- The linear span of triangular words; equality to the full algebra is not assumed. -/
@[expose] def triangularSpan : Submodule F (Module.End F Q.Space) :=
  Submodule.span F {a | ∃ l h r, Q.triangularWord l h r = a}

/-- Joint nilpotence makes the negative image space proper. The premise is
uniform vanishing of words, not separate nilpotence of their letters. -/
theorem negativeImage_ne_top_of_word_vanishing
    (hvanish : ∃ N : ℕ, ∀ l : List NegativeRoot, l.length = N →
      (l.map fun r => Q.operator r.val).prod = 0) : Q.negativeImage ≠ ⊤ := by
  intro htop
  have descend : ∀ N : ℕ, (∀ l : List NegativeRoot, l.length = N →
      (l.map fun r => Q.operator r.val).prod = 0) → False := by
    intro N
    induction N with
    | zero =>
      intro h
      have hz := congrArg (fun a : Module.End F Q.Space => a Q.highestVector)
        (h [] rfl)
      exact Q.highestVector_ne_zero (by simpa using hz)
    | succ N ih =>
      intro h
      apply ih
      intro l hl
      apply LinearMap.ker_eq_top.mp
      apply top_unique
      have hle : Q.negativeImage ≤ LinearMap.ker
          ((l.map fun r => Q.operator r.val).prod) := by
        apply iSup_le
        intro r x hx
        obtain ⟨w, rfl⟩ := hx
        have hz := congrArg (fun a : Module.End F Q.Space => a w)
          (h (l ++ [r]) (by simp [hl]))
        simpa only [LinearMap.mem_ker, List.map_append, List.map_cons, List.map_nil,
          List.prod_append, List.prod_cons, List.prod_nil, mul_one,
          Module.End.mul_apply, LinearMap.zero_apply] using hz
      simpa only [htop] using hle
  obtain ⟨N, hN⟩ := hvanish
  exact descend N hN

/-- Every vector is the action of one root-algebra element on the distinguished vector. -/
theorem exists_rootAction_highest (w : Q.Space) :
    ∃ a : rootAlgebra B, Q.rootAction a Q.highestVector = w := by
  obtain ⟨z, rfl⟩ := Q.surjective w
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp z.property
  have hz : (cyclicSubmodule B v).module.smul a (cyclicVector B v) = z :=
    Subtype.ext ha
  refine ⟨a, ?_⟩
  change a • Q.projection (cyclicVector B v) = Q.projection z
  rw [← Q.projection.map_smul]
  exact congrArg Q.projection hz

end SimpleCyclicQuotient
end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
