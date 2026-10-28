module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.NormFree
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointFixed
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.Restriction
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedHeart
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedQuotients

/-!
# The ordinary binary M₁₂ degree gap

The conclusion is degree at most ten for a faithful irreducible
binary M₁₂ representation of degree at most 24. Choose a simple submodule
of its actual M₁₁ point restriction. The line branch gives a quotient of
the twelve-point augmentation core modulo constants, hence degree at most
ten. The ten-dimensional branch gives a surjection from the literal induced
point representation by the existing marked M₁₁ recognition and Frobenius
reciprocity. The order-eleven bound supplies nontriviality in the line branch.

The independently proved M₁₁ simple degrees through 24 and small simple
quotients of the induced point module discharge both branches. Their native
filtrations and finite matrix certificates establish the binary degree bounds
without absolute irreducibility or semisimplicity of the restriction.
The conditional reductions remain available alongside the final degree gap.

Source context: Aschbacher–Smith Chapter K, printed pp.451 and 457, invokes
Guralnick–Malle, Classification of 2F-modules I, Theorem 6.6/Table 6.7, under
cubic-ratio hypotheses. The ordinary gap here is a separate sufficient input
to that source reduction; James, J. Algebra 27 (1973), 57–111, is the intrinsic
modular-character reference. No citation is used as a Lean proof.
-/

public section
namespace Representation.MathieuSmall.M12DegreeGap
open Sporadic.Mathieu M12Recognition
open M12Recognition.PointClassification.NormalizedInvolution

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The degree window reduces to a genuine simple quotient of the induced point module.
The point simple-degree classification is still an explicit input. -/
theorem finrank_le_ten_or_inducedHeart_quotient_of_point_degrees
    (σ : Representation (ZMod 2) M12 V) (hf : Function.Injective σ)
    [σ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 24)
    (hlocal : ∀ S : Subrepresentation (σ.comp pointEmbedding),
      S.toRepresentation.IsIrreducible → Module.finrank (ZMod 2) S.toSubmodule ≤ 24 →
      Module.finrank (ZMod 2) S.toSubmodule = 1 ∨
        Module.finrank (ZMod 2) S.toSubmodule = 10) :
    Module.finrank (ZMod 2) V ≤ 10 ∨
      ∃ f : inducedHeart.IntertwiningMap σ, Function.Surjective f := by
  have hlo := BinaryPrimeDegree.orderOf_le_finrank σ hf
    (by decide : Nat.Prime 11) (by decide : 11 ≠ 2) (by rw [m12_order]; norm_num)
  rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hlo
  rcases point_fixed_or_point_map_of_simple_degrees σ
    (fun S hS => hlocal S hS ((Submodule.finrank_le S.toSubmodule).trans hd)) with h | ⟨f, hf⟩
  · exact Or.inl (finrank_le_ten_of_point_fixed σ (by omega) h)
  · exact Or.inr ⟨inducePointMap σ f, inducePointMap_surjective σ f hf⟩

/-- Concrete application of the norm-zero classification to every simple submodule
of the literal M₁₁ restriction. Only the line-or-zero-norm alternative remains an input. -/
theorem finrank_le_ten_or_inducedHeart_quotient_of_point_norms
    (σ : Representation (ZMod 2) M12 V) (hf : Function.Injective σ)
    [σ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 24)
    (hlocal : ∀ S : Subrepresentation (σ.comp pointEmbedding),
      S.toRepresentation.IsIrreducible → Module.finrank (ZMod 2) S.toSubmodule ≤ 24 →
      Module.finrank (ZMod 2) S.toSubmodule = 1 ∨
        S.toRepresentation.asAlgebraHom elevenNorm = 0) :
    Module.finrank (ZMod 2) V ≤ 10 ∨
      ∃ f : inducedHeart.IntertwiningMap σ, Function.Surjective f := by
  apply finrank_le_ten_or_inducedHeart_quotient_of_point_degrees σ hf hd
  intro S hS hdim
  rcases hlocal S hS hdim with h | h
  · exact Or.inl h
  · let : S.toRepresentation.IsIrreducible := hS
    exact Or.inr (finrank_eq_ten_of_elevenNorm_eq_zero S.toRepresentation h)

/-- A faithful irreducible binary M₁₂ module of dimension at most 24 has
dimension at most ten. Both the point simple-degree and induced-quotient
inputs are discharged; no cubic or absolute-irreducibility premise is used. -/
theorem finrank_le_ten
    (σ : Representation (ZMod 2) M12 V) (hf : Function.Injective σ)
    [σ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 24) :
    Module.finrank (ZMod 2) V ≤ 10 := by
  have hlocal (S : Subrepresentation (σ.comp pointEmbedding))
      (hS : S.toRepresentation.IsIrreducible)
      (hSdim : Module.finrank (ZMod 2) S.toSubmodule ≤ 24) :
      Module.finrank (ZMod 2) S.toSubmodule = 1 ∨
        Module.finrank (ZMod 2) S.toSubmodule = 10 := by
    let : S.toRepresentation.IsIrreducible := hS
    exact PointSimpleDegrees.finrank_eq_one_or_ten S.toRepresentation hSdim
  rcases finrank_le_ten_or_inducedHeart_quotient_of_point_degrees σ hf hd hlocal with
    h | ⟨q, hq⟩
  · exact h
  · exact InducedQuotients.finrank_le_ten σ hd q hq

end Representation.MathieuSmall.M12DegreeGap
