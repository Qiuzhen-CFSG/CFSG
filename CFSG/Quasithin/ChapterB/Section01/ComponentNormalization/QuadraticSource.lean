module

public import Theory.Representation.QuadraticFourGroup.Recognition.PairRecognition
public import Theory.Representation.QuadraticFourGroup.CubicSections
public import Theory.Representation.QuadraticFourGroup.TensorClassification
public import FeitThompson.FinalTheorem

/-!
# The genuine quadratic four-group source theorem

The diagonal argument gives odd transpositions in the faithful irreducible
image. Feit--Thompson supplies an involution in the simple component quotient,
and the single-pair recognition gives the exact two-core quotient. The proved
irreducible-image reduction returns to the original component orbit. Every
nontrivial irreducible section descends through that quotient; its cubic fixed
spaces vanish on both factors, so scalar descent gives an actual tensor over
the common binary extension field.

Source: GLS volume 2, Chapter G, Theorem 25.14, Steps 2--5 and its remarks.
The tensor field is the extension field, as in the theorem statement.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentNormalization.QuadraticSource
open Representation.QuadraticFourGroup
universe u v w

/-- All hypotheses of the faithful irreducible recognition are discharged. -/
theorem irreducibleRecognition : IrreducibleRecognition.{v} := by
  intro G V _ _ _ _ _ ρ _ L B a h hgen hcore
  have hodd : HasOddTranspositions a := h.hasOddTranspositions_of_sup_eq_top hgen hcore
  obtain ⟨t, ht⟩ := h.quotient_involution_of_odd_solvable
    (odd_order_theorem (L ⧸ center L))
  exact h.twoFactorModel_of_oddTranspositions hodd t ht

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

/-- The actual orbit quotient is a product of two genuine PSL₂ factors. -/
theorem twoFactorModel (h : Hypotheses ρ L B a) :
    Nonempty (TwoFactorModel (componentOrbit L B)) :=
  h.twoFactorModel_of_irreducible irreducibleRecognition
    (fun n _ => factor_oddSylow_isCyclic n)

/-- The section conclusion retains the literal model projection. -/
theorem naturalTensorSection (h : Hypotheses ρ L B a)
    (M : TwoFactorModel (componentOrbit L B))
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (componentOrbit L B) W)
    (hs : IsIrreducibleSection (ρ.comp (componentOrbit L B).subtype) σ)
    (hn : ¬ σ.IsTrivial) : IsNaturalTensorAlong M.projection σ := by
  obtain ⟨σbar, hc, hi, _, _, hfirst, hsecond⟩ :=
    exists_cubic_fixed_free_section h M σ hs hn
  let := hi
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, ⟨φ⟩⟩ :=
    TensorClassification.isNaturalTensorAlong_of_cubicFreeOnFactors σbar M.one_lt
      ⟨hfirst,hsecond⟩
  refine ⟨τ₁, τ₂, hτ₁, hτ₂, ⟨Representation.Equiv.mk φ.toLinearEquiv ?_⟩⟩
  intro g
  rw [← hc]
  exact φ.isIntertwining' (M.projection g)

/-- GLS2 25.14, including all nontrivial composition factors and the original
component-orbit quotient. Trivial sections are explicitly retained. -/
theorem classification (h : Hypotheses ρ L B a) :
    ∃ M : TwoFactorModel (componentOrbit L B),
      ∀ (W : Type w) [AddCommGroup W] [Module (ZMod 2) W]
        [FiniteDimensional (ZMod 2) W]
        (σ : Representation (ZMod 2) (componentOrbit L B) W),
        IsIrreducibleSection (ρ.comp (componentOrbit L B).subtype) σ →
          σ.IsTrivial ∨ IsNaturalTensorAlong M.projection σ := by
  obtain ⟨M⟩ := twoFactorModel h
  refine ⟨M, fun W _ _ _ σ hs => ?_⟩
  by_cases hn : σ.IsTrivial
  · exact Or.inl hn
  · exact Or.inr (naturalTensorSection h M σ hs hn)

end CFSG.Quasithin.ChapterB.ComponentNormalization.QuadraticSource
