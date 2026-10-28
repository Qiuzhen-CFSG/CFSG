module
public import Theory.Representation.Triality.RestrictedWeights.ConcreteInnerSource
public import Theory.Representation.Triality.OuterDisplacement.TensorCoordinates
public import Theory.Representation.Triality.InnerDisplacement.ScalarDescent
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.SourceUniversality

/-!
# Actual absolute triality involution estimate

Extend the original finite-field action to its algebraic closure. Its character
is fixed by the Frobenius of the coefficient field, so the proved native
character-displacement estimate applies. Scalar extension preserves the rank
of the identical displacement operator, giving the exact coefficient multiplier.
The only earlier geometric input is universality, supplied by the shared
semisimple-center theorem. Source: Guralnick--Malle II, Lemma 8.6.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
open Representation.BinaryOffender.NaturalTensor
open Representation
namespace Triality.RestrictedWeights.Concrete
open Triality.SimplyConnected Triality.Standard
universe u
variable {E W : Type u} [Field E] [Finite E] [Algebra (ZMod 2) E] [CharP E 2]
  [AddCommGroup W] [Module E W] [FiniteDimensional E W]

theorem native_absolute_displacement (n : ℕ) (hn : 0<n)
    (hu : IsUniversalVersion (groupVariety (AlgebraicClosure E)))
    (τ : Representation E (BinaryCarrier n hn) W)
    (hi : IsAbsolutelyIrreducible τ) (hf : Function.Injective τ)
    (t : BinaryCarrier n hn) (ht : t≠1) (ht2 : t^2=1) :
    5*n < Module.finrank (ZMod 2) E * Module.finrank E (LinearMap.range (τ t - LinearMap.id)) := by
  let k := AlgebraicClosure E
  let σ := Representation.extendScalars k τ
  let := hi
  have hiσ : IsIrreducible σ := IsAbsolutelyIrreducible.irreducible_of_extension τ k
  have hfσ : Function.Injective σ := (extendScalars_faithful_iff k τ).mp hf
  let : Fintype E := Fintype.ofFinite E
  let : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  have hc : Fintype.card E = 2 ^ Module.finrank (ZMod 2) E := by
    simpa only [ZMod.card] using (Module.card_eq_pow_finrank (K:=ZMod 2) (V:=E))
  have hchar : ∀ g, Representation.character σ g ^ (2^Module.finrank (ZMod 2) E) =
      Representation.character σ g := by
    intro g
    change LinearMap.trace k _ ((τ g).baseChange k) ^ _ = LinearMap.trace k _ ((τ g).baseChange k)
    rw [LinearMap.trace_baseChange, ←map_pow, ←hc, FiniteField.pow_card]
  have ho : orderOf t=2 := orderOf_eq_prime_iff.mpr ⟨ht2,ht⟩
  have hb := native_faithful_character_displacement k hu n hn (FDRep.of σ) hiσ hfσ
    (Module.finrank (ZMod 2) E) Module.finrank_pos hchar t ho
  change 5*n < Module.finrank (ZMod 2) E * Module.finrank k
    (LinearMap.range ((τ t).baseChange k - LinearMap.id)) at hb
  exact hb.trans_eq (congrArg (fun d => Module.finrank (ZMod 2) E * d)
    (Triality.OuterDisplacement.displacement_finrank_baseChange (τ t) k))

/-- All representation inputs in the model absolute bound are discharged. -/
theorem native_absoluteBound_of_semisimple_centers (n : ℕ) (hn : 0<n)
    (hcenter : ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2],
      ∀ (H : Variety k) [AlgebraicGroup H], IsSemisimpleAlgebraicGroup H →
        ∀ T : ClosedSubgroup H, IsMaximalTorus T →
          Subgroup.center (Variety.Point H) ≤ T.toSubgroup) :
    Triality.InnerDisplacement.AbsoluteBound.{0,u} (BinaryCarrier n hn) (5*n) := by
  intro E W _ _ _ _ _ _ _ τ hi hf t ht ht2
  exact native_absolute_displacement n hn
    (source_universal_of_semisimple_centers (AlgebraicClosure E) (hcenter (AlgebraicClosure E)))
    τ hi hf t ht ht2

end Triality.RestrictedWeights.Concrete
