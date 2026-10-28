module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.Induction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.TwoStep.Orientation
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.TwoStep.Sections

/-!
# Splitting the two-factor sections of a supplement

A chief layer Y ⋖ X ∩ W and a supplement X to W give the actual extension
`(X ∩ W)/Y ≤ X/Y`, whose quotient is equivariantly U/W. The chief-factor
hypothesis identifies the kernel, while the specified natural-or-dual head
supplies faithfulness and the common axis. Quadratic action passes to X/Y.
If the kernel is dual, one contragredient change of actor identification
makes it natural and preserves the two possible quotient orientations.
The published two-factor premise then supplies a complement, which lifts
to exactly the local complement required by the finite-length induction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, B.4.9(1), printed p.92, and 13.8.25,
printed p.961. This proves the conditional reduction to B.4.9(1); it does
not prove that splitting premise or assert either final axis exclusion.
-/

public section

universe u v

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions

open Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors

/-- The local complement condition for the finite-length splitting induction.
The two factors are identified inside the actual section X/Y; the kernel
orientation is corrected by the contragredient actor automorphism when needed. -/
theorem two_step_splitting_of_commonAxis
    {H : Type u} {U : Type v} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hsplit : TwoFactorSplitting.{u, v} H)
    (hchief : ChiefFactorsNaturalOrDual ρ eH)
    (W : Subrepresentation ρ) (_hW : IsCoatom W)
    (hhead : IsNaturalOrDual W.quotientRepresentation eH)
    (E : Subgroup H) (hE : Nat.card E = 4) (hq : IsQuadratic ρ E)
    (ha : HasCommonAxis W.quotientRepresentation E)
    (X : Subrepresentation ρ) (hX : X ⊔ W = ⊤)
    (Y : Subrepresentation ρ) (hY : Y ⋖ X ⊓ W) :
    ∃ C : Subrepresentation ρ, C ≤ X ∧ C ⊔ (X ⊓ W) = X ∧ C ⊓ (X ⊓ W) = Y := by
  let hYW := hY.le.trans inf_le_right
  let p := TwoStep.projection ρ W X Y hYW
  let e := TwoStep.kernelEquiv ρ W X Y hYW
  have he : ∀ g k, e.symm (p.ker.toRepresentation g k) =
      sectionRepresentation ρ Y (X ⊓ W) g (e.symm k) := by
    intro g k
    apply e.injective
    rw [e.apply_symm_apply]
    change _ = TwoStep.kernelEquiv ρ W X Y hYW
      (sectionRepresentation ρ Y (X ⊓ W) g (e.symm k))
    rw [TwoStep.kernelEquiv_equivariant]
    exact congrArg (p.ker.toRepresentation g) (e.apply_symm_apply k).symm
  have hK : IsNaturalOrDual p.ker.toRepresentation eH :=
    naturalOrDual_of_equivariant _ _ e.symm he eH (hchief Y (X ⊓ W) hY).1
  have hQ : IsNaturalOrDual p.ker.quotientRepresentation eH :=
    naturalOrDual_of_equivariant _ _ (TwoStep.quotientEquiv ρ W X Y hYW hX)
      (TwoStep.quotientEquiv_equivariant ρ W X Y hYW hX) eH hhead
  have haxis : HasCommonAxis p.ker.quotientRepresentation E :=
    commonAxis_of_equivariant _ _ (TwoStep.quotientEquiv ρ W X Y hYW hX)
      (TwoStep.quotientEquiv_equivariant ρ W X Y hYW hX) E ha
  have hfaith : Function.Injective (sectionRepresentation ρ Y X) :=
    faithful_of_equivariant_surjection _ _ p.toLinearMap
      (TwoStep.projection_surjective ρ W X Y hYW hX) p.isIntertwining
      (naturalOrDual_faithful _ eH hhead)
  obtain ⟨D, hi, hs⟩ := TwoStep.complement_of_naturalOrDual_kernel
    (sectionRepresentation ρ Y X) hsplit eH p.ker hfaith hK hQ E hE
    (quadratic_section ρ E hq Y X) haxis
  exact ⟨TwoStep.lift ρ X Y D, TwoStep.lift_complement ρ W X Y hY.le D hi hs⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions
