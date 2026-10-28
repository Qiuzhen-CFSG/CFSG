module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.LocalActions.Semilinear.Transport
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery

/-!
# Common Ree block parameters without simplicity assumptions

Preservation of the four full signed simple blocks suffices to recover a
common field automorphism and a twist-compatible diagonal action when `m ≥ 1`.
The additive coordinates on the linear blocks, their opposite-root braid and
Weyl conjugation identities give scaled multiplication and inverse scales.
Their action on the Suzuki coordinates forces the same field map, vanishing
central displacement, and inverse scales on the two signs. Complete coordinate
coverage extends these formulas to every element of all four intersections.
The inverse-Cartan solution then gives compatible torus parameters.

We assemble the elementary results of `FieldRecovery` directly, without its
wrapper's simplicity and perfectness assumptions. The canonical application
retains the supplied odd-index, seed-generation and unipotent-pair hypotheses;
the coordinate calculation itself only needs simple-block preservation.
Realization of the diagonal matrix in the fixed group belongs to the caller.

Source: GLS3, Table 2.4, §2.4 and 2.5.1(b,c), and Steinberg, Theorem 36,
in `refs/KGroup/GLS3/chapter2.tex` and `refs/KGroup/GLS3/Chapter2St1.tex`.
The matrix convention is `T⁻¹ * σ(x) * T`.
-/

public noncomputable section

namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters
open FieldRecovery
variable {m : ℕ}

/-- Recover the common field map from block preservation alone, including the
central Suzuki parameter and both opposite signs on the full intersections. -/
theorem exists_torusFieldAction_of_preservesSimpleBlocks (hm : 1 ≤ m)
    (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) :
    ∃ (u : TorusParameters m) (σ : CoefficientField m ≃+* CoefficientField m),
      TwistCompatible u ∧ HasTorusFieldAction d a u σ := by
  let C := suzukiCoordinates d
  obtain ⟨b, σ, hlin⟩ := exists_signedLinearAction_of_preservesSimpleBlocks d a hb
  obtain ⟨c, hsu⟩ := exists_pureSuzukiAction hm d a hb C b σ hlin
  exact exists_torusFieldAction_of_parameter_relations d a hb C
    ⟨c, parameterRelations_of_signed_actions d a hb C b c σ hlin hsu⟩
    torusWordLaws

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters

namespace ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions.Semilinear
open LocalBlockInput.PairRigidity.BlockParameters
variable {m : ℕ}

/-- The actual model automorphism has compatible torus-field parameters in the
canonical fixed-group coordinates. This discharges the parameter-recovery
premise of `common_field_of_recovery_and_realization` at the canonical input;
fixed-torus realization remains a separate obligation. -/
theorem exists_canonical_torusFieldAction (hm : 1 ≤ m)
    (_hindex : Odd (unipotent m).index)
    (_hgen : seed m .suzuki ⊔ seed m .linear = ⊤)
    (c : MulAut (Model m)) (_hp : PreservesUnipotentPair m c)
    (hc : PreservesSimpleBlocks m c) :
    let d := canonicalLocalBlockInput m
    ∃ (u : TorusParameters m) (σ : CoefficientField m ≃+* CoefficientField m),
      TwistCompatible u ∧ HasTorusFieldAction d (pullback d c) u σ :=
  exists_torusFieldAction_of_preservesSimpleBlocks hm (canonicalLocalBlockInput m)
    (pullback (canonicalLocalBlockInput m) c)
    (pullback_preservesSimpleBlocks (canonicalLocalBlockInput m) c hc)

end ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions.Semilinear

end
