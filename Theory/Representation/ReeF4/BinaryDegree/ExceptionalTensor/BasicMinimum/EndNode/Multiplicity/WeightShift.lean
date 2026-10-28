module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.Multiplicity.TorusCovariance

/-!
# Full weight shifts under the actual lowering operators

Comparing first coefficients in the coroot covariance equation subtracts the
entire Cartan row from a vector's integral weight. The rows of the adjacent
short roots sum to `(0,-1,1,1)`, so both orders of lowering a vector of this
weight belong to the full four-coroot zero weight space.

The remaining rank-one coefficient contract is stated separately. It asks
only for raising after lowering on highest vectors of exponent one or two;
it contains no weight-space dimension or independence assertion.

Source: GLS3, Sections 1.12 and 1.14.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.EndNode.Multiplicity
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- Only the rank-one highest-string coefficients one and two are needed. -/
@[expose] def RankOneHighestCoefficient (B : AlgebraicFactor F) : Prop :=
  ∀ (i : Fin 4), (i = 2 ∨ i = 3) → ∀ (n : ℕ), (n = 1 ∨ n = 2) → ∀ v : B.Space,
    (∀ a : F, (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) a) :
      Module.End F B.Space) v = v) →
    (∀ t : Fˣ, (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = (t : F) ^ n • v) →
    raising B i (lowering B i v) = (n : F) • v

theorem lowering_mem_corootWeightSpace
    (B : AlgebraicFactor F) (i : Fin 4)
    (μ : Weight) (v : B.Space) (hv : v ∈ corootWeightSpace B μ) :
    lowering B i v ∈ corootWeightSpace B (μ - typeF4CartanMatrix i) := by
  apply (mem_corootWeightSpace B _ _).mpr
  intro j t
  let A : Module.End F B.Space :=
    B.action.action (algebraicCorootElement (typeF4SimpleRootIndex j) t)
  have he := rootOperator_intertwine B (-typeF4SimpleRootIndex i)
    (-typeF4SimpleRootIndex i) A A ((t : F) ^ (-typeF4CartanMatrix i j)) (by
      intro a w
      have hh := congrArg (fun g => (B.action.action g : Module.End F B.Space) w)
        (coroot_negativeSimple_commute i j t a)
      simpa only [map_mul, Units.val_mul, Module.End.mul_apply, A] using hh)
  have he' := congrArg (fun L : Module.End F B.Space => L v) he
  have ht := (mem_corootWeightSpace B μ v).mp hv j t
  change A (lowering B i v) =
    ((t : F) ^ (-typeF4CartanMatrix i j)) • lowering B i (A v) at he'
  change A v = _ at ht
  rw [ht, map_smul, smul_smul] at he'
  convert he' using 1
  simp only [Pi.sub_apply, sub_eq_add_neg, zpow_add₀ t.ne_zero, mul_comm]

theorem shortA2Weight_sub_rows :
    shortA2Weight - typeF4CartanMatrix 3 - typeF4CartanMatrix 2 = 0 ∧
    shortA2Weight - typeF4CartanMatrix 2 - typeF4CartanMatrix 3 = 0 := by
  decide

theorem lowerings_mem_zero
    (B : AlgebraicFactor F) (v : B.Space) (hv : v ∈ corootWeightSpace B shortA2Weight) :
    lowering B 2 (lowering B 3 v) ∈ corootWeightSpace B 0 ∧
    lowering B 3 (lowering B 2 v) ∈ corootWeightSpace B 0 := by
  constructor
  · have h := lowering_mem_corootWeightSpace B 2 _ _
      (lowering_mem_corootWeightSpace B 3 _ _ hv)
    rwa [shortA2Weight_sub_rows.1] at h
  · have h := lowering_mem_corootWeightSpace B 3 _ _
      (lowering_mem_corootWeightSpace B 2 _ _ hv)
    rwa [shortA2Weight_sub_rows.2] at h

end
end ReeF4.BinaryDegree.ExceptionalTensor.EndNode.Multiplicity
