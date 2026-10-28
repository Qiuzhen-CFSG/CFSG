module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSeed.Transport
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalHyperplanes
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualAction

/-!
# The covered seed action on the genuine natural flag

The actual permutation image contains A₆ by compatibility with the hexacode
cover. Its Sylow-stable natural hyperplane is the perpendicular of its
Sylow-stable point. The point stabilizer's two-residual preserves this
perpendicular and generates it modulo the point: the concrete calculation
uses the embedded A₄ residual on the augmentation quotient. Equivariant
preimage transport proves the corresponding assertions for L₁ on V₃/V₁.

The exact earlier factorization L₁ = L₁,+ L₀ removes L₀, which centralizes V.
The final `seed_action` theorem discharges both geometric model premises
of the intermediate transport lemmas. Its only additional source input is
13.2.2(3), explicitly named as the factorization hypothesis. Normalization
is proved separately without that input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and 13.2.2(3), printed p.877; 13.8.16, pp.952–953;
and the covered case of 13.8.21(1), printed p.957.
-/

public section
noncomputable section
open Subgroup Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup
variable {G : Type*} [Group G] {L T V V₁ V₃ : Subgroup G}
  (d : NaturalSetup L T V V₁ V₃)
include d

/-- The earlier centralizing factor may be removed after normalization is proved. -/
theorem one_seed_commutator_eq_plus
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hplus : plus L T V₁ ≤ normalizer (V₃ : Set G)) :
    ⁅one L T V₁, V₃⁆ = ⁅plus L T V₁, V₃⁆ := by
  have hz := d.zero_centralizes.trans (centralizer_le d.seed_le)
  have he := commutator_eq_of_centralizing_sup
    (show zero L ⊔ plus L T V₁ = one L T V₁ by rw [sup_comm]; exact hfactor.symm)
    hz hplus
  rw [commutator_comm V₃ (plus L T V₁), commutator_comm V₃ (one L T V₁)] at he
  exact he.symm

variable [Finite G]

/-- Conditional transport of the concrete residual flag calculation. The two model
premises concern the literal six-letter action and are discharged in `seed_action`.
The factorization is precisely the input 13.2.2(3). -/
theorem seed_action_of_residual_flag
    (hstable : residual (d.permutation.range ⊓ subspaceStabilizer naturalAction d.point) ≤
      subspaceStabilizer naturalAction d.hyperplane)
    (hgen : d.hyperplane ≤ subspaceCommutator naturalAction d.hyperplane
      (residual (d.permutation.range ⊓ subspaceStabilizer naturalAction d.point)) ⊔ d.point)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    plus L T V₁ ≤ normalizer (V₃ : Set G) ∧ V₃ ≤ ⁅plus L T V₁, V₃⁆ ⊔ V₁ := by
  have hnorm : one L T V₁ ≤ normalizer (V₃ : Set G) :=
    d.normalizes_seed_of_image _ ((one_le L T V₁).trans inf_le_left)
      (d.one_image ▸ hstable)
  have hp : plus L T V₁ ≤ normalizer (V₃ : Set G) :=
    (plus_le_one L T V₁ d.line_stable).trans hnorm
  refine ⟨hp, ?_⟩
  have h := d.seed_le_commutator_sup_of_displacement (one L T V₁) (d.one_image ▸ hgen)
  rwa [d.one_seed_commutator_eq_plus hfactor hp] at h

omit [Finite G] in
/-- The geometric perpendicular identification suffices for normalization. -/
theorem plus_normalizes_seed_of_perpendicular
    (hperp : d.hyperplane = form.orthogonal d.point) :
    plus L T V₁ ≤ normalizer (V₃ : Set G) := by
  have hp : d.permutationImage (parabolic L T V₁) ≤
      subspaceStabilizer naturalAction d.hyperplane := by
    rw [d.parabolic_image, hperp]
    exact inf_le_right.trans (stabilizer_le_orthogonal_stabilizer d.point)
  exact ((plus_le_one L T V₁ d.line_stable).trans (one_le L T V₁)).trans
    (d.normalizes_seed_of_image _ inf_le_left hp)

/-- Assembly from the perpendicular marking and the concrete residual displacement.
The factorization is precisely the earlier 13.2.2(3) input. -/
theorem seed_action_of_perpendicular
    (hperp : d.hyperplane = form.orthogonal d.point)
    (hgen : form.orthogonal d.point ≤ subspaceCommutator naturalAction
      (form.orthogonal d.point)
      (residual (d.permutation.range ⊓ subspaceStabilizer naturalAction d.point)) ⊔ d.point)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    plus L T V₁ ≤ normalizer (V₃ : Set G) ∧ V₃ ≤ ⁅plus L T V₁, V₃⁆ ⊔ V₁ := by
  apply d.seed_action_of_residual_flag _ _ hfactor
  · rw [hperp]
    exact (residual_le _).trans (inf_le_right.trans
      (stabilizer_le_orthogonal_stabilizer d.point))
  · simpa only [hperp] using hgen

/-- The supplied Sylow subgroup identifies the actual natural hyperplane with the
perpendicular of the point. No choice of canonical coordinates is assumed. -/
theorem hyperplane_eq_orthogonal : d.hyperplane = form.orthogonal d.point := by
  obtain ⟨Q, hQ⟩ := d.image_sylow
  apply Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalHyperplanes.sylow_invariant_hyperplane_eq_orthogonal
    d.permutation.range d.alternating_le_range Q d.point d.hyperplane
    d.point_dim d.hyperplane_dim
  · rw [hQ]
    exact d.sylow_flag_stable.1
  · rw [hQ]
    exact d.sylow_flag_stable.2

/-- The covered residual L₁,+ normalizes the actual seed V₃. -/
theorem plus_normalizes_seed : plus L T V₁ ≤ normalizer (V₃ : Set G) :=
  d.plus_normalizes_seed_of_perpendicular d.hyperplane_eq_orthogonal

/-- The genuine natural action gives normalization and generation of V₃/V₁ by
L₁,+. The only additional input is the earlier factorization 13.2.2(3). -/
theorem seed_action (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    plus L T V₁ ≤ normalizer (V₃ : Set G) ∧ V₃ ≤ ⁅plus L T V₁, V₃⁆ ⊔ V₁ := by
  apply d.seed_action_of_perpendicular d.hyperplane_eq_orthogonal _ hfactor
  exact Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualAction.point_residual_displacement
    d.permutation.range d.alternating_le_range d.point d.point_dim

/-- Commutators with L₁,+ generate the seed modulo its full point preimage. -/
theorem seed_le_plus_commutator_sup
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    V₃ ≤ ⁅plus L T V₁, V₃⁆ ⊔ V₁ :=
  (d.seed_action hfactor).2

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup
end
