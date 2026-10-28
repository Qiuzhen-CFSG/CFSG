module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Basic
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Automorphisms
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.LinearGeometry.Coordinates
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.LinearGeometry.Torus
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.LinearGeometry.FieldAction

/-!
# The linear branch of the Section 16 model geometry

An actual equivalence with PSL₂(2ⁿ) identifies every Sylow two-subgroup with
the additive field. Its first omega subgroup and center are the whole Sylow
subgroup. The marked Borel intersection is a cyclic torus of order 2ⁿ − 1,
inverted by the chosen outside involution and equal to its commutator with it.
The root subgroup and that involution generate the whole model; the source's
three marked generators give the same subgroup.

The common centralizer of the two marked involutions is trivial. Thus an inner
automorphism fixing both is the identity. An arbitrary outer square-one
automorphism preserving the Borel and fixing the outside involution acts on
the marked torus by x ↦ x^(2ᵐ), where n = 2m and m > 0. A fixed involution s
also admits an actual witness g⁻¹a(g) = s.

These are intrinsic statements, with no ambient product-disconnection or
recognition premises. Their consumers are GLS IV, Chapter 2, Lemma 16.2 and
Proposition 16.5; their source is Chapter 4, Lemmas 3.2(b–e,h) and 3.4(a,c,f).
Assembly with the other model families remains in `ModelGeometry.lean`.
-/

namespace BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry
open Subgroup _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {n : ℕ}

/-- The exact ambient omega/center statement for an arbitrary Sylow subgroup
of the actual binary linear model, including its elementary structure and order. -/
public theorem omega_geometry (hn : 0 < n) (e : G ≃* PSL2BinaryMatrixGroup n)
    (P : Sylow 2 G) :
    omegaOneAmbient (P : Subgroup G) = (P : Subgroup G) ∧
      omegaOneAmbient (P : Subgroup G) = (center P).map (P : Subgroup G).subtype ∧
      IsElementaryAbelian 2 (omegaOneAmbient (P : Subgroup G)) ∧
      Nat.card (omegaOneAmbient (P : Subgroup G)) = 2 ^ n := by
  have hω := sylow_omega_eq e P
  refine ⟨hω, hω.trans (sylow_center_eq e P).symm, ?_, ?_⟩
  · rw [hω]
    exact sylow_elementary e P
  · rw [hω]
    exact sylow_card hn e P

end BenderSuzuki.ZD.RankOneModelGeometry.LinearGeometry
