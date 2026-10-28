module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Natural
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections

/-!
# Natural source contradictions after actual Borel centralization

Source: Aschbacher–Smith, proof of 13.8.20(a), printed pp.954–955.
The actual Borel centralization supplies the seed commutator identity.
The marked residual and the one/two-layer fixed-space calculations then
contradict the genuine action kernel on U_H/V₁. The L₂ argument works in
both parities; the L₃ layers retain independent natural/dual orientations.

Centralization is an explicit intermediate theorem argument. Its producer
belongs to the source-alternative/field assembly, where it must be discharged.
No covered centralizer formula or old local index is used here.
-/

@[expose] public section
open Subgroup Representation Representation.HigherFieldBorelFixedSpaces
open Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

variable {G : Type*} [Group G] [Finite G]
  (H K V V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (hKH : K ≤ H) (hVH : V₃ ≤ H) (hV₃ : V₃ ≤ V)
  (hHK : H ≤ normalizer K) (hHV₁ : H ≤ normalizer V₁)
  (hkernel : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
  (hne : Source.starImage H K ≠ ⊥)
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (hρ : SeedAction.IsConjugation H V₃ V₁ ρ)
  (B₀ : Subgroup (Source.Hstar H)) (hB₀ : B₀ ≤ Source.starImage H K)

local notation "B" => borelResidual (borelLift H K hKH B₀)
local notation "κ" => MonoidHom.comp ρ (Subgroup.subtype (Source.starImage H K))
local notation "Bstar" => Subgroup.subgroupOf (Source.starImage H B) (Source.starImage H K)

include hVH hV₃ hHK hHV₁ hkernel hne hρ hB₀ in
/-- The L₂ natural branch, in either field parity. -/
theorem sl2_natural_impossible {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n) (e : Source.starImage H K ≃* SL(2,F))
    (hmark : (B₀.subgroupOf (Source.starImage H K)).map e.toMonoidHom =
      Matrix.SpecialLinearGroup.rankOneBorel F)
    (hc : B ≤ centralizer (V : Set G))
    (C W : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))
    (hcentral : C ≤ Representation.invariants κ)
    (hquot : ∀ g u, κ g u - u ∈ W)
    (layer : NaturalLayers.TensorLayer κ (binaryNatural 2) e C W) : False := by
  exact NaturalBranches.sl2_natural_impossible H K V₃ V₁ B hKH hVH hHK hHV₁
    hkernel hne ρ hρ (seed_commutator_of_borel_centralizes B V V₃ V₁ hV₃ hc)
    hn hF e (lifted_borel_residual_marking H K hKH B₀ hB₀ e _ hmark)
    C W hcentral hquot layer

include hVH hV₃ hHK hHV₁ hkernel hne hρ hB₀ in
/-- One natural or dual-natural L₃ layer. -/
theorem psl3_odd_one_layer_impossible
    {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    {n : ℕ} (hn : 1 < n) (hodd : Odd n) (hF : Nat.card F = 2 ^ n)
    (e : Source.starImage H K ≃* PSL(3,F))
    (hmark : (B₀.subgroupOf (Source.starImage H K)).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F)
    (hc : B ≤ centralizer (V : Set G))
    (σ : Representation (ZMod 2) PSL(3,F) N) (hσ : IsProjectiveNaturalOrDual hodd hF σ)
    (C W : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))
    (hcentral : C ≤ Representation.invariants κ)
    (hquot : ∀ g u, κ g u - u ∈ W)
    (layer : NaturalLayers.TensorLayer κ σ e C W) : False := by
  have hf := NaturalLayers.fixedSpace_of_one_layer κ σ e Bstar _
    (lifted_borel_residual_marking H K hKH B₀ hB₀ e _ hmark)
    (psl3_twoResidual_odd_index hn hF) C W hcentral hquot layer
    (projectiveNaturalOrDual_fixedSpace hn hodd hF σ hσ)
  exact SeedAction.contradiction_of_star_fixedSpace H V₃ V₁ K B hKH hVH hHK hHV₁
    hkernel hne ρ hρ (seed_commutator_of_borel_centralizes B V V₃ V₁ hV₃ hc) hf.le

include hVH hV₃ hHK hHV₁ hkernel hne hρ hB₀ in
/-- Two independently oriented natural or dual-natural L₃ layers. -/
theorem psl3_odd_two_layers_impossible
    {N N' : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    [AddCommGroup N'] [Module (ZMod 2) N']
    {n : ℕ} (hn : 1 < n) (hodd : Odd n) (hF : Nat.card F = 2 ^ n)
    (e : Source.starImage H K ≃* PSL(3,F))
    (hmark : (B₀.subgroupOf (Source.starImage H K)).map e.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F)
    (hc : B ≤ centralizer (V : Set G))
    (σ : Representation (ZMod 2) PSL(3,F) N) (hσ : IsProjectiveNaturalOrDual hodd hF σ)
    (τ : Representation (ZMod 2) PSL(3,F) N') (hτ : IsProjectiveNaturalOrDual hodd hF τ)
    (C D W : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))
    (hcentral : C ≤ Representation.invariants κ)
    (hquot : ∀ g u, κ g u - u ∈ W)
    (first : NaturalLayers.TensorLayer κ σ e C D)
    (second : NaturalLayers.TensorLayer κ τ e D W) : False := by
  have hf := NaturalLayers.fixedSpace_of_two_layers κ σ τ e Bstar _
    (lifted_borel_residual_marking H K hKH B₀ hB₀ e _ hmark)
    (psl3_twoResidual_odd_index hn hF) C D W hcentral hquot first second
    (projectiveNaturalOrDual_fixedSpace hn hodd hF σ hσ)
    (projectiveNaturalOrDual_fixedSpace hn hodd hF τ hτ)
  exact SeedAction.contradiction_of_star_fixedSpace H V₃ V₁ K B hKH hVH hHK hHV₁
    hkernel hne ρ hρ (seed_commutator_of_borel_centralizes B V V₃ V₁ hV₃ hc) hf.le

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation

end
