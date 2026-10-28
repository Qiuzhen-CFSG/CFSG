module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.NaturalLayers

/-!
# The natural-module contradictions in 13.8.20

Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955
(combined manuscript, 1 March 2004), external-X alternative (a).

The actor is the actual subgroup K* of H/O₂(H), and the module is the
literal source quotient U_H/V₁. Concrete Borel and equivariant tensor
section coordinates imply C_U(B*)=C_U(K*), including one or two noncentral
layers with central sections. SeedAction then turns the B-centralized seed
into the forbidden containment K≤O₂(H).

The earlier FF classification must still supply the section coordinates,
and the local B_C calculation must supply centralization of V₃ by B.
These conditional branch theorems do not assume either fixed-space equality
or the external-X contradiction. They are the endpoints used after those
source obligations are discharged.
-/

public section
open Subgroup Representation Representation.HigherFieldBorelFixedSpaces
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.NaturalBranches
variable {G : Type*} [Group G] (H K V₃ V₁ B : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (hKH : K ≤ H) (hVH : V₃ ≤ H)
  (hHK : H ≤ normalizer K) (hHV₁ : H ≤ normalizer V₁)
  (hkernel : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
  (hne : Source.starImage H K ≠ ⊥)
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (hρ : SeedAction.IsConjugation H V₃ V₁ ρ) (hseed : ⁅V₃, B⁆ ≤ V₁)

local notation "κ" => MonoidHom.comp ρ (Subgroup.subtype (Source.starImage H K))
local notation "Bstar" => Subgroup.subgroupOf (Source.starImage H B) (Source.starImage H K)

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

include hKH hVH hHK hHV₁ hkernel hne hρ hseed in
/-- The natural rank-one branch contradicts the source action kernel. -/
theorem sl2_natural_impossible {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : Source.starImage H K ≃* SL(2,F))
    (hB : (Bstar).map e.toMonoidHom =
      twoResidualImage (Matrix.SpecialLinearGroup.rankOneBorel F))
    (C W : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))
    (hcentral : C ≤ Representation.invariants κ)
    (hquot : ∀ (g : Source.starImage H K) (u : SeedAction.Space H V₃ V₁), κ g u - u ∈ W)
    (layer : NaturalLayers.TensorLayer κ (binaryNatural 2) e C W) : False := by
  have hf := NaturalLayers.sl2_one_layer κ hn hF e Bstar hB C W hcentral hquot layer
  exact SeedAction.contradiction_of_star_fixedSpace H V₃ V₁ K B hKH hVH hHK hHV₁
    hkernel hne ρ hρ hseed hf.le

include hKH hVH hHK hHV₁ hkernel hne hρ hseed in
/-- The first odd-degree L₃ case, with a central quotient above one tensor layer. -/
theorem psl3_one_layer_impossible {n : ℕ} (hn : 1 < n) (hodd : Odd n)
    (hF : Nat.card F = 2 ^ n) (e : Source.starImage H K ≃* PSL(3,F))
    (hB : (Bstar).map e.toMonoidHom = twoResidualImage (Matrix.PSL3.LinearThree.borel F))
    (C W : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))
    (hcentral : C ≤ Representation.invariants κ)
    (hquot : ∀ (g : Source.starImage H K) (u : SeedAction.Space H V₃ V₁), κ g u - u ∈ W)
    (layer : NaturalLayers.TensorLayer κ (projectiveBinaryNatural hodd hF) e C W) : False := by
  have hf := NaturalLayers.psl3_one_layer κ hn hodd hF e Bstar hB C W hcentral hquot layer
  exact SeedAction.contradiction_of_star_fixedSpace H V₃ V₁ K B hKH hVH hHK hHV₁
    hkernel hne ρ hρ hseed hf.le

include hKH hVH hHK hHV₁ hkernel hne hρ hseed in
/-- The second odd-degree L₃ case, with both natural tensor layers retained. -/
theorem psl3_two_layers_impossible {n : ℕ} (hn : 1 < n) (hodd : Odd n)
    (hF : Nat.card F = 2 ^ n) (e : Source.starImage H K ≃* PSL(3,F))
    (hB : (Bstar).map e.toMonoidHom = twoResidualImage (Matrix.PSL3.LinearThree.borel F))
    (C D W : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))
    (hcentral : C ≤ Representation.invariants κ)
    (hquot : ∀ (g : Source.starImage H K) (u : SeedAction.Space H V₃ V₁), κ g u - u ∈ W)
    (first : NaturalLayers.TensorLayer κ (projectiveBinaryNatural hodd hF) e C D)
    (second : NaturalLayers.TensorLayer κ (projectiveBinaryNatural hodd hF) e D W) : False := by
  have hf := NaturalLayers.psl3_two_layers κ hn hodd hF e Bstar hB C D W
    hcentral hquot first second
  exact SeedAction.contradiction_of_star_fixedSpace H V₃ V₁ K B hKH hVH hHK hHV₁
    hkernel hne ρ hρ hseed hf.le

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.NaturalBranches
end
