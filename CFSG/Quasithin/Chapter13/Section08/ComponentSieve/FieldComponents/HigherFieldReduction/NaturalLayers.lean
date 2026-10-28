module

public import Theory.Representation.HigherFieldBorelFixedSpaces

/-!
# Natural tensor layers in the external-X branch

Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955
(combined manuscript, 1 March 2004).

A layer carries actual quotient coordinates intertwining the component
isomorphism with the natural module tensored with the binary S₃ plane.
The Borel has no fixed vectors on that tensor. One or two such layers,
above a central layer and below a central quotient, therefore give
C_U(B)=C_U(K) by odd-index averaging. This proves the extension step also
when the module does not split. The rank-one and odd-degree projective
rank-two specializations discharge the fixed-space and odd-index premises
using concrete matrix Borels and their two-residuals.

These are conditional layer deductions. The source owner must construct the
section identifications from F.9.18 and B.4.2 and connect B to its actual
Borel image; none of those classification steps is a field of the result.
-/

@[expose] public section
open Representation Representation.BinaryOffender Representation.HigherFieldBorelFixedSpaces
open scoped TensorProduct MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction
namespace NaturalLayers
variable {K L U N : Type*} [Group K] [Group L]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup N] [Module (ZMod 2) N]

/-- Restriction to the first actor of the tensor with the genuine natural S₃ plane. -/
noncomputable abbrev naturalTensor (σ : Representation (ZMod 2) L N) :=
  (externalTensor σ (BinaryPermutation.coreRepresentation (Fin 3))).comp
    (MonoidHom.inl L (Equiv.Perm (Fin 3)))

/-- A genuine invariant section, with equivariant tensor coordinates and a component isomorphism. -/
structure TensorLayer (ρ : Representation (ZMod 2) K U)
    (σ : Representation (ZMod 2) L N) (e : K ≃* L)
    (C D : Submodule (ZMod 2) U) where
  lower_le : C ≤ D
  stable : ∀ (g : K) (d : D), ρ g d ∈ D
  coordinates : (D ⧸ C.comap D.subtype) ≃ₗ[ZMod 2]
    N ⊗[ZMod 2] BinaryPermutation.core (Fin 3)
  equivariant : ∀ (g : K) (d : D),
    coordinates (Submodule.Quotient.mk (⟨ρ g d, stable g d⟩ : D)) =
      naturalTensor σ (e g) (coordinates (Submodule.Quotient.mk d))

/-- A Borel-fixed vector in the upper layer belongs to its lower layer. -/
theorem TensorLayer.fixed_le
    {ρ : Representation (ZMod 2) K U} {σ : Representation (ZMod 2) L N}
    {e : K ≃* L} {C D : Submodule (ZMod 2) U}
    (layer : TensorLayer ρ σ e C D) (B : Subgroup K) (B₀ : Subgroup L)
    (hB : B.map e.toMonoidHom = B₀) (hzero : fixedSpace σ B₀ = ⊥) :
    D ⊓ fixedSpace ρ B ≤ C := by
  let actor : B →* L := e.toMonoidHom.comp B.subtype
  have hactor : actor.range = B₀ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hB
  exact fixedSpace_le_of_model_section ρ (naturalTensor σ) B B₀ C D
    (fun b d => layer.stable b d) actor hactor layer.coordinates
    (fun b d => layer.equivariant b d)
    (externalTensor_left_fixedSpace σ _ B₀ hzero)

/-- Odd Borel index transports through the actual component isomorphism. -/
theorem odd_index_of_model (e : K ≃* L) (B : Subgroup K) (B₀ : Subgroup L)
    (hB : B.map e.toMonoidHom = B₀) (hodd : Odd B₀.index) : Odd B.index := by
  have hm : B₀.comap e.toMonoidHom = B := by
    rw [← hB]
    exact Subgroup.comap_map_eq_self_of_injective e.injective B
  rw [← hm, Subgroup.index_comap_of_surjective _ e.surjective]
  exact hodd

/-- A single natural tensor layer with central sections gives equality of fixed spaces. -/
theorem fixedSpace_of_one_layer
    (ρ : Representation (ZMod 2) K U) (σ : Representation (ZMod 2) L N)
    (e : K ≃* L) (B : Subgroup K) (B₀ : Subgroup L)
    (hB : B.map e.toMonoidHom = B₀) (hodd : Odd B₀.index)
    (C W : Submodule (ZMod 2) U)
    (hcentral : C ≤ ρ.invariants)
    (hquot : ∀ (g : K) (u : U), ρ g u - u ∈ W)
    (layer : TensorLayer ρ σ e C W) (hzero : fixedSpace σ B₀ = ⊥) :
    fixedSpace ρ B = ρ.invariants :=
  odd_index_fixedSpace_extension ρ B W (odd_index_of_model e B B₀ hB hodd) hquot
    ((layer.fixed_le B B₀ hB hzero).trans hcentral)

/-- Two natural tensor layers give the same conclusion, with no splitting premise. -/
theorem fixedSpace_of_two_layers {N' : Type*} [AddCommGroup N'] [Module (ZMod 2) N']
    (ρ : Representation (ZMod 2) K U) (σ : Representation (ZMod 2) L N)
    (τ : Representation (ZMod 2) L N')
    (e : K ≃* L) (B : Subgroup K) (B₀ : Subgroup L)
    (hB : B.map e.toMonoidHom = B₀) (hodd : Odd B₀.index)
    (C D W : Submodule (ZMod 2) U)
    (hcentral : C ≤ ρ.invariants)
    (hquot : ∀ (g : K) (u : U), ρ g u - u ∈ W)
    (first : TensorLayer ρ σ e C D) (second : TensorLayer ρ τ e D W)
    (hzero : fixedSpace σ B₀ = ⊥) (hzero' : fixedSpace τ B₀ = ⊥) :
    fixedSpace ρ B = ρ.invariants :=
  odd_index_fixedSpace_extension_two_layers ρ B C D W
    (odd_index_of_model e B B₀ hB hodd) hquot hcentral
    (first.fixed_le B B₀ hB hzero) (second.fixed_le B B₀ hB hzero')

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The natural L₂ branch, with the Borel residual and its odd index computed. -/
theorem sl2_one_layer (ρ : Representation (ZMod 2) K U) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2 ^ n) (e : K ≃* SL(2,F))
    (B : Subgroup K)
    (hB : B.map e.toMonoidHom = twoResidualImage (Matrix.SpecialLinearGroup.rankOneBorel F))
    (C W : Submodule (ZMod 2) U) (hcentral : C ≤ ρ.invariants)
    (hquot : ∀ (g : K) (u : U), ρ g u - u ∈ W)
    (layer : TensorLayer ρ (binaryNatural 2) e C W) : fixedSpace ρ B = ρ.invariants :=
  fixedSpace_of_one_layer ρ (binaryNatural 2) e B _ hB
    (sl2_twoResidual_odd_index hn hF) C W hcentral hquot layer
    (sl2_twoResidual_natural_fixedSpaces hn hF).1

/-- The first odd-degree L₃ case, on the actual projective natural module. -/
theorem psl3_one_layer (ρ : Representation (ZMod 2) K U) {n : ℕ}
    (hn : 1 < n) (hodd : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))
    (B : Subgroup K)
    (hB : B.map e.toMonoidHom = twoResidualImage (Matrix.PSL3.LinearThree.borel F))
    (C W : Submodule (ZMod 2) U) (hcentral : C ≤ ρ.invariants)
    (hquot : ∀ (g : K) (u : U), ρ g u - u ∈ W)
    (layer : TensorLayer ρ (projectiveBinaryNatural hodd hF) e C W) :
    fixedSpace ρ B = ρ.invariants :=
  fixedSpace_of_one_layer ρ (projectiveBinaryNatural hodd hF) e B _ hB
    (psl3_twoResidual_odd_index hn hF) C W hcentral hquot layer
    (psl3_twoResidual_natural_fixedSpaces hn hodd hF).1

/-- The second odd-degree L₃ case, retaining both natural tensor layers. -/
theorem psl3_two_layers (ρ : Representation (ZMod 2) K U) {n : ℕ}
    (hn : 1 < n) (hodd : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))
    (B : Subgroup K)
    (hB : B.map e.toMonoidHom = twoResidualImage (Matrix.PSL3.LinearThree.borel F))
    (C D W : Submodule (ZMod 2) U) (hcentral : C ≤ ρ.invariants)
    (hquot : ∀ (g : K) (u : U), ρ g u - u ∈ W)
    (first : TensorLayer ρ (projectiveBinaryNatural hodd hF) e C D)
    (second : TensorLayer ρ (projectiveBinaryNatural hodd hF) e D W) :
    fixedSpace ρ B = ρ.invariants :=
  fixedSpace_of_two_layers ρ (projectiveBinaryNatural hodd hF)
    (projectiveBinaryNatural hodd hF) e B _ hB
    (psl3_twoResidual_odd_index hn hF) C D W hcentral hquot first second
    (psl3_twoResidual_natural_fixedSpaces hn hodd hF).1
    (psl3_twoResidual_natural_fixedSpaces hn hodd hF).1

end NaturalLayers
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction

end
