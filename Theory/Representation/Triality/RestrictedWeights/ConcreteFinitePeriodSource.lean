module
public import Theory.Representation.Triality.RestrictedWeights.ConcreteFiniteTensorSource
/-!
# Exact native tensor character periods

The native inclusion lies in the literal graph-field fixed subgroup. The
proved basic character shift, finite tensor irreducibility and unique
parameters therefore identify Frobenius-fixed character values exactly with
periods of the forward diagram-wrapped word. No finite classification or
coefficient-twist premise remains. Source: GLS3 Remark 2.8.8.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
namespace Triality.RestrictedWeights.Concrete
open Triality.SimplyConnected Triality.Standard
open SteinbergTensors SteinbergTensors.AlgebraicTensor
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))

theorem nativePointHom_graphField_fixed (n : ℕ) (hn : 0<n) (g : BinaryCarrier n hn) :
    ((pointEnd (ordinaryFrobenius k hu).morphism)^n)
      ((pinnedTriality k hu).iso.toMulEquiv (nativePointHom k n hn g)) = nativePointHom k n hn g := by
  rw [nativePointHom_eq_inclusion]
  exact (nativeElementaryEquiv k n hn g).val.property

theorem native_tensor_character_period (n : ℕ) (hn : 0<n)
    (a : Fin n → BasicWeight) (r : ℕ) :
    (∀ g, Representation.character
      (tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
        (nativePointHom k n hn) (extendWeights hn a) n).ρ g ^ (2^r) =
      Representation.character
      (tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
        (nativePointHom k n hn) (extendWeights hn a) n).ρ g) ↔
      Function.Periodic (extendWeights hn a) r :=
  left_tensor_character_period (algebraicGeometry k hu) (ordinaryFrobenius k hu)
    (pinnedTriality k hu) (basicFamily k hu) (finiteGeometry k hu).commute
    (nativePointHom k n hn) n hn (nativePointHom_graphField_fixed k hu n hn)
    (native_tensor_irreducible k hu n hn) (native_tensor_unique k hu n hn) a r

end Triality.RestrictedWeights.Concrete
