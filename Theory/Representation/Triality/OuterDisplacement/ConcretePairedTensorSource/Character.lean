module
public import Theory.Representation.Triality.OuterDisplacement.ConcretePairedTensorSource.Coefficients
public import Theory.Representation.Triality.RestrictedWeights.ConcreteFinitePeriodSource

/-!
# Weight periods forced by the actual outer involution

The native coefficient action carries tensor character values to their
`2^r`-th powers. This follows from its proved compatibility with the original
Spin Frobenius, the basic-factor Frobenius character formula, and the product
formula for tensor characters.

A square-one linear operator intertwining the actual tensor with an inner
twist of that coefficient action preserves its character. Conjugacy
invariance removes the inner twist, and the established native character
period theorem therefore gives period `r` for the same extended weight word.
No character-invariance or Frobenius-compatibility premise remains; the
operator and all native inclusion and coefficient maps are retained.

Source: GLS3 2.8.3--4 and Remark 2.8.8; Guralnick--Malle,
Classification of 2F-modules II, Section 3.5 and Lemma 8.6.
-/

public noncomputable section
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
open scoped BigOperators
namespace Triality.OuterDisplacement.ConcretePairedTensorSource
open Triality.Standard Triality.Standard.OuterOdd Triality.Standard.EvenField
open Triality.SimplyConnected Triality.RestrictedWeights Triality.RestrictedWeights.Concrete
open SteinbergTensors SteinbergTensors.AlgebraicTensor

private theorem basic_character_iterate
    {k : Type*} [Field k] {G : Type*} [Group G]
    (χ : BasicWeight → G → k) (φ : Monoid.End G)
    (hφ : ∀ a g, χ a (φ g) = χ a g ^ 2)
    (a : BasicWeight) (g : G) (r : ℕ) :
    χ a ((φ ^ r) g) = χ a g ^ (2 ^ r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ']
    change χ a (φ ((φ ^ r) g)) = _
    rw [hφ, ih, ← pow_mul, Nat.pow_succ]

variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]
    (hu : IsUniversalVersion (groupVariety k))

/-- Every native coefficient Frobenius acts by the corresponding power on tensor traces. -/
theorem native_tensor_coefficient_character (n : ℕ) (hn : 0 < n)
    (w : ℕ → BasicWeight) (r : ℕ) (g : BinaryCarrier n hn) :
    Representation.character
      (tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
        (nativePointHom k n hn) w n).ρ
      (coefficientAction (binaryParameters n hn) (EvenField.coefficientFrobenius n hn r) g) =
    Representation.character
      (tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
        (nativePointHom k n hn) w n).ρ g ^ (2 ^ r) := by
  let φ : Monoid.End (groupVariety k).Point := (finiteGeometry k hu).frobenius.onPoints
  have hφ : ∀ a g, basicCharacter (basicFamily k hu).factor a (φ g) =
      basicCharacter (basicFamily k hu).factor a g ^ 2 :=
    basicCharacter_frobenius (algebraicGeometry k hu) (ordinaryFrobenius k hu) (basicFamily k hu)
  have hι : nativePointHom k n hn
      (coefficientAction (binaryParameters n hn) (EvenField.coefficientFrobenius n hn r) g) =
      (φ ^ r) (nativePointHom k n hn g) := nativePointHom_frobenius_pow k n hn r g
  change Representation.character
      (tensor (basicFamily k hu).factor φ (nativePointHom k n hn) w n).ρ
      (coefficientAction (binaryParameters n hn) (EvenField.coefficientFrobenius n hn r) g) =
    Representation.character
      (tensor (basicFamily k hu).factor φ (nativePointHom k n hn) w n).ρ g ^ (2 ^ r)
  rw [character_tensor, character_tensor, ← Finset.prod_pow, hι]
  apply Finset.prod_congr rfl
  intro i _
  have hcomm : (φ ^ i) ((φ ^ r) (nativePointHom k n hn g)) =
      (φ ^ r) ((φ ^ i) (nativePointHom k n hn g)) := by
    change ((φ ^ i) * (φ ^ r)) _ = ((φ ^ r) * (φ ^ i)) _
    rw [← pow_add, ← pow_add, Nat.add_comm]
  rw [hcomm]
  exact basic_character_iterate (basicCharacter (basicFamily k hu).factor) φ hφ _ _ r

private theorem character_involutive_intertwiner
    {F G W : Type*} [Field F] [Group G] [AddCommGroup W] [Module F W]
    (ρ : Representation F G W) (α : G ≃* G)
    (T : Module.End F W) (hT : T * T = 1)
    (hTi : ∀ g, T * ρ g = ρ (α g) * T) (g : G) :
    ρ.character (α g) = ρ.character g := by
  have hTi' : Function.Involutive T := fun v => LinearMap.congr_fun hT v
  let e : Representation.Equiv ρ (ρ.comp α.toMonoidHom) :=
    .mk (LinearEquiv.ofInvolutive T hTi') hTi
  exact (congrFun (Representation.char_iso e) g).symm

/-- The actual square-one intertwiner forces a period of the original extended weight word. -/
theorem native_tensor_period_of_inner_coefficient_intertwiner
    (n : ℕ) (hn : 0 < n) (a : Fin n → BasicWeight) (r : ℕ)
    (α : BinaryCarrier n hn ≃* BinaryCarrier n hn) (x : BinaryCarrier n hn)
    (hform : ∀ g, α g = x *
      coefficientAction (binaryParameters n hn) (EvenField.coefficientFrobenius n hn r) g * x⁻¹)
    (T : Module.End k (tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
      (nativePointHom k n hn) (extendWeights hn a) n))
    (hT : T * T = 1)
    (hTi : ∀ g, T *
        (tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
          (nativePointHom k n hn) (extendWeights hn a) n).ρ g =
      (tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
        (nativePointHom k n hn) (extendWeights hn a) n).ρ (α g) * T) :
    Function.Periodic (extendWeights hn a) r := by
  apply (native_tensor_character_period k hu n hn a r).mp
  intro g
  rw [← native_tensor_coefficient_character k hu n hn (extendWeights hn a) r g]
  have h := character_involutive_intertwiner
    (tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
      (nativePointHom k n hn) (extendWeights hn a) n).ρ α T hT hTi g
  rw [hform, Representation.char_conj] at h
  exact h

end Triality.OuterDisplacement.ConcretePairedTensorSource
