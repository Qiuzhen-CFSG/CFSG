module
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Bounds
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Swap
public import Theory.SpecificGroups.PSL2.AutomorphismModel
import Mathlib.Tactic

/-!
# Field twists and the genuine projective quotient

Coordinatewise inverse field automorphisms identify independently twisted natural
summands with the ordinary binary natural sum. On a tensor, independent twists
are instead encoded by actual automorphisms of the two acting factors: the tensor
product remains over F. The canonical SL₂ ≃ PSL₂ quotient in characteristic two
transports the models without replacing either group by a family tag.

Source: GLS, vol. 2, Theorems 25.14 and 26.24 (natural-module twists and the final
fixed-codimension argument). No automorphism coverage theorem is assumed here.
-/
@[expose] public section
open Module
namespace Representation.BinaryOffender.NaturalTensor
variable (F : Type*) [Field F] [Algebra (ZMod 2) F]

/-- Independently untwist every natural summand by its actual field automorphism. -/
def untwistNaturalSum {ι : Type*} (τ : ι → F ≃+* F) :
    (ι → NaturalSpace F) ≃ₗ[ZMod 2] (ι → NaturalSpace F) where
  toFun v i j := (τ i).symm (v i j)
  invFun v i j := τ i (v i j)
  left_inv v := by ext i j; exact (τ i).apply_symm_apply _
  right_inv v := by ext i j; exact (τ i).symm_apply_apply _
  map_add' v w := by ext i j; exact (τ i).symm.map_add _ _
  map_smul' c v := by ext i j; exact ZMod.map_smul (τ i).symm c (v i j)

/-- A sum of genuine natural representations with independent field twists. -/
def twistedNaturalSumAction {ι : Type*} (τ : ι → F ≃+* F) :
    Representation F (Matrix.SpecialLinearGroup (Fin 2) F) (ι → NaturalSpace F) where
  toFun g := LinearMap.pi (fun i =>
    (specialLinearNatural 2 (Theory.PSL2.sl2FieldAut (τ i) g)).comp (LinearMap.proj i))
  map_one' := by ext v i j; simp
  map_mul' g h := by ext v i j; simp

/-- The untwisting is binary-linear and genuinely equivariant. -/
theorem untwistNaturalSum_action {ι : Type*} (τ : ι → F ≃+* F)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : ι → NaturalSpace F) :
    untwistNaturalSum F τ (twistedNaturalSumAction F τ g v) =
      naturalSumAction F ι g (untwistNaturalSum F τ v) := by
  ext i j
  change (τ i).symm ((specialLinearNatural 2 (Theory.PSL2.sl2FieldAut (τ i) g) (v i)) j) =
    (specialLinearNatural 2 g (fun j => (τ i).symm (v i j))) j
  simp [specialLinearNatural_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Theory.PSL2.sl2FieldAut]

/-- The genuine tensor over F, with independently field-twisted factors. -/
def twistedTensorAction (τ υ : F ≃+* F) :
    Representation (ZMod 2)
      (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) (TensorSpace F) :=
  (binaryTensorAction F).comp
    ((Theory.PSL2.sl2FieldAut τ).prodCongr (Theory.PSL2.sl2FieldAut υ)).toMonoidHom

/-- Untwist the marking of both group factors; the tensor scalar field stays F. -/
theorem twistedTensorAction_reparam (τ υ : F ≃+* F)
    (g : Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)
    (v : TensorSpace F) :
    twistedTensorAction F τ υ
      ((Theory.PSL2.sl2FieldAut τ).symm g.1, (Theory.PSL2.sl2FieldAut υ).symm g.2) v =
      tensorAction F g v := by
  simp [twistedTensorAction, binaryTensorAction, MulEquiv.prodCongr]

variable [Finite F]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Inner bounds remain valid for independently twisted natural summands. -/
theorem twisted_natural_sum_inner_bound [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {ι : Type*} [Fintype ι] (τ : ι → F ≃+* F)
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) V)
    (e : V ≃ₗ[ZMod 2] (ι → NaturalSpace F))
    (he : ∀ g v, e (ρ g v) = twistedNaturalSumAction F τ g (e v))
    (T : Module.End (ZMod 2) V) (hTi : Function.Injective T)
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (hr : r * r = 1) (hne : r ≠ 1)
    (hT : ∀ g v, T (ρ g v) = ρ (r * g * r⁻¹) (T v)) :
    Fintype.card ι * n ≤ operatorFixedCodim T :=
  natural_sum_inner_bound F hF ρ (e.trans (untwistNaturalSum F τ))
    (fun g v => by simp only [LinearEquiv.trans_apply, he, untwistNaturalSum_action])
    T hTi r hr hne hT

/-- Field bounds also permit independent twists and arbitrary mixing of summands. -/
theorem twisted_natural_sum_field_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {ι : Type*} [Fintype ι] (τ : ι → F ≃+* F)
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) V)
    (e : V ≃ₗ[ZMod 2] (ι → NaturalSpace F))
    (he : ∀ g v, e (ρ g v) = twistedNaturalSumAction F τ g (e v))
    (T : Module.End (ZMod 2) V) (r : Matrix.SpecialLinearGroup (Fin 2) F)
    (σ : F →+* F) (hσ : ∃ a, σ a ≠ a)
    (hT : ∀ g v, T (ρ g v) = ρ (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹) (T v)) :
    Fintype.card ι * n ≤ operatorFixedCodim T :=
  natural_sum_field_bound F hF ρ (e.trans (untwistNaturalSum F τ))
    (fun g v => by simp only [LinearEquiv.trans_apply, he, untwistNaturalSum_action])
    T r σ hσ hT

/-- A factor exchange between independently twisted tensor factors, with
compatible twists expressed on the actual group coordinates. -/
theorem twisted_tensor_swap_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (τ υ : F ≃+* F) (T : Module.End (ZMod 2) (TensorSpace F))
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (σ : F →+* F)
    (hT : ∀ g v, T (twistedTensorAction F τ υ (1, g) v) =
      twistedTensorAction F τ υ
        ((Theory.PSL2.sl2FieldAut τ).symm
          (r * Matrix.SpecialLinearGroup.map σ (Theory.PSL2.sl2FieldAut υ g) * r⁻¹), 1) (T v)) :
    n ≤ operatorFixedCodim T := by
  apply swap_inner_field_bound F hF T r σ
  intro g v
  simpa [twistedTensorAction, binaryTensorAction, MulEquiv.prodCongr] using
    hT ((Theory.PSL2.sl2FieldAut υ).symm g) v

end Representation.BinaryOffender.NaturalTensor
