module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.Models
import Mathlib.Tactic.FinCases

open Matrix Representation Representation.BinaryOffender TensorProduct
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
/-!
# The point radical in the natural tensor model

These are the literal point shears of SL₃(2), included in the first factor
of SL₃(2) × S₃. Their rank is two, their tensor action is quadratic, and
they fix the tensor of the marked point with the whole S₃ natural module.
Thus these three properties alone cannot give the rank-one conclusion in
the final paragraph of Aschbacher–Smith 13.8.21(1), printed p.957 (combined
manuscript of 1 March 2004). The critical-pair argument needs additional
source input. No identification with a source parabolic is asserted here.

Adapted from the checked MarkedTensorProbe in the retained parent workspace;
the original scratch probe is preserved.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical


def pointShear : Multiplicative (ZMod 2 × ZMod 2) →* BinaryLinearThree.Group where
  toFun c := ⟨!![1,c.toAdd.1,c.toAdd.2; 0,1,0; 0,0,1], by
    simp [Matrix.det_fin_three]⟩
  map_one' := by apply Subtype.ext; decide
  map_mul' c d := by
    apply Subtype.ext
    change !![1,c.toAdd.1+d.toAdd.1,c.toAdd.2+d.toAdd.2; 0,1,0; 0,0,1] =
      !![1,c.toAdd.1,c.toAdd.2; 0,1,0; 0,0,1] *
      !![1,d.toAdd.1,d.toAdd.2; 0,1,0; 0,0,1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]

def pointRadical : Subgroup BinaryLinearThree.Group := pointShear.range

theorem pointShear_injective : Function.Injective pointShear := by
  intro c d h
  exact Prod.ext (congrArg (fun g : BinaryLinearThree.Group => g.val 0 1) h)
    (congrArg (fun g : BinaryLinearThree.Group => g.val 0 2) h)

theorem card_pointRadical : Nat.card pointRadical = 4 := by
  change Nat.card pointShear.range = 4
  rw [← Nat.card_congr (MonoidHom.ofInjective pointShear_injective).toEquiv,
    Nat.card_eq_fintype_card]
  decide

theorem pointRadical_quadratic : IsQuadratic BinaryLinearThree.W pointRadical := by
  rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩ v
  change (pointShear c).val.mulVec ((pointShear d).val.mulVec v - v) =
    (pointShear d).val.mulVec v - v
  change (!![1,c.toAdd.1,c.toAdd.2; 0,1,0; 0,0,1]).mulVec
    ((!![1,d.toAdd.1,d.toAdd.2; 0,1,0; 0,0,1]).mulVec v - v) =
      (!![1,d.toAdd.1,d.toAdd.2; 0,1,0; 0,0,1]).mulVec v - v
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

def componentInclusion : BinaryLinearThree.Group →* TensorGroup := MonoidHom.inl BinaryLinearThree.Group (Equiv.Perm (Fin 3))
def tensorPointRadical : Subgroup TensorGroup := pointRadical.map componentInclusion

theorem tensorPointRadical_rank_two : rank tensorPointRadical = 2 := by
  rw [Representation.BinaryOffender.rank, tensorPointRadical, Subgroup.card_map_of_injective
    (show Function.Injective componentInclusion from fun _ _ h => congrArg Prod.fst h), card_pointRadical]
  decide

theorem tensorPointRadical_quadratic : IsQuadratic naturalTensor tensorPointRadical := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ z
  change TensorProduct.map (BinaryLinearThree.W a)
    (BinaryPermutation.coreRepresentation (Fin 3) 1)
    (TensorProduct.map (BinaryLinearThree.W b)
      (BinaryPermutation.coreRepresentation (Fin 3) 1) z - z) =
    TensorProduct.map (BinaryLinearThree.W b)
      (BinaryPermutation.coreRepresentation (Fin 3) 1) z - z
  rw [map_one]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    simp only [TensorProduct.map_tmul, Module.End.one_apply,
      ← TensorProduct.sub_tmul, pointRadical_quadratic a ha b hb v]
  | add x y hx hy =>
    simp only [map_add, add_sub_add_comm, hx, hy]

/-- The radical fixes the marked point tensor the entire S₃ natural module. -/
theorem tensorPointRadical_fixes_seed (g : TensorGroup) (hg : g ∈ tensorPointRadical) (w : S3Natural) :
    naturalTensor g ((![1,0,0] : BinaryLinearThree.Vector) ⊗ₜ[ZMod 2] w) =
      (![1,0,0] : BinaryLinearThree.Vector) ⊗ₜ[ZMod 2] w := by
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨c, rfl⟩ := ha
  change TensorProduct.map (BinaryLinearThree.W (pointShear c))
    (BinaryPermutation.coreRepresentation (Fin 3) 1)
    ((![1,0,0] : BinaryLinearThree.Vector) ⊗ₜ[ZMod 2] w) = _
  rw [map_one, TensorProduct.map_tmul, Module.End.one_apply]
  congr 1
  change (!![1,c.toAdd.1,c.toAdd.2; 0,1,0; 0,0,1]).mulVec ![1,0,0] = ![1,0,0]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical
