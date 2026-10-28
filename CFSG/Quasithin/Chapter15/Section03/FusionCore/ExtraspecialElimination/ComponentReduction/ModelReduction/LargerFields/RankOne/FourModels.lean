module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelCases
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.AtlasPort.LinearGroups.G2.Perfectness
public import Theory.SpecificGroups.SL2.EvenBorelResidual

/-!
# The four concrete nonbinary Lie carriers

The existing Lie alternative retains PSL₂ and the derived Sp₄ and G₂
carriers. In characteristic two PSL₂ is SL₂. For field order greater than
two, the checked root-generation arguments identify the derived Sp₄ and
G₂ groups with their full matrix and octonion groups. This leaves exactly
SL₂, SL₃, Sp₄ and G₂, with actual multiplicative equivalences and the same
field exponent. The characteristic-two instance is derived from field order.

This is a carrier conversion from a supplied Lie alternative. Extracting
that alternative from the genuine offender representation remains the
responsibility of the source assembly and the existing FF enumeration owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2,
printed p.86, and proof of 15.3.49 after (k), printed p.1144.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
universe u
variable {D : Type u} [Group D]

/-- Every alternative is an isomorphism with the actual group over the given field. -/
def FourModels (D : Type u) [Group D] (F : Type) [Field F] : Prop :=
  Nonempty (D ≃* SL(2,F)) ∨ Nonempty (D ≃* SL(3,F)) ∨
    Nonempty (D ≃* Matrix.symplecticGroup (Fin 2) F) ∨ Nonempty (D ≃* Atlas.G2.Model F)

/-- Remove the binary endpoints and identify the full nonbinary carriers. -/
theorem four_models_of_lie {n : ℕ} (hmodel : LieComponentModel D n) (hn : 1 < n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧ FourModels D F := by
  have hq : 2 < 2 ^ n := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ < 2 ^ n := Nat.pow_lt_pow_right (by decide) hn
  cases hmodel with
  | linear_two he F hF model =>
    let _ := Fintype.ofFinite F
    let _ : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    obtain ⟨e⟩ := model
    let a : SL(2,F) ≃* PSL(2,F) := MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
      ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
    exact ⟨F, inferInstance, inferInstance, inferInstance, hF, Or.inl ⟨e.trans a.symm⟩⟩
  | linear_three he F hF model =>
    let _ := Fintype.ofFinite F
    let _ : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact ⟨F, inferInstance, inferInstance, inferInstance, hF, Or.inr (Or.inl model)⟩
  | symplectic he F hF model =>
    let _ := Fintype.ofFinite F
    let _ : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    obtain ⟨e⟩ := model
    exact ⟨F, inferInstance, inferInstance, inferInstance, hF, Or.inr (Or.inr (Or.inl
      ⟨e.trans (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two (hF ▸ hq))⟩))⟩
  | g2 he F hF model =>
    let _ := Fintype.ofFinite F
    let _ : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    obtain ⟨e⟩ := model
    let _ := Atlas.G2.isPerfect (F := F) (hF ▸ hq)
    let a : commutator (Atlas.G2.Model F) ≃* Atlas.G2.Model F :=
      (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans topEquiv
    exact ⟨F, inferInstance, inferInstance, inferInstance, hF,
      Or.inr (Or.inr (Or.inr ⟨e.trans a⟩))⟩
  | binary_linear he n' hn' model => omega
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
