module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
public import Theory.GroupTheory.SolvableNormalSup

/-!
# The marked local inputs for the external cubic action

All residuals use the literal definitions in Notation 13.2.1. Two-perfectness
comes from taking the two-residual. In the covered case the natural flag
calculation gives the cubic quotient and the elementary-nine quotient of L₁.
Solvability extends over T. The earlier identity V₃ = [V₃,L₁], together with
the centralization by L₀, gives V₃ = [V₃,L₁,+] on the original subgroups.
The ordinary cubic order remains the exact earlier ordinary local calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and 13.2.2(3), printed p.877; §13.3, printed pp.891–892;
application 13.8.20(a), printed p.954/PDF p.971.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]

private theorem solvable_join (D T : Subgroup G) (hD : Group.IsSolvable D)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (D : Set G)) : Group.IsSolvable (D ⊔ T : Subgroup G) := by
  let J := D ⊔ T
  let A := D.subgroupOf J
  let B := T.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le D.le_normalizer hn)
  let : Group.IsSolvable D := hD
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show D ≤ J from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show D ≤ J from le_sup_left)).injective
  let : Group.IsSolvable T := @IsNilpotent.to_isSolvable T _ hT.isNilpotent
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show T ≤ J from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show T ≤ J from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top A B
  rw [← subgroupOf_sup (show D ≤ J from le_sup_left) (show T ≤ J from le_sup_right)]
  exact subgroupOf_self _

theorem ordinary_local_inputs (L T V₁ : Subgroup G)
    (hT : IsPGroup 2 T) (hTV : T ≤ normalizer (V₁ : Set G))
    (hcard : Nat.card (one L T V₁ ⧸ pCore 2 (one L T V₁)) = 3) :
    IsPPerfect 2 (one L T V₁) ∧ Group.IsSolvable (one L T V₁ ⊔ T : Subgroup G) := by
  have hs : Group.IsSolvable (one L T V₁) := by
    let : IsMulCommutative (one L T V₁ ⧸ pCore 2 (one L T V₁)) :=
      (isCyclic_of_prime_card hcard).isMulCommutative
    exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 (one L T V₁))).mpr
      ⟨@IsNilpotent.to_isSolvable _ _ pCore_isPGroup.isNilpotent,
        Group.isSolvable_of_comm (fun a b => mul_comm a b)⟩
  exact ⟨residual_isPPerfect _, solvable_join _ _ hs hT (T_normalizes_one L T V₁ hTV)⟩

theorem covered_local_inputs (L T V V₁ V₃ : Subgroup G)
    (d : LocalAction.NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hseed : V₃ = ⁅V₃, one L T V₁⁆) :
    IsPPerfect 2 (plus L T V₁) ∧
      Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3 ∧
      Group.IsSolvable (one L T V₁ ⊔ T : Subgroup G) ∧
      V₃ = ⁅V₃, plus L T V₁⁆ := by
  have hs : Group.IsSolvable (one L T V₁) := by
    let : IsMulCommutative (one L T V₁ ⧸ pCore 2 (one L T V₁)) :=
      d.one_quotient_commutative hfactor
    exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 (one L T V₁))).mpr
      ⟨@IsNilpotent.to_isSolvable _ _ pCore_isPGroup.isNilpotent,
        Group.isSolvable_of_comm (fun a b => mul_comm a b)⟩
  have ht : IsPGroup 2 T := d.sylow_eq ▸ d.sylow.isPGroup' |>.of_equiv
    (subgroupOfEquivOfLe (show T ≤ L ⊔ T from le_sup_right))
  refine ⟨residual_isPPerfect _, d.plus_core_card hfactor,
    solvable_join _ _ hs ht (T_normalizes_one L T V₁ d.line_stable), ?_⟩
  calc
    V₃ = ⁅V₃, one L T V₁⁆ := hseed
    _ = ⁅one L T V₁, V₃⁆ := commutator_comm _ _
    _ = ⁅plus L T V₁, V₃⁆ := d.one_seed_commutator_eq_plus hfactor d.plus_normalizes_seed
    _ = ⁅V₃, plus L T V₁⁆ := commutator_comm _ _

/-- Select the actual source residual in the two local model cases. The
ordinary cubic order and covered natural flag are earlier §13.2 inputs;
the seed identity is the earlier §13.3 identity for the full L₁. -/
theorem selected_local_inputs (L T V V₁ V₃ X : Subgroup G)
    (hT : IsPGroup 2 T) (hTV : T ≤ normalizer (V₁ : Set G))
    (hlocal : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧ X = plus L T V₁))
    (hordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (one L T V₁ ⧸ pCore 2 (one L T V₁)) = 3)
    (hcovered : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
      Nonempty (LocalAction.NaturalSetup L T V V₁ V₃))
    (hfactor : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
      one L T V₁ = plus L T V₁ ⊔ zero L)
    (hseed : V₃ = ⁅V₃, one L T V₁⁆) :
    X ≤ one L T V₁ ∧ IsPPerfect 2 X ∧ Nat.card (X ⧸ pCore 2 X) = 3 ∧
      Group.IsSolvable (one L T V₁ ⊔ T : Subgroup G) ∧ V₃ = ⁅V₃, X⁆ := by
  rcases hlocal with ⟨h,rfl⟩ | ⟨h,rfl⟩
  · obtain ⟨hp,hs⟩ := ordinary_local_inputs L T V₁ hT hTV (hordinary h)
    exact ⟨le_rfl,hp,hordinary h,hs,hseed⟩
  · obtain ⟨d⟩ := hcovered h
    exact ⟨plus_le_one L T V₁ d.line_stable,
      covered_local_inputs L T V V₁ V₃ d (hfactor h) hseed⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel

end
