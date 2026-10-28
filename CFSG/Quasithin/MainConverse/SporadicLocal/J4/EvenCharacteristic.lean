module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Criteria
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CharacteristicTwo
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Model
public import Theory.GroupTheory.PCoreOvergroup

/-!
# The J₄ condition-E reduction to its maximal Sylow overgroups

A two-local in a nonabelian simple group is proper. Enlarge a two-local
containing T to a maximal proper subgroup L and use an exhaustive cover by
actual equivalences to the literal ATLAS max1, max2 and max4 subgroups.
Max1 and max2 have certified self-centralizing intrinsic two-cores. Assuming
the corresponding max4 result, L has characteristic two. Restricting T to L
then passes characteristic two to the original two-local.

The displayed cover has exactly the mathematical contract of the existing
maximal-Sylow-overgroup owner. The cover and max4 fact remain explicit inputs;
this reduction does not yet establish the J₄ case of the source theorem.
In particular involution fusion or a single local subgroup cannot replace
exhaustive coverage. No standalone ambient simplicity certificate is required.

Source: Aschbacher–Smith, Theorem 0.1.2(5), printed p.4, repeated as
Theorem 0.1.1(5), printed p.482; condition E on pp.3–4 and pp.481–482.
The Sylow-overgroup route is the one used in A.3.12, printed pp.47–48.
-/

public section

namespace CFSG.Quasithin.MainConverse.SporadicLocal
open Subgroup Janko4
open Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- The exhaustive maximal-Sylow cover and the remaining max4 calculation
imply E. Ambient simplicity is inherited from the source application. -/
theorem j4_evenCharacteristic_of_maximal_sylow_cover
    [IsSimpleGroup Model] (hna : ¬ IsMulCommutative Model)
    (hc4 : HasCharacteristicTwo max4Subgroup)
    (hcover : ∀ (T : Sylow 2 Model) (L : Subgroup Model), IsCoatom L →
      (T : Subgroup Model) ≤ L →
      Nonempty (L ≃* Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four) ∨
        Nonempty (L ≃* sourceSubgroup) ∨ Nonempty (L ≃* max4Subgroup)) :
    IsEvenCharacteristic Model := by
  intro T M hM hTM
  obtain ⟨L, hL, hML⟩ := (eq_top_or_exists_le_coatom M).resolve_left
    (twoLocal_ne_top_of_nonabelian_simple hna hM.1)
  have hTL := hTM.trans hML
  have hcL : HasCharacteristicTwo L := by
    rcases hcover T L hL hTL with h | h | h
    · obtain ⟨e⟩ := h
      exact @HasCharacteristicTwo.of_equiv
        (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four) L
        (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four).toGroup L.toGroup
        e.symm LocalStructure.max1_twoCore_centralizer_le
    · obtain ⟨e⟩ := h
      exact @HasCharacteristicTwo.of_equiv sourceSubgroup L sourceSubgroup.toGroup L.toGroup
        e.symm LocalStructure.max2_twoCore_centralizer_le
    · obtain ⟨e⟩ := h
      exact @HasCharacteristicTwo.of_equiv max4Subgroup L max4Subgroup.toGroup L.toGroup
        e.symm hc4
  have hsub : ((T.subtype hTL) : Subgroup L) ≤ M.subgroupOf L := by
    intro x hx
    exact hTM hx
  have hcM := centralizer_pCore_le_of_sylow_le (T.subtype hTL)
    (M.subgroupOf L) hsub hcL
  exact @HasCharacteristicTwo.of_equiv (M.subgroupOf L) M
    (M.subgroupOf L).toGroup M.toGroup (subgroupOfEquivOfLe hML) hcM

end CFSG.Quasithin.MainConverse.SporadicLocal
