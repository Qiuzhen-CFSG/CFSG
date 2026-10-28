module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCoreSplitting
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCartan
public import Theory.GroupTheory.GaschutzCentralPreimage

/-!
# A full endpoint complement containing the original whole Cartan

The prescribed compatible Cartans have joint order seven in the original
common Borel. Conjugating the constructed complement to the full H-core
places that same joint Cartan inside it. Its rank-one identification remains
the restriction of the prescribed original quotient projection.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCartanComplement
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85.OriginalExtension
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

/-- The original joint Cartan is contained in a complement to the whole
intrinsic H-core, with the literal source quotient marking on that complement. -/
theorem source_cartan_complement
    (c : CompatibleCartans ![locals T M Mc H 1,locals T M Mc H 0]
      (reducedSylow ![locals T M Mc H 1,locals T M Mc H 0] (T : Subgroup G))) :
    ∃ R : Subgroup H, (pCore 2 H).IsComplement' R ∧
      c.D 0 ⊔ c.D 1 ≤ R.map H.subtype ∧
      ∃ f : R ≃* Theory.PSL2.BinaryGroup 3,
        ∀ r : R, f r = (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)
          (QuotientGroup.mk' (pCore 2 H) (r:H)) := by
  let L := ![locals T M Mc H 1,locals T M Mc H 0]
  have hB : commonBorel L (T : Subgroup G) = H ⊓ M := by
    change borel (locals T M Mc H 1) (T : Subgroup G) ⊔
      borel (locals T M Mc H 0) (T : Subgroup G) ⊔ (T : Subgroup G) = _
    rw [sup_comm (borel (locals T M Mc H 1) (T : Subgroup G))
      (borel (locals T M Mc H 0) (T : Subgroup G))]
    exact (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).2.2.1
  have hS : reducedSylow L (T : Subgroup G) = (T : Subgroup G) := by
    change (commonBorel L (T : Subgroup G)).pCoreIn 2 = _
    rw [hB]
    exact source_borel_twoCore hG T hempty hM hu hmany hcard e H hH eR
  have hBH : commonBorel L (reducedSylow L (T : Subgroup G)) ≤ H := by
    rw [hS,hB]
    exact inf_le_left
  have hCH : c.D 0 ⊔ c.D 1 ≤ H := c.joint_le.trans hBH
  have hC7 : Nat.card (c.D 0 ⊔ c.D 1 : Subgroup G)=7 := by
    have hc := SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c
    rw [cartan,card_map_of_injective middleMap_injective,
      Nat.card_congr (subgroupOfEquivOfLe c.joint_le).toEquiv] at hc
    exact hc
  let A := (c.D 0 ⊔ c.D 1).subgroupOf H
  have hA7 : Nat.card A=7 := (Nat.card_congr (subgroupOfEquivOfLe hCH).toEquiv).trans hC7
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hA : IsPGroup 7 A := IsPGroup.of_card (n:=1) (by simpa only [pow_one] using hA7)
  have hQ7 : ¬7∣Nat.card (pCore 2 H) := by
    have h512 := (source_core_orders hG T hempty hM hu hmany hcard e H hH eR).1
    rw [pCoreIn,card_map_of_injective H.subtype_injective] at h512
    rw [h512]
    decide
  obtain ⟨K,hK,_,_⟩ := SourceCoreSplitting.source_first_core_complement
    hG T hempty hM hu hmany hcard e H hH eR
  obtain ⟨R,hR,hAR⟩ := complement_containing_prime_subgroup (pCore 2 H) K A hK hA hQ7
  let ε := sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR
  let f := hR.symm.QuotientMulEquiv.symm.trans ε
  refine ⟨R,hR,?_,f,?_⟩
  · rw [←map_subgroupOf_eq_of_le hCH]
    exact map_mono hAR
  · intro r
    apply congrArg ε
    change hR.symm.QuotientMulEquiv.symm r=QuotientGroup.mk' (pCore 2 H) (r:H)
    apply hR.symm.QuotientMulEquiv.injective
    rw [MulEquiv.apply_symm_apply,quotientMulEquiv_mk_apply_of_isComplement']

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCartanComplement
