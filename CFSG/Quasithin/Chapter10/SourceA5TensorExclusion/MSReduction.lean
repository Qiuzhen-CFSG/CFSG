module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.CharacteristicReduction
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MSCentralOrbit

/-!
# The original tensor branch admits the MS characteristic replacement

The original stabilizer supplies MS3 and contains O₂(H). The C-component
product identifies the normal residual. These source inputs construct the
minimum characteristic replacement and preserve the embedded intrinsic core,
without requiring an initial symplectic module or a binary quotient.

Source: AS9.3.6--10 and MS93 Section7, pp.932--933.
-/

public section
open Subgroup Theory.GroupTheory
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC.MSCentralOrbit
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Source Section 7 replacement on the original H/K construction. -/
theorem source_tensor_ms_characteristic_reduction
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hLH : L ≤ H) (hout : ¬ H ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hprod : ∀ g : H, ∃ k ∈ K,
      ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H), k*r=g) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H)
    ∃ d : ChapterC.BinaryMS.MS93.CharacteristicReduction K R,
      d.overgroup.Normal ∧ ChapterC.MSCharacteristicCondition d.radical ∧
      pCore 2 d.overgroup ≤ d.radical ∧
      (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆).map d.overgroup.subtype =
        (ChapterC.blockU K).map K.subtype := by
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D hn H hRH hLH hout hs
  exact ChapterC.BinaryMS.MS93.component_characteristic_reduction K _ hK
    hodd.isPGroup hprod hodd.twoCore_le hms

end CFSG.Quasithin.Chapter10
