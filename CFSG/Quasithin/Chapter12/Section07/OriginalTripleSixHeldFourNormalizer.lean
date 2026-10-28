module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixEscapingSource
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldNoncentralPoint
public import Theory.GroupTheory.PCoreLocalSetup

/-! The normalizer of the original noncentral point four cannot contain an
ambient Sylow two-subgroup. Otherwise its normal four lies in that Sylow and
meets its center, contradicting the proved original noncentrality. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_four_normalizer_no_sylow
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G))
    (S : Sylow 2 G) : ¬(S : Subgroup G)≤normalizer (tripleSixPoint D a t : Set G) := by
  obtain ⟨hB,_,_,_,_⟩ := original_tripleSix_point_identification_at
    h structural D a t ht heven hout
  intro hSN
  let V := tripleSixPoint D a t
  let N := normalizer (V : Set G)
  have hVc : Nat.card V=4 := (tripleSixPoint_properties D a t ht).2.2.1
  have hV0 : V≠⊥ := by intro he; rw [he,card_bot] at hVc; omega
  have hVp : IsPGroup 2 V := IsPGroup.of_card (p := 2) (n := 2) hVc
  have hVNcore : V≤N.pCoreIn 2 := le_pCoreIn_of_normalizes hVp V.le_normalizer le_rfl
  have hVS : V≤(S : Subgroup G) := by
    have hh := hVNcore.trans (pCoreIn_le_sylow N (S.subtype hSN))
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSN] at hh
  have hh := inf_centerIn_ne_bot S.isPGroup' hV0 hVS hSN
  exact hh (original_tripleSix_held_point_inf_sylow_center_eq_bot h D a t ht hB S)

end CFSG.Quasithin.Chapter12.Section07
