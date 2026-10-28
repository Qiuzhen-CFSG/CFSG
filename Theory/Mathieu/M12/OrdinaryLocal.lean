module
public import Theory.Mathieu.M12.TwoCentralInvolutions.CentralizerOrder
public import Theory.Mathieu.M12.SylowOvergroups.RankTwoCoverage
public import Theory.Mathieu.M12.Properties.AutCover

/-!
# The ordinary M₁₂ centralizer

The checked Sylow center has order two. A two-central involution has
centralizer of order 192, and every proper Sylow overgroup has order dividing
192, so this centralizer is maximal. These facts apply to the actual Witt-design
model and feed the central-cover argument in Aschbacher--Smith 15.1.20(3d),
printed pp.1096--1097.
-/

public section
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
namespace Sporadic.Mathieu.OrdinaryTwelve
open M12SmallPair

theorem sylow_center_card_two (S : Sylow 2 M12) : Nat.card (center S) = 2 := by
  rw [Nat.card_congr (centerCongr (S.equiv commonSylow)).toEquiv]
  apply (Nat.card_eq_two_iff' (1 : center commonSylow)).mpr
  let zS : commonSylow := ⟨z, core_le_sylowCandidate z_mem_core⟩
  have hz : zS ∈ center commonSylow := (sylowCandidate_center_mem _).mpr (Or.inr rfl)
  refine ⟨⟨zS,hz⟩, ?_, ?_⟩
  · intro he
    have hez : z = 1 := congrArg (fun x : center commonSylow => ((x : commonSylow) : M12)) he
    have ho := z_order
    rw [hez,orderOf_one] at ho
    omega
  · intro x hne
    rcases (sylowCandidate_center_mem x.val).mp x.property with h1 | hz
    · exact (hne (Subtype.ext (Subtype.ext h1))).elim
    · exact Subtype.ext (Subtype.ext hz)

theorem twoCentral_centralizer_isCoatom (t : M12) (ht : orderOf t = 2)
    (hc : TwoCentral t) : IsCoatom (centralizer ({t} : Set M12)) := by
  let C := centralizer ({t} : Set M12)
  have hcard : Nat.card C = 192 := M12Involutions.card_centralizer_of_twoCentral t ht hc
  have hne : C ≠ ⊤ := by
    intro he
    have hz : t ∈ center M12 := mem_center_iff.mpr (fun x =>
      mem_centralizer_singleton_iff.mp (show x ∈ C from he.symm ▸ mem_top x))
    have ht1 : t = 1 := mem_bot.mp (m12_center_eq_bot ▸ hz)
    rw [ht1,orderOf_one] at ht
    omega
  refine ⟨hne, ?_⟩
  intro U hCU
  by_contra hU
  obtain ⟨P,hPC⟩ := hc.exists_sylow_le_centralizer
  have hd := SylowOvergroups.card_dvd_192_of_ne_top U hU ⟨P,hPC.trans hCU.le⟩
  have he : C = U := eq_of_le_of_card_ge hCU.le (by
    rw [hcard]
    exact Nat.le_of_dvd (by decide) hd)
  exact hCU.ne he
end Sporadic.Mathieu.OrdinaryTwelve
