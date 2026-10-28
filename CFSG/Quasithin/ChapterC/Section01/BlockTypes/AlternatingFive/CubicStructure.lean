module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.CubicNormalizer
public import Theory.GroupTheory.PResidual.PrimeToSubnormal

/-! The cubic Sylow subgroup and cubic residual of an A₅ block. Its
quotient by O₂ has order60, so no cubic square divides its order; every
nontrivial cubic normally generates the block. Used in source2.4.25. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L] [Finite L]

theorem IsAlternatingBlock.nine_not_dvd_card (h : IsAlternatingBlock L 5) :
    ¬ 9 ∣ Nat.card L := by
  obtain ⟨e⟩ := h.2.2.quotient_iso
  have hquot : Nat.card (L ⧸ pCore 2 L) = 60 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,card_alternatingGroup]
    decide
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  have hcard : Nat.card L = 60 * 2^n := by
    rw [←(pCore 2 L).index_mul_card,(pCore 2 L).index_eq_card,hquot,hn]
  have hc : Nat.Coprime 9 (2^n) := (by decide : Nat.Coprime 9 2).pow_right n
  intro hd
  rw [hcard] at hd
  have : 9 ∣ 60 := hc.dvd_mul_right.mp hd
  norm_num at this

theorem IsAlternatingBlock.cyclic_three_sylow (h : IsAlternatingBlock L 5)
    (P : Sylow 3 L) : IsCyclic P := by
  obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
  have hn1 : n ≤ 1 := by
    by_contra hh
    apply h.nine_not_dvd_card
    change 3^2 ∣ Nat.card L
    exact (pow_dvd_pow 3 (by omega : 2 ≤ n)).trans (hn ▸ (P : Subgroup L).card_subgroup_dvd_card)
  have hd : Nat.card P ∣ 3 := by
    rw [hn]
    simpa only [pow_one] using pow_dvd_pow 3 hn1
  exact isCyclic_of_card_dvd_prime hd

theorem IsAlternatingBlock.threeResidual_eq_top (h : IsAlternatingBlock L 5) :
    primeToResidual 3 L = ⊤ := by
  obtain ⟨e⟩ := h.2.2.quotient_iso
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (L ⧸ pCore 2 L) := e.isSimpleGroup
  apply primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 L) pCore_isPGroup h.2.1.twoPerfect
  rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,card_alternatingGroup]
  decide

end CFSG.Quasithin.ChapterC
