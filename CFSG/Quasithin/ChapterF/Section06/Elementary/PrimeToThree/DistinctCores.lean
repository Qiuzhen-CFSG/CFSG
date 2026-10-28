module
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree
public import CFSG.Quasithin.ChapterF.Section06.Amalgams.CaseOne
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Unequal local cores in the prime-to-three quotient

Distinct two-cores of the original two Goldschmidt vertices exclude the
collapsed quotient. They also exclude a common quotient Sylow subgroup of
order two: in that case both local quotient cores vanish, so their preimages
are the same ambient two-core.

Source: Aschbacher--Smith F.6.11(2), printed pp.306--307; the application to
unequal parabolic cores is in 14.6.10(5), printed p.1028.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

private theorem core_eq_of_quotient_core_bot
    (h : IsGoldschmidtTriple A B)
    (hc : pCore 2 (A.map (QuotientGroup.mk' (pPrimeCore 3 G))) = ⊥) :
    A.pCoreIn 2 = pCore 2 G := by
  let q := QuotientGroup.mk' (pPrimeCore 3 G)
  let f := q.subgroupMap A
  have hk : f.ker = (pCore 2 G).subgroupOf A :=
    h.primeToThreeCore_subgroup_kernel A le_rfl
  have hp : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup.comap_subtype
  have he := f.comap_pCore_of_ker_isPGroup (q.subgroupMap_surjective A) hp
  rw [hc] at he
  change f.ker = pCore 2 A at he
  change (pCore 2 A).map A.subtype = pCore 2 G
  rw [←he,hk,map_subgroupOf_eq_of_le (h.twoCore_isGreatest.1.1.trans inf_le_left)]

/-- Unequal original cores retain the full Goldschmidt triple in the literal quotient. -/
theorem IsGoldschmidtTriple.quotient_primeToThreeCore_of_distinct_cores
    (h : IsGoldschmidtTriple A B) (hne : A.pCoreIn 2 ≠ B.pCoreIn 2) :
    IsGoldschmidtTriple (A.map (QuotientGroup.mk' (pPrimeCore 3 G)))
      (B.map (QuotientGroup.mk' (pPrimeCore 3 G))) := by
  rcases h.primeToThreeCore_dichotomy with hg | hb
  · exact hg.2.1
  · exact (hne (hb.1.trans hb.2.1.symm)).elim

/-- The quotient overlap cannot be cyclic of order two when the original cores differ. -/
theorem IsGoldschmidtTriple.primeToThreeCore_intersection_not_cyclic_two
    (h : IsGoldschmidtTriple A B) (hne : A.pCoreIn 2 ≠ B.pCoreIn 2) :
    ¬ Nonempty (((A.map (QuotientGroup.mk' (pPrimeCore 3 G))) ⊓
      (B.map (QuotientGroup.mk' (pPrimeCore 3 G))) : Subgroup _) ≃*
        Multiplicative (ZMod 2)) := by
  rintro ⟨e⟩
  have ht := h.quotient_primeToThreeCore_of_distinct_cores hne
  have hc : Nat.card ((A.map (QuotientGroup.mk' (pPrimeCore 3 G))) ⊓
      (B.map (QuotientGroup.mk' (pPrimeCore 3 G))) : Subgroup _) = 2 := by
    rw [Nat.card_congr e.toEquiv]
    simp
  have hA := core_eq_of_quotient_core_bot h
    (ht.left_core_eq_bot_of_intersection_card_two hc)
  have hB := core_eq_of_quotient_core_bot h.symm
    (ht.symm.left_core_eq_bot_of_intersection_card_two (by simpa only [inf_comm] using hc))
  exact hne (hA.trans hB.symm)
end CFSG.Quasithin.ChapterF
