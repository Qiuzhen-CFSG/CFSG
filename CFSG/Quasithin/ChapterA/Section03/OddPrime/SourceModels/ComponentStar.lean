module

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.PrimeRankZero

/-!
# The actual star map on a component with central two-kernel

For an odd prime dividing the component order, O_{p'}(H) centralizes the
component. Its intersection with the component is exactly the center when
that center is a two-group: the reverse inclusion follows from subnormal
inheritance of the two-core. Thus the original star map induces an explicitly
marked equivalence L/Z(L) ≃ L*, without replacing either quotient map.

This is the first reduction of A.3.18, pp.51--53, for the rank-two binary
components in the proof of 2.5.7, p.556. No ambient odd-core or normality
hypothesis is added.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ComponentStar

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

/-- The source prime-to-p core centralizes every component whose order has a p-factor. -/
theorem core_centralizes {L : Subgroup H} (hL : IsComponent H L)
    (hd : p ∣ Nat.card L) : pPrimeCore p H ≤ centralizer (L : Set H) := by
  rcases hL.normal_dichotomy (pPrimeCore p H) with h | h
  · exact (((Fact.out : p.Prime).coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le h))) hd).elim
  · rw [commutator_comm] at h
    exact commutator_eq_bot_iff_le_centralizer.mp h

/-- The complete center, including an exceptional central two-cover, is the
kernel of the literal source star map on L. -/
theorem core_comap_eq_center {L : Subgroup H} (hL : IsComponent H L)
    (hZ : IsPGroup 2 (center L)) (ho : Odd p) (hd : p ∣ Nat.card L) :
    (pPrimeCore p H).comap L.subtype = center L := by
  apply le_antisymm
  · intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (core_centralizes hL hd hx) y y.property)
  · have hz : center L ≤ pCore 2 L := le_sSup ⟨inferInstance, hZ⟩
    have hcore : pCore 2 H ≤ pPrimeCore p H := by
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      obtain ⟨m, hm⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
      rw [hm]
      exact (Nat.coprime_two_right.mpr ho).pow_right m
    exact hz.trans (map_le_iff_le_comap.mp ((pCoreIn_le_of_subnormal 2 hL.1).trans hcore))

/-- The canonical central quotient identifies with the actual image under starMap. -/
def quotientEquiv {L : Subgroup H} (hL : IsComponent H L)
    (hZ : IsPGroup 2 (center L)) (ho : Odd p) (hd : p ∣ Nat.card L) :
    (L ⧸ center L) ≃* starComponent p L := by
  let f := (starMap p H).subgroupMap L
  have hk : f.ker = center L := by
    rw [ker_subgroupMap, starMap, QuotientGroup.ker_mk']
    exact core_comap_eq_center hL hZ ho hd
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f ((starMap p H).subgroupMap_surjective L))

/-- The marking keeps precisely the original ambient star quotient on representatives. -/
theorem quotientEquiv_mk {L : Subgroup H} (hL : IsComponent H L)
    (hZ : IsPGroup 2 (center L)) (ho : Odd p) (hd : p ∣ Nat.card L) (x : L) :
    (quotientEquiv hL hZ ho hd (QuotientGroup.mk' (center L) x) : Star p H) =
      starMap p H x := rfl

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ComponentStar
