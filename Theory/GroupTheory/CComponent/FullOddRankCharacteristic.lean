module
public import Theory.GroupTheory.CComponent.OddRankIsolation

/-!
# A C-component carrying the full odd prime rank is characteristic

Distinct C-components have prime-to-p order when a centerless two-core
quotient already carries the whole ambient p-rank. An automorphic image
has the same positive p-rank, so it must be the original component.

Source: the component-rank argument of Aschbacher–Smith A.3.18, applied
to the local conjugate span in the A₅ specialization of C.4.8.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}
/-- Full positive odd prime rank makes a centerless-quotient C-component characteristic. -/
theorem IsCComponent.characteristic_of_full_odd_rank
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hne : 0 < primeRank p (K ⧸ pCore 2 K))
    (hr : primeRank p G ≤ primeRank p (K ⧸ pCore 2 K)) : K.Characteristic := by
  apply characteristic_iff_map_eq.mpr
  intro a
  by_contra he
  have hc := hK.other_coprime_of_full_odd_rank hp hz hr (hK.map_equiv a) he
  have hzero : primeRank p (K.map a.toMonoidHom) = 0 :=
    PrimeRank.eq_zero_iff_not_dvd_card.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hc)
  have hk : primeRank p K = 0 := (primeRank_congr p (a.subgroupMap K)).trans hzero
  have hb := primeRank_quotient_le_of_isTwoGroup p hp (pCore 2 K) pCore_isPGroup
  omega
end Subgroup

