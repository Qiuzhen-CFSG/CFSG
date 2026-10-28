module

public import Theory.PPrimeCore
public import Mathlib.GroupTheory.Transfer

/-!
# The odd core complements a cyclic Sylow two-subgroup

Burnside transfer gives a normal odd complement when the Sylow two-subgroup
is cyclic. It lies in the odd core; coprimality makes the latter disjoint
from the Sylow subgroup, so the odd core itself is the complement.
-/

namespace Sylow

public theorem isComplement'_pPrimeCore_of_isCyclic
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (hT : IsCyclic T)
    (heven : 2 ∣ Nat.card G) :
    (T : Subgroup G).IsComplement' (pPrimeCore 2 G) := by
  have hmin : (Nat.card G).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr heven
  let f := MonoidHom.transferSylow T (hT.normalizer_le_centralizer hmin)
  have hK := hT.isComplement' hmin
  have hle : f.ker ≤ pPrimeCore 2 G := by
    apply le_sSup
    exact ⟨inferInstance, Nat.prime_two.coprime_iff_not_dvd.mpr
      (MonoidHom.not_dvd_card_ker_transferSylow T (hT.normalizer_le_centralizer hmin))⟩
  have hsup : (T : Subgroup G) ⊔ pPrimeCore 2 G = ⊤ := by
    apply top_unique
    rw [← hK.sup_eq_top]
    exact sup_le (hle.trans le_sup_right) le_sup_left
  have hdis : Disjoint (T : Subgroup G) (pPrimeCore 2 G) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp T.isPGroup'
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := G)).pow_left n
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
  rw [← Subgroup.mul_normal, hsup, Subgroup.coe_top]

end Sylow
