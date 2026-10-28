module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.ThreeCoreBounds
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue
public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.Quasithin.EvenCharacteristic

/-!
# Seventeen does not divide a full-Sylow Held two-local

The certified maximal-normalizer catalogue places the two-local inside a
conjugate of max3, max4 or max5. The first two have a two-core quotient
mapping to S₆ with kernel of order dividing three. The last has order
21504. All three orders are prime to seventeen.

This excludes a PSL₂(16) section in the original normalized rank-one
local component, as used in Aschbacher–Smith 5.2.2, pp.648–649.
The imported native subgroup and quotient maps retain their ATLAS and
GLS3 Table 5.3p attribution. No ambient order or simplicity input is used.
-/

public section
open Subgroup Theory.GroupTheory
namespace Held.TwoLocalCandidates
open LocalPairs.PairCoverage LocalPairs.PairCoverage.IntervalNormalizer.Inner

private theorem max34_seventeen_free (i : Bool) : ¬ 17 ∣ Nat.card (localOvergroup i) := by
  let f := SixPoint.quotientAction i
  have hk : ¬ 17 ∣ Nat.card f.ker := fun h =>
    (by decide : ¬ 17 ∣ 3) (h.trans (ThreeCoreBounds.quotientAction_kernel_card_dvd_three i))
  have hi : ¬ 17 ∣ Nat.card f.range := by
    intro h
    have hh := h.trans f.range.card_subgroup_dvd_card
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at hh
  have hquot : ¬ 17 ∣ Nat.card (LocalQuotient i) := by
    rw [←f.ker.card_mul_index,index_ker]
    exact fun h => ((by decide : Nat.Prime 17).dvd_mul.mp h).elim hk hi
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := localOvergroup i)).exists_card_eq
  rw [←(pCore 2 (localOvergroup i)).card_mul_index,index_eq_card,hn]
  intro h
  rcases (by decide : Nat.Prime 17).dvd_mul.mp h with h | h
  · exact (by decide : ¬ 17 ∣ 2) ((by decide : Nat.Prime 17).dvd_of_dvd_pow h)
  · exact hquot h

private theorem candidate_seventeen_free (i : Fin 3) : ¬ 17 ∣ Nat.card (subgroup i) := by
  fin_cases i
  · exact max34_seventeen_free false
  · exact max34_seventeen_free true
  · change ¬ 17 ∣ Nat.card max5
    rw [InvolutionFixedData.TwoB.max5_card]
    decide

/-- Every two-local containing a full Sylow of Held has order prime to seventeen. -/
theorem not_seventeen_dvd_card_twoLocal (S : Sylow 2 He) (M : Subgroup He)
    (hM : IsTwoLocal M) (hSM : (S : Subgroup He) ≤ M) : ¬ 17 ∣ Nat.card M := by
  obtain ⟨T,hcatalogue⟩ := MaximalNormalizerCatalogue.exists_sylow_catalogue
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq He S T
  let a := MulAut.conj g
  have hT : (T : Subgroup He) ≤ M.map a.toMonoidHom := by
    have hh := map_mono (f := a.toMonoidHom) hSM
    change ((g • S : Sylow 2 He) : Subgroup He) ≤ _ at hh
    rwa [hg] at hh
  obtain ⟨N,hMN,hN⟩ := Finite.exists_le_maximal (Theory.Quasithin.isTwoLocal_map a hM)
  obtain ⟨R,hR,hRn,hRe,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le T hN (hT.trans hMN)
  obtain ⟨i,k,hk⟩ := hcatalogue R hR hRn hRe (hNR ▸ hN)
  intro hd
  have hdN : 17 ∣ Nat.card N :=
    (by rwa [card_map_of_injective a.injective] : 17 ∣ Nat.card (M.map a.toMonoidHom)).trans
      (card_dvd_of_le hMN)
  rw [hNR,hk,card_map_of_injective (MulAut.conj k).injective] at hdN
  exact candidate_seventeen_free i hdN
end Held.TwoLocalCandidates

