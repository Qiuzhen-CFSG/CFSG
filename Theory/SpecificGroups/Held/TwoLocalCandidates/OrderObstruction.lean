module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.ThreeCoreBounds
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue
public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.Quasithin.EvenCharacteristic

/-!
# The 63 obstruction in Held two-local subgroups

A two-local containing a full Sylow subgroup lies in a maximal two-local.
The native normal-elementary catalogue identifies its actual conjugate
with one of max3, max4 or max5. The first two have a two-core quotient
mapping to S₆ with kernel of order dividing three, so their orders are
prime to seven. The last has order 21504, indivisible by nine.

Source: GLS3 Table 5.3p and Aschbacher–Smith A.3.12, pp.47–48.
The original non-A₅ point-component comparison applies this to the literal
normalizer of its moved elementary image in I/Z(I).
-/

public section
open Subgroup Theory.GroupTheory
namespace Held.TwoLocalCandidates
open LocalPairs.PairCoverage LocalPairs.PairCoverage.IntervalNormalizer.Inner

private theorem max34_seven_free (i : Bool) : ¬ 7 ∣ Nat.card (localOvergroup i) := by
  let q := localQuotientMap i
  let f := SixPoint.quotientAction i
  have hk : ¬ 7 ∣ Nat.card f.ker := fun h =>
    (by decide : ¬ 7 ∣ 3) (h.trans (ThreeCoreBounds.quotientAction_kernel_card_dvd_three i))
  have hi : ¬ 7 ∣ Nat.card f.range := by
    intro h
    have hh := h.trans f.range.card_subgroup_dvd_card
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at hh
  have hquot : ¬ 7 ∣ Nat.card (LocalQuotient i) := by
    rw [←f.ker.card_mul_index,index_ker]
    exact fun h => ((by decide : Nat.Prime 7).dvd_mul.mp h).elim hk hi
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := localOvergroup i)).exists_card_eq
  rw [←(pCore 2 (localOvergroup i)).card_mul_index,index_eq_card,hn]
  intro h
  rcases (by decide : Nat.Prime 7).dvd_mul.mp h with h | h
  · exact (by decide : ¬ 7 ∣ 2) ((by decide : Nat.Prime 7).dvd_of_dvd_pow h)
  · exact hquot h

private theorem candidate_sixtythree_free (i : Fin 3) : ¬ 63 ∣ Nat.card (subgroup i) := by
  fin_cases i
  · exact fun h => max34_seven_free false ((by decide : 7 ∣ 63).trans h)
  · exact fun h => max34_seven_free true ((by decide : 7 ∣ 63).trans h)
  · change ¬ 63 ∣ Nat.card max5
    rw [InvolutionFixedData.TwoB.max5_card]
    decide

/-- A full-Sylow two-local in Held cannot have both a factor seven and a factor nine. -/
theorem not_sixtythree_dvd_card_twoLocal (S : Sylow 2 He) (M : Subgroup He)
    (hM : IsTwoLocal M) (hSM : (S : Subgroup He) ≤ M) : ¬ 63 ∣ Nat.card M := by
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
  have hdN : 63 ∣ Nat.card N :=
    (by rwa [card_map_of_injective a.injective] : 63 ∣ Nat.card (M.map a.toMonoidHom)).trans
      (card_dvd_of_le hMN)
  rw [hNR,hk,card_map_of_injective (MulAut.conj k).injective] at hdN
  exact candidate_sixtythree_free i hdN
end Held.TwoLocalCandidates

