module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.PrimeBounds.Solvable
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Targets

/-!
# The maximal-prime bound for all solvable overgroups

Every H ≤ J ≤ Mc contains the nontrivial two-core of Mc, since it contains
T. Thus J itself belongs to the actual outside family. The original global
maximal-prime choice bounds every odd prime core of J/O₂(J). Odd-prime
rank passes through the two-group kernel, and the solvable prime-support
argument gives exactly {2,3} or {2,3,5}, according to the chosen p.

This proves the first paragraph of 14.6.14 without assuming a closure
classification, solvability of Mc, or a bound only on the chosen H. The
remaining Suzuki and strict-closure arguments stay with the same source
assembly owner, qt-e-suitable-odd-normalizer.

Source: Aschbacher--Smith, printed p.1032.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))

include hH hunique in
omit [Finite G] in
/-- Every literal intermediate subgroup is in the same outside family. -/
theorem source_intermediate_outside (J : Subgroup G) (hHJ : H ≤ J) (hJMc : J ≤ Mc) :
    J ∈ Chapter1.HOutside G (T : Set G) (M : Set G) := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hunique.symm ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := hH.1.2.trans (hHJ.trans hJMc)
  have hQT : Mc.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] using
      pCoreIn_le_sylow Mc (T.subtype hTMc)
  have hn : Mc ≤ normalizer (Mc.pCoreIn 2 : Set G) := Mc.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  have hle := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Mc)
    (hQT.trans (hH.1.2.trans hHJ)) (hJMc.trans hn)
  refine ⟨⟨?_,hH.1.2.trans hHJ⟩,fun hh => hH.2 (hHJ.trans hh)⟩
  exact fun hz => Chapter1.mem_H_of_isTwoLocal hMc.1.1 (le_bot_iff.mp (hle.trans hz.le))

include hG hunique hH in
/-- The actual maximal-prime choice gives the full solvable-overgroup prime bound. -/
theorem source_solvable_overgroup_prime_bound
    {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hmax : MaximalOddPrime (T : Subgroup G) M p) : SolvableOvergroupPrimeBound H Mc p := by
  intro J hHJ hJMc hs r hr hd
  have hout := source_intermediate_outside T hunique H hH J hHJ hJMc
  let : Group.IsSolvable J := hs
  have hc := (pCore 2 J).card_mul_index
  rw [←hc] at hd
  rcases hr.dvd_mul.mp hd with hcore | hquot
  · obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := J)).exists_card_eq
    rw [hn] at hcore
    exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hr Nat.prime_two hcore)
  · exact solvable_prime_support_of_small_odd_cores inferInstance
      (pCore_quotient_pCore_eq_bot 2) hp
      (hmax J hout)
      (fun q hq ho => by
        let : Fact q.Prime := ⟨hq⟩
        exact (primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 J) pCore_isPGroup).trans
          ((Chapter3.sqtk_of_mem_H hG hout.1.1).stronglyQuasithin q hq ho)) hr hquot
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
