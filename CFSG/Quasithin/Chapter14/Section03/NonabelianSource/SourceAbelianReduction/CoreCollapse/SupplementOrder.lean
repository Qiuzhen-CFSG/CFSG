module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.Defs
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockSupplement
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorSupplementAction

/-!
# The order of the original centralizing supplement

Self-centralization of the marked elementary factor excludes the order-eight
case of the faithful dihedral action. Lagrange's theorem and the strict
containment of the point then force the supplement to have order four.
This proves the order assertion; cyclicity still requires excluding the two
reflection classes in the actual block action.

Source: Aschbacher--Smith 14.3.22, printed p.998.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]

/-- Under the original self-centralization hypothesis, the proper supplement has order four. -/
theorem source_supplement_card_four
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hproper : F.Vi 1 < F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)) :
    Nat.card (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G) : Subgroup G) = 4 := by
  let D := F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)
  obtain ⟨_, A, hAR, hVA, hEA, hAc, hc8, hAN, _⟩ :=
    source_factor_supplement_action_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  let := hEA
  have hselfA := hself A hEA hAR hVA hAc hc8 hAN
  obtain ⟨j, hj, hDc⟩ := source_factor_block_supplement_dihedral_embedding_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  have hdiv : Nat.card D ∣ 8 := by
    simpa only [DihedralGroup.nat_card] using Subgroup.card_dvd_of_injective j hj
  have hne8 : Nat.card D ≠ 8 := by
    intro hc
    have hbij : Function.Bijective j := hj.bijective_of_nat_card_le (by
      simpa only [DihedralGroup.nat_card] using hc.ge)
    have hh := (source_factor_block_supplement_dihedral_iff_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN).mp
        ⟨MulEquiv.ofBijective j hbij⟩
    exact hh.2.ne hselfA
  have hz : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hlt : 2 < Nat.card D := by
    by_contra! hc
    exact hproper.ne (eq_of_le_of_card_ge hproper.le (by simpa only [hz] using hc))
  change Nat.card D = 4
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card D ∣ 2 ^ 3 from hdiv)
  interval_cases i
  · change Nat.card D = 1 at he
    omega
  · change Nat.card D = 2 at he
    omega
  · exact he
  · exact False.elim (hne8 he)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse
