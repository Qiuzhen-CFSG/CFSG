module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreKernel
public import Theory.GroupTheory.Fitting.SmallOddCore

/-!
# The original three-core and odd-core alternatives

The action-kernel argument bounds O₃(I/O₂(I)) by three. If it is
nontrivial, lift it as an actual normal two-perfect cubic. The full
preimage lies in M, so the strict-intersection argument forces L₁ into
this lift. Its nonzero star image exhausts the three-core, proving
14.7.27 with the literal original quotient map.

The odd core is solvable by the odd-order theorem. Its Fitting subgroup
lies in the same three-core. The small-Fitting lemma makes the entire
odd core a three-group, hence it equals the three-core. This proves
14.7.28 without assuming the point normal in I or I solvable.

The proof uses the independently established 14.7.29 and the A.3.6
quasisimplicity reduction; neither depends on these new alternatives.
The component and module classification through 14.7.52 remains.

Source: Aschbacher–Smith, 14.7.27–28, printed pp.1054–1055,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Source 14.7.27 for every original local, with the actual point image. -/
theorem local_threeCore_eq_bot_or_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    pCore 3 (HStar I) = ⊥ ∨ pCore 3 (HStar I) =
      ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) := by
  let P := pCore 3 (HStar I)
  let q := QuotientGroup.mk' (pCore 2 I)
  let A := (F.Li L 1).subgroupOf I
  by_cases hb : P = ⊥
  · exact Or.inl hb
  right
  have hc : Nat.card P = 3 := by
    have hbound := local_threeCore_card_le_three d h hab structural previous faithful earlier I hI
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := HStar I)).exists_card_eq
    have hnpos : n ≠ 0 := by
      intro he
      apply hb
      apply card_eq_one.mp
      rw [hn,he,pow_zero]
    have hlow : 3 ≤ Nat.card P := by
      rw [hn]
      exact Nat.le_of_dvd (pow_pos (by decide) _) (dvd_pow_self 3 hnpos)
    exact le_antisymm hbound hlow
  obtain ⟨Y,hYn,_,_,hYm,hYk,⟨eY⟩⟩ := exists_normal_three_residual_lift q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    P pCore_isPGroup
  let := hYn
  have hY3 : IsPGroup 3 (Y ⧸ pCore 2 Y) := pCore_isPGroup.of_equiv eY.symm
  have hYc : Nat.card (Y ⧸ pCore 2 Y) = 3 := (Nat.card_congr eY.toEquiv).trans hc
  have hYM : Y.map I.subtype ≤ normalizer (L : Set G) :=
    (map_mono (show Y ≤ P.comap q from map_le_iff_le_comap.mp hYm.le)).trans
      (local_threeCore_preimage_control d h hab structural previous faithful earlier I hI).1
  have hi := local_lift_intersection_of_cubic_sublift h structural I hI Y Y le_rfl hYM hYk hYc
  have hAY := local_three_lift_contains_point h structural I hI Y hY3 hi
  have hAP : A.map q ≤ P := (map_mono hAY).trans hYm.le
  have hAne : A.map q ≠ ⊥ := by
    intro he
    have hAQ : A ≤ pCore 2 I := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff A).mp he
    have hA2 : IsPGroup 2 (F.Li L 1) :=
      (pCore_isPGroup.to_le hAQ).of_equiv (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hI))
    have hdiv : 3 ∣ Nat.card (F.Li L 1) := by
      have hd := card_quotient_dvd_card (pCore 2 (F.Li L 1))
      rwa [pointResidual_core_quotient_card h structural] at hd
    obtain ⟨n,hn⟩ := hA2.exists_card_eq
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (hn ▸ hdiv)
    norm_num at h32
  have hAc : Nat.card (A.map q) = 3 := by
    have hh := card_dvd_of_le hAP
    rw [hc] at hh
    exact ((Nat.dvd_prime Nat.prime_three).mp hh).resolve_left
      (fun he => hAne (card_eq_one.mp he))
  exact (eq_of_le_of_card_ge hAP (by rw [hc,hAc])).symm

/-- Source 14.7.28: the full odd core is trivial or the literal point cubic. -/
theorem local_oddCore_eq_bot_or_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    pPrimeCore 2 (HStar I) = ⊥ ∨ pPrimeCore 2 (HStar I) =
      ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) := by
  have hs : Group.IsSolvable (pPrimeCore 2 (HStar I)) :=
    odd_order_theorem _ (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  rw [oddCore_eq_threeCore_of_small_fitting hs
    (local_fitting_eq_threeCore h hab structural previous faithful I hI)
    (local_threeCore_card_le_three d h hab structural previous faithful earlier I hI)]
  exact local_threeCore_eq_bot_or_point d h hab structural previous faithful earlier I hI

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
