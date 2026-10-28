module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.BlockPlacement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Orbits
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# Cubic ranks in the literal nonsingular section centralizer

The residual has centerless quotient L_(n-1)(2). Odd-rank addition bounds
its three-rank plus that of its section centralizer by two. In degree five
the residual already has rank two, so the section centralizer has order
prime to three. This excludes the entire normal-residual branch through
the original outside-block theorem. In degree four the bound is one;
uniqueness among actual chi-blocks then makes each such block normal in
the full point centralizer, since it normalizes the section centralizer.

`CubicSource` applies these results to the original nonsingular and
zeroth-closure consumer. The degree-four cubic exclusion and the remaining
component/parabolic branches belong to qt-d-double-natural-centralizers.
Source: Aschbacher--Smith, 12.1.1, printed pp.788--789.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement IsMulCommutative
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits.AutomorphismModel
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter4 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The residual and its literal section centralizer share the ambient cubic-rank bound. -/
theorem doubleNatural_sectionCentralizer_residual_threeRank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      B.quadratic (Additive.ofMul w) = 1 →
      primeRank 3 (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w)) +
        primeRank 3 (B.pointResidual w) ≤ 2 := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  let R := B.pointResidual w
  let Y := sectionCentralizerIn (B.pointCentralizer w) R
  have hy := (le_sectionCentralizer_iff Y R).mp (show Y ≤ sectionCentralizer R from inf_le_right)
  obtain ⟨e₀⟩ := (S.nonsingular_residual_kernel_and_quotient w hw).2
  have hn : 0 < n-1 := by have := B.degree; omega
  let e := e₀.trans (projectiveEquivLinear hn)
  have hsum := ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor
    (by decide : Odd 3) Y R hy.1
    ((commutator_mono (map_subtype_le _) le_rfl).trans hy.2) (by
      rw [Nat.card_congr (centerCongr e).toEquiv,linear_center_eq_bot hn,card_bot]
      decide)
  have hH := (h.simpleQTKE.twoLocal_sqtk
    (isTwoLocal_involution_centralizer (D.doubleNatural_point_orderOf_two h B w hw))).stronglyQuasithin
  exact hsum.trans ((primeRank_mono 3 (sup_le inf_le_left
    ((B.pointResidual_le w).trans inf_le_right))).trans
      (hH 3 Nat.prime_three (by decide)))

/-- In degree five the ambient section centralizer has order prime to three. -/
theorem doubleNatural_five_sectionCentralizer_three_prime
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      B.quadratic (Additive.ofMul w) = 1 →
      Nat.Coprime 3 (Nat.card
        (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w))) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  have hsum := D.doubleNatural_sectionCentralizer_residual_threeRank h B S w hw
  obtain ⟨e₀⟩ := (S.nonsingular_residual_kernel_and_quotient w hw).2
  let e := e₀.trans (projectiveEquivLinear (by decide : 0 < 5-1))
  let : Finite (LinearGroup (5-1)) := Finite.of_equiv
    (B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) e.toEquiv
  have hR : 2 ≤ primeRank 3 (B.pointResidual w) := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
      (pCore 2 (B.pointResidual w)) pCore_isPGroup,
      primeRank_equiv 3 e,←primeRank_equiv 3 (slEquivLinear (5-1))]
    exact Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank (by decide)
  have hz : primeRank 3
      (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w)) = 0 := by omega
  exact Nat.prime_three.coprime_iff_not_dvd.mpr (PrimeRank.eq_zero_iff_not_dvd_card.mp hz)

/-- The entire degree-five normal-residual branch, assuming only the preceding characteristic-two branch. -/
theorem doubleNatural_five_adapted_normal_centralizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      B.pointCentralizer w ≤ normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc hn
  by_contra hout
  obtain ⟨K,hKY,hK,_,_,_,_⟩ :=
    D.doubleNatural_adapted_normal_outside_chiZero h B S w hw hc hn hout
  have hd : 3 ∣ Nat.card K := by
    have hd := RankOne.ChiProduct.three_dvd_card_of_chi hK.2.chi
    rwa [Nat.card_congr (subgroupOfEquivOfLe hKY).toEquiv] at hd
  exact (Nat.prime_three.coprime_iff_not_dvd.mp
    (D.doubleNatural_five_sectionCentralizer_three_prime h B S w hw.nonsingular))
      (hd.trans (card_dvd_of_le hKY))

/-- In degree four the literal section centralizer has cubic rank at most one. -/
theorem doubleNatural_four_sectionCentralizer_threeRank_le_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      B.quadratic (Additive.ofMul w) = 1 →
      primeRank 3 (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w)) ≤ 1 := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  have hsum := D.doubleNatural_sectionCentralizer_residual_threeRank h B S w hw
  obtain ⟨e₀⟩ := (S.nonsingular_residual_kernel_and_quotient w hw).2
  let e := (e₀.trans (projectiveEquivLinear (by decide : 0 < 4-1))).trans (slEquivLinear (4-1)).symm
  have hR : primeRank 3 (B.pointResidual w) ≠ 0 := by
    intro hz
    have hnd := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    apply hnd
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 (B.pointResidual w)))
    rw [Nat.card_congr e.toEquiv]
    change 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    rw [Matrix.PSL3Two.card_SL]
    decide
  omega

private theorem chi_unique_of_rank_one {A : Type*} [Group A] [Finite A]
    (hf : generalizedFitting A = pCore 2 A) (hr : primeRank 3 A ≤ 1)
    {X Y : Subgroup A} (hX : IsChiBlockIn X) (hY : IsChiBlockIn Y) : X = Y := by
  classical
  let I := {K : Subgroup A // IsChiBlockIn K}
  let : Fintype I := Fintype.ofFinite I
  have hc : Fintype.card I ≤ 1 :=
    (RankOne.ChiProduct.card_le_threeRank
      (RankOne.ChiProduct.blockCommutationHypothesis_of_fitting hf)
      (fun i : I => i.val) Subtype.val_injective (fun i => i.property)).trans hr
  have he := Fintype.card_le_one_iff.mp hc (⟨X,hX⟩ : I) ⟨Y,hY⟩
  exact congrArg Subtype.val he

/-- The unique χ-block of Y is normalized by the whole point centralizer, not merely by Y. -/
theorem doubleNatural_four_normal_chi_block_normalized
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      B.quadratic (Additive.ofMul w) = 1 →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ∀ K : Subgroup G,
        K ≤ sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w) →
        IsChiBlockIn (K.subgroupOf
          (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w))) →
        B.pointCentralizer w ≤ normalizer (K : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc hn K hKY hK
  let H := B.pointCentralizer w
  let Y := sectionCentralizerIn H (B.pointResidual w)
  have hHY : H ≤ normalizer (Y : Set G) := sectionCentralizerIn_normalized
    ((normal_subgroupOf_iff_le_normalizer ((B.pointResidual_le w).trans inf_le_right)).mp hn)
  have hf := doubleNatural_normal_sectionCentralizer_characteristic B w hc hn
  have hr := D.doubleNatural_four_sectionCentralizer_threeRank_le_one h B S w hw
  intro x hx
  let e := Y.normalizerMonoidHom ⟨x,hHY hx⟩
  have he : (K.subgroupOf Y).map e.toMonoidHom = K.subgroupOf Y :=
    chi_unique_of_rank_one hf hr (RankOne.ChiProduct.chi_map_equiv e hK) hK
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hh := congrArg (map Y.subtype) he
  rw [map_map,map_subgroupOf_eq_of_le hKY] at hh
  calc
    K.map (MulAut.conj x).toMonoidHom =
        ((K.subgroupOf Y).map Y.subtype).map (MulAut.conj x).toMonoidHom := by
      rw [map_subgroupOf_eq_of_le hKY]
    _ = (K.subgroupOf Y).map (Y.subtype.comp e.toMonoidHom) := by
      rw [map_map]
      rfl
    _ = K := hh

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
