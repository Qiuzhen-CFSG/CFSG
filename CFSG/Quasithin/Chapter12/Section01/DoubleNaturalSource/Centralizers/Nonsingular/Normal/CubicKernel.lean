module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.LocalKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedSetup
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank

/-!
# The three-prime kernel in the normal nonsingular branch

The original L/O₂(L) has three-rank at least two in both degrees. The
kernel on W centralizes this exact section. Odd-rank addition in its join
with L and quasithinness of N_G(L) force the kernel to have three-rank
zero; Cauchy's theorem makes its order prime to three. `LocalKernel`
then gives the same conclusion for C_{M_w}(L_w/O₂(L_w)).

`LocalSource` applies the bound to the actual outside block's intersection
with M. The A₅ Borel-placement argument is still required by
qt-d-double-natural-centralizers; qt-d-1222-double-natural owns final assembly.
Source: Aschbacher--Smith, 12.1.1, printed p.788, using the rank argument
underlying A.3.18. No classification callback is used here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement IsMulCommutative
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits.AutomorphismModel
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal normalizer kernel on the doubled orbit has order prime to three. -/
theorem doubleNatural_orbitCentralizer_three_prime
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    Nat.Coprime 3 (Nat.card (normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) : Subgroup G)) := by
  let : Finite (LinearGroup n) := Finite.of_equiv (L ⧸ pCore 2 L) B.component.toEquiv
  let C := normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G)
  have hcomm : ⁅C,L⁆ ≤ L.pCoreIn 2 := by
    apply commutator_le.mpr
    intro c hc l hl
    let cm : normalizer (L : Set G) := ⟨c,hc.1⟩
    let lm : normalizer (L : Set G) := inclusion L.le_normalizer ⟨l,hl⟩
    have hfc : B.actionProjection cm = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [normalizerAction_ker]
      exact hc.2
    have hcl : ⁅c,l⁆ ∈ L := le_normalizer_iff_commutator_le_right.mp
      (show C ≤ normalizer (L : Set G) from inf_le_left)
      (commutator_mem_commutator hc hl)
    let u : L := ⟨⁅c,l⁆,hcl⟩
    have hu : B.componentToActionQuotient u = 1 := by
      change B.actionProjection ⁅cm,lm⁆ = 1
      rw [map_commutatorElement,hfc,commutatorElement_one_left]
    exact ⟨u,B.componentToActionQuotient_ker ▸ hu,rfl⟩
  have hsum := ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor
    (by decide : Odd 3) C L inf_le_left
    ((commutator_mono (map_subtype_le _) le_rfl).trans hcomm) (by
      rw [Nat.card_congr (centerCongr B.component).toEquiv,
        linear_center_eq_bot (by have := B.degree; omega),card_bot]
      decide)
  have hN : IsStronglyQuasithin (normalizer (L : Set G)) :=
    (h.simpleQTKE.twoLocal_sqtk (D.doubledNormalizer_unique h).1.1).stronglyQuasithin
  have hupper : primeRank 3 (C ⊔ L : Subgroup G) ≤ 2 :=
    (primeRank_mono 3 (sup_le inf_le_left L.le_normalizer)).trans
      (hN 3 Nat.prime_three (by decide))
  have hL : 2 ≤ primeRank 3 L := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 L) pCore_isPGroup,
      primeRank_equiv 3 B.component,←primeRank_equiv 3 (slEquivLinear n)]
    exact Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank
      (by have := B.degree; omega)
  have hz : primeRank 3 C = 0 := by omega
  exact Nat.prime_three.coprime_iff_not_dvd.mpr (PrimeRank.eq_zero_iff_not_dvd_card.mp hz)

/-- The nonsingular local section centralizer has order prime to three. -/
theorem doubleNatural_local_sectionCentralizer_three_prime
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      B.quadratic (Additive.ofMul w) = 1 →
      Nat.Coprime 3 (Nat.card
        (sectionCentralizerIn (B.localPointCentralizer w) (B.pointResidual w))) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  rw [S.nonsingular_local_sectionCentralizer_eq w hw]
  exact (D.doubleNatural_orbitCentralizer_three_prime h B).coprime_dvd_right
    (card_dvd_of_le (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
