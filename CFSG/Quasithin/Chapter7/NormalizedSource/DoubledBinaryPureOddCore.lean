module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddCore
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureFactors
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.NormalizedSupCard
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlanes

/-!
# Odd-core reduction at a pure binary line

The source pure line lies in a paired plane of order four. Its local
residual contains that plane's residual, whose moved subgroup supplements
the plane in the original natural–dual orbit. Thus the pure-line residual
moves a subgroup of codimension at most two.

For the chosen-module application, the established bound r ≥ 3 controls
this moved subgroup's centralizer. A.1.26 makes it centralize the odd core
of a local-base overgroup; characteristic two of the intersection with M
then eliminates that odd core. This is the odd-core step of Proposition
7.7.2. Ordinary-component elimination is a separate remaining obligation.

Source: Aschbacher–Smith A.1.26 and 7.7.3, printed pp.705–706,
refs/quasithin.pdf. The actual application is NonFFSourceDoubledBinaryPureOddCore.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureOddCore
open ChapterE BinaryLinearThree NaturalDual DoubledBinaryPlanes DoubledBinaryLocalCore
open DoubledBinaryOddCore
variable {G : Type*} [_root_.Group G] [Finite G]

/-- The literal pure-line residual moves a subgroup of index at most four
in the whole doubled orbit, retaining the original component action. -/
theorem naturalLine_residual_relIndex_le_four
    (W₀ L A Z : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G)) (hAW : A ≤ W₀)
    (q : L →* Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) = action (q l) (E w))
    (hA : ∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ A)
    (hZ : Nat.card Z = 2) (hZA : Z ≤ A) :
    (⁅W₀,localResidual L Z⁆).relIndex W₀ ≤ 4 := by
  obtain ⟨z,hz,hall⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  let w : Additive W₀ := Additive.ofMul ⟨z,hAW (hZA z.property)⟩
  have hw : (E w).2 = 0 := (hA w).mpr (hZA z.property)
  have hv : (E w).1 ≠ 0 := by
    intro he
    have hh := E.map_eq_zero_iff.mp (Prod.ext he hw)
    exact hz (Subtype.ext (congrArg (fun a : Additive W₀ => (a.toMul : G)) hh))
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hv
  let U := ambientPlane W₀ E (E w).1 f
  have hzU : (z : G) ∈ U := by
    refine ⟨w.toMul,?_,rfl⟩
    change E w ∈ pairedPlane (E w).1 f
    rw [← show ((E w).1,0) = E w from Prod.ext rfl hw.symm]
    exact Submodule.subset_span (by simp)
  have hZU : Z ≤ U := by
    intro x hx
    by_cases he : (⟨x,hx⟩ : Z) = 1
    · have he' : x = 1 := congrArg Subtype.val he
      exact he'.symm ▸ U.one_mem
    · have he' : x = z := congrArg Subtype.val (hall ⟨x,hx⟩ he)
      exact he'.symm ▸ hzU
  let R := localResidual L Z
  let N := ⁅W₀,R⁆
  have hRN : R ≤ normalizer (W₀ : Set G) :=
    (map_subtype_le _).trans (inf_le_left.trans hLN)
  have hNW : N ≤ W₀ := le_normalizer_iff_commutator_le_left.mp hRN
  have hgen : U ⊔ N = W₀ := by
    apply le_antisymm (sup_le (ambientPlane_le_orbit W₀ E _ f) hNW)
    exact (pairedPlane_residual_supplement W₀ L hLN q hq E hE (E w).1 f hf).symm.le.trans
      (sup_le_sup_left (commutator_mono le_rfl
        (embedded_pResidual_mono 2 (inf_le_inf_left L (centralizer_le hZU)))) U)
  have hcount := card_mul_eq_card_inf_mul_card_sup_of_normalizes U N
    ((hNW.trans ((le_centralizer W₀).trans
      (centralizer_le (ambientPlane_le_orbit W₀ E _ f)))).trans
        (Subgroup.centralizer_le_normalizer _))
  have hU : Nat.card U = 4 := DoubledBinaryPlaneQuotient.ambientPlane_card W₀ E _ f hf
  rw [hgen,hU] at hcount
  have hindex := relIndex_mul_relIndex (⊥ : Subgroup G) N W₀ bot_le hNW
  simp only [relIndex_bot_left] at hindex
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hI : 1 ≤ Nat.card (U ⊓ N : Subgroup G) := Nat.card_pos
  have hle : Nat.card W₀ ≤ 4 * Nat.card N := by nlinarith
  change N.relIndex W₀ ≤ 4
  nlinarith

/-- The moved subgroup centralizes the odd core by A.1.26. Its centralizer
control then puts the whole odd core inside the characteristic-two intersection. -/
theorem oddCore_eq_bot_of_moved_centralizer
    (W₀ R H M : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hR : IsPPerfect 2 R) (hRN : R ≤ normalizer (W₀ : Set G))
    (hWH : W₀ ≤ H) (hRH : R ≤ H)
    (hAM : centralizer ((⁅W₀,R⁆ : Subgroup G) : Set G) ≤ M)
    (hSQ : IsStronglyQuasithin H)
    (hMH : HasCharacteristicTwo (H ⊓ M : Subgroup G)) :
    pPrimeCore 2 H = ⊥ := by
  let A := ⁅W₀,R⁆
  have hAW : A ≤ W₀ := le_normalizer_iff_commutator_le_left.mp hRN
  have hAH : A ≤ H := hAW.trans hWH
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (inclusion hAW) (inclusion_injective hAW)
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  have hpR : IsPPerfect 2 (R.subgroupOf H) := hR.of_surjective
    (subgroupOfEquivOfLe hRH).symm.toMonoidHom (subgroupOfEquivOfLe hRH).symm.surjective
  have hcomm : ⁅A.subgroupOf H,R.subgroupOf H⁆ = A.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hRH]
    exact commutator_isPPerfect_idempotent R W₀ hR (IsElementaryAbelian.isPGroup 2 W₀) hRN
  have hcent := ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hSQ
    (R.subgroupOf H) (A.subgroupOf H) hpR hcomm
  let O := (pPrimeCore 2 H).map H.subtype
  have hAO : ⁅A,O⁆ = ⊥ := by
    have hh := congrArg (Subgroup.map H.subtype) hcent
    simpa only [map_commutator,map_subgroupOf_eq_of_le hAH,Subgroup.map_bot] using hh
  have hOM : O ≤ M := (le_centralizer_iff.mpr
    (commutator_eq_bot_iff_le_centralizer.mp hAO)).trans hAM
  let N := M.subgroupOf H
  have hcN : HasCharacteristicTwo N := by
    have hh := hMH.of_equiv (subgroupOfEquivOfLe (H := H ⊓ M) inf_le_left).symm
    exact hh.of_equiv (MulEquiv.subgroupCongr (inf_subgroupOf_left M H))
  have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 H).subgroupOf N)) := by
    rw [← inf_subgroupOf_right,
      Nat.card_congr (subgroupOfEquivOfLe (H := pPrimeCore 2 H ⊓ N) inf_le_right).toEquiv]
    exact pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le inf_le_left)
  have hz : (pPrimeCore 2 H).subgroupOf N = ⊥ := by
    have hh : (pPrimeCore 2 H).subgroupOf N ≤ pPrimeCore 2 N := le_sSup ⟨inferInstance,hcop⟩
    rw [pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hcN] at hh
    exact le_bot_iff.mp hh
  apply le_bot_iff.mp
  intro x hx
  have hm : x ∈ N := hOM (mem_map_of_mem H.subtype hx)
  have hh : (⟨x,hm⟩ : N) ∈ (pPrimeCore 2 H).subgroupOf N := hx
  rw [hz] at hh
  exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hh))

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureOddCore
