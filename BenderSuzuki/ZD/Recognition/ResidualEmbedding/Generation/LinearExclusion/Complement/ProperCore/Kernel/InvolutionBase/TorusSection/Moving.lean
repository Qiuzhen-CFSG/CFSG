module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.TorusSection.Containment
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl
public import Theory.GroupAction.CoprimeMovingSection
import Mathlib.GroupTheory.Exponent

/-!
# The moving torus section from the elementary quotient

Inside M write A for the distinguished closure, R for the normal closure
of J = C_G(L), and K for the literal subgroup (D ∩ L). The preceding
containment theorem gives A ≤ [R,K]. Under the explicit square hypothesis,
R/A is abelian. Coprime fixed-point lifting identifies its fixed subgroup
with the image of J, of order two, and its moving subgroup with the image
of [R,K]. Consequently [R,K] has order q².

For each nonidentity k in K, localization gives C_R(k) = J. Fixed-point
lifting and disjointness of the abelian fixed and moving factors make K
act freely on the nonidentity elements of the moving quotient. Its order
is q and |K| = q−1, so this action is transitive. Transporting the quotient
equality gives precisely y = k*x*k⁻¹*a with a in A.

The square hypothesis and earlier centralizer-closure collapse remain
explicit source premises. Their discharge belongs to the torus-section
and involution-base assemblies, respectively. No normality in M or
commutativity of [R,K] is assumed or asserted here.

Source: GLS, Volume 4, Chapter 2, opening of Lemma 15.7,
`refs/KGroup/GLS4/Chapter2.tex`, lines 2737–2745.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory

/-- The source moving section of R/A has order q, and lifts to a subgroup
of order q² on whose nontrivial A-cosets the literal torus acts transitively.
The square hypothesis is the preceding elementary-quotient obligation. -/
public theorem linear_involutionBase_moving_section_of_squares
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hfixed : pCore 2 M ⊓
      centralizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t)
    (hsq : ∀ x ∈ linearCentralizerClosure M z t,
      x ^ 2 ∈ (closure (Z ∩ (M : Set G))).subgroupOf M) :
    Nat.card (linearCommutatorKernel M z t) = (2 ^ n) ^ 2 ∧
      ∀ x ∈ linearCommutatorKernel M z t,
        x ∉ (closure (Z ∩ (M : Set G))).subgroupOf M →
        ∀ y ∈ linearCommutatorKernel M z t,
          y ∉ (closure (Z ∩ (M : Set G))).subgroupOf M →
          ∃ k ∈ (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M,
            ∃ a ∈ (closure (Z ∩ (M : Set G))).subgroupOf M, y = k * x * k⁻¹ * a := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let R := linearCentralizerClosure M z t
  let B := linearCommutatorKernel M z t
  let K := (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M
  let J := (centralizer (residualGenerated M z t : Set G)).subgroupOf M
  let V := pCore 2 M
  let : A.Normal := distinguishedClosure_normal h.disconnected
  let : R.Normal := normalClosure_normal
  have hRV : R ≤ V := linearCentralizerClosure_le_twoCore hR
  have hBR : B ≤ R := linearCommutatorKernel_le_closure
  have hJR : J ≤ R := subset_normalClosure
  have hAB : A ≤ B := linear_distinguishedClosure_le_commutatorKernel_of_centralizerClosure
    h r hz hzM ht htM hL hn e hJ hR hAL hcollapse
  have hAR : A ≤ R := hAB.trans hBR
  obtain ⟨_, _, hAcard⟩ := linear_distinguishedClosure_internal_facts
    h.disconnected r hz hzM ht htM hL hn e hAL
  obtain ⟨hKcard, hfree⟩ := linear_distinguishedClosure_torus_geometry
    h r hz hzM ht htM hL hn e hAL
  have hlocal := linear_involution_localization_of_centralizerClosure h.disconnected r
    hz hzM ht htM hL hn e hAL hJ hcollapse
  have helement := linear_twoCore_element_centralizer_of_localization
    h.disconnected hz hzM hJ hR hlocal hfree
  let N := A.subgroupOf R
  have hNcard : Nat.card N = 2 ^ n :=
    (Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv).trans hAcard
  have hInv : IsInvariant K R N := by
    constructor
    intro k x
    change (x : M) ∈ A ↔ (k : M) * (x : M) * (k : M)⁻¹ ∈ A
    exact mem_normalizer_iff.mp
      (show (k : M) ∈ normalizer (A : Set M) from le_normalizer_of_normal (mem_top _)) x
  have hRp : IsPGroup 2 R := (pCore_isPGroup (p := 2) (G := M)).to_le hRV
  let : Group.IsNilpotent R := hRp.isNilpotent
  have hodd : Odd (Nat.card K) := by
    rw [show Nat.card K = Nat.card
      (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) from
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).toEquiv]
    exact pair_inf_proper_residualGenerated_odd h.disconnected r hz hzM ht htM hL
  have hcop : Nat.Coprime (Nat.card K) (Nat.card R) := by
    obtain ⟨m, hm⟩ := hRp.exists_card_eq
    rw [hm]
    exact hodd.coprime_two_right.pow_right m
  have hQsq : ∀ x : R ⧸ N, x ^ 2 = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hsq y y.property)
  let : IsMulCommutative (R ⧸ N) :=
    ⟨⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun g => orderOf_dvd_iff_pow_eq_one.mpr (hQsq g)) x y).eq⟩⟩
  have hRJ : R ⊓ centralizer (K : Set M) = J :=
    linearCentralizerClosure_inf_centralizer hR hfixed
  have hF : fixedPointSubgroup K R = J.subgroupOf R := by
    have hh := fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn R K
      (show K ≤ normalizer (R : Set M) from le_normalizer_of_normal)
    change fixedPointSubgroup K R = (R ⊓ centralizer (K : Set M)).subgroupOf R at hh
    exact hh.trans (congrArg (fun S : Subgroup M => S.subgroupOf R) hRJ)
  have hFcard : Nat.card (fixedPointSubgroup K R) = 2 := by
    rw [hF]
    exact (Nat.card_congr (subgroupOfEquivOfLe hJR).toEquiv).trans
      (linearCentralizer_subgroupOf_card h.disconnected hz hzM hJ)
  have hCmap : (commutatorAction K R).map R.subtype = B :=
    commutatorAction_subgroup_conj_map_eq_commutator R K le_normalizer_of_normal
  have hCmem (x : R) : x ∈ commutatorAction K R ↔ (x : M) ∈ B := by
    rw [← hCmap]
    constructor
    · intro hx
      exact mem_map_of_mem R.subtype hx
    · rintro ⟨y, hy, he⟩
      exact (Subtype.ext he : y = x) ▸ hy
  have hNC : N ≤ commutatorAction K R := fun x hx => (hCmem x).mpr (hAB hx)
  have hq : 4 ≤ 2 ^ n := (show 4 = 2 ^ 2 by norm_num) ▸
    Nat.pow_le_pow_right (by decide) hn
  let : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hKcard]
    omega)
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  have hNF : Disjoint N (fixedPointSubgroup K R) := by
    apply disjoint_def.mpr
    intro x hxN hxF
    have hxC : (x : M) ∈ centralizer ({(k : M)} : Set M) := by
      have hh := congrArg Subtype.val (hxF k)
      change (k : M) * (x : M) * (k : M)⁻¹ = (x : M) at hh
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hh : (x : M) ∈ A ⊓ centralizer ({(k : M)} : Set M) := ⟨hxN, hxC⟩
    rw [hfree k k.property (fun he => hk (Subtype.ext he)), mem_bot] at hh
    exact Subtype.ext hh
  have hpoint : ∀ k : K, k ≠ 1 → ∀ x : R,
      k • x = x → x ∈ fixedPointSubgroup K R := by
    intro k hk x hx
    rw [hF]
    change (x : M) ∈ (centralizer (residualGenerated M z t : Set G)).subgroupOf M
    rw [← helement k k.property (fun he => hk (Subtype.ext he))]
    refine ⟨hRV x.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have hh := congrArg Subtype.val hx
    change (k : M) * (x : M) * (k : M)⁻¹ = (x : M) at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  obtain ⟨hCcard, horbit⟩ := Theory.GroupAction.moving_section_of_abelian_quotient N hInv
    inferInstance hcop hNC hNF hpoint (by rw [hFcard, hNcard]; exact hR)
    (by rw [hNcard, hKcard]; omega)
  constructor
  · change Nat.card B = (2 ^ n) ^ 2
    rw [← hCmap, card_map_of_injective R.subtype_injective, hCcard, hNcard]
  · intro x hx hxA y hy hyA
    let xR : R := ⟨x, hBR hx⟩
    let yR : R := ⟨y, hBR hy⟩
    obtain ⟨k, a, ha, he⟩ := horbit xR ((hCmem xR).mpr hx) hxA
      yR ((hCmem yR).mpr hy) hyA
    exact ⟨k, k.property, a, ha, congrArg Subtype.val he⟩

end BenderSuzuki.ZD
