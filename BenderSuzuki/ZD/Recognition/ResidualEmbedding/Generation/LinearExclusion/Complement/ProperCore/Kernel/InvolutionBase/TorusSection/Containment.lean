module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.Distinguished
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.Reduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Geometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Torus
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupAction.RegularNonidentityOrbit

/-!
# The distinguished layer lies in the moving kernel

Write `A = ⟨Z ∩ M⟩`, `R = ⟨Jᴹ⟩` and `K = D ∩ L`, all inside M.
The source localization `C_V(J) ≤ AJ` first forces `A ∩ R ≠ 1`:
otherwise J would be a self-centralizing subgroup of order two in the
larger two-group R, contradicting the normalizer condition. The actual
PSL₂ torus acts freely on A away from the identity and has order |A|−1,
so its orbit of any nonidentity element of `A ∩ R` fills A. Thus A ≤ R.
Coprime action and `C_A(K) = 1` then give `A = [A,K] ≤ [R,K]`.

This proves the first clause of the requested torus section without
assuming the elementary quotient, the order of the moving kernel, or its
abelian structure. The elementary quotient and its moving summand remain
separate source obligations. The permitted earlier centralizer-closure
collapse remains explicit, with final discharge owned by the involution
base assembly. Source: GLS, Volume 4, Chapter 2, Lemma 15.6 and the opening
of 15.7, `refs/KGroup/GLS4/Chapter2.tex`, lines 2703–2745.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory

private theorem root_le_normal_of_localization
    {H : Type*} [Group H] [Finite H] (V R A J K : Subgroup H)
    [R.Normal] [A.Normal] (hRp : IsPGroup 2 R)
    (hRV : R ≤ V) (hJR : J ≤ R) (hJ : Nat.card J = 2)
    (hR : 2 < Nat.card R)
    (hlocal : V ⊓ centralizer (J : Set H) ≤ A ⊔ J)
    (hcard : Nat.card A = Nat.card K + 1)
    (hfree : ∀ k ∈ K, k ≠ 1 → A ⊓ centralizer ({k} : Set H) = ⊥) : A ≤ R := by
  have hnon : A ⊓ R ≠ ⊥ := by
    intro hbot
    let : Group.IsNilpotent R := hRp.isNilpotent
    have hRJ : R ≤ J := le_of_nilpotent_of_card_two_of_centralizer_le R J hJR hJ (by
      intro x hx
      obtain ⟨a, ha, j, hj, he⟩ := mem_sup_of_normal_left.mp (hlocal ⟨hRV hx.1, hx.2⟩)
      have haR : a ∈ R := by
        have hh := R.mul_mem hx.1 (R.inv_mem (hJR hj))
        rwa [← he, mul_inv_cancel_right] at hh
      have ha1 : a = 1 := by
        have hh : a ∈ A ⊓ R := ⟨ha, haR⟩
        simpa only [hbot, mem_bot] using hh
      simpa only [← he, ha1, one_mul] using hj)
    have hc := Nat.card_le_card_of_injective (Subgroup.inclusion hRJ)
      (Subgroup.inclusion_injective hRJ)
    rw [hJ] at hc
    omega
  obtain ⟨xx, hxx⟩ := ne_bot_iff_exists_ne_one.mp hnon
  let x : H := xx
  have hx : x ∈ A ⊓ R := xx.property
  have hx1 : x ≠ 1 := fun he => hxx (Subtype.ext he)
  have hfree' : ∀ k : K, k ≠ 1 → ∀ a : A, k • a = a → a = 1 := by
    intro k hk a ha
    apply Subtype.ext
    change (a : H) = 1
    have hh := congrArg Subtype.val ha
    change (k : H) * (a : H) * (k : H)⁻¹ = a at hh
    have hm : (a : H) ∈ A ⊓ centralizer ({(k : H)} : Set H) :=
      ⟨a.property, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm⟩
    simpa only [hfree k k.property (fun he => hk (Subtype.ext he)), mem_bot] using hm
  intro a ha
  by_cases ha1 : a = 1
  · simpa only [ha1] using R.one_mem
  obtain ⟨k, hk⟩ := Theory.GroupAction.exists_smul_eq_of_free_of_card hcard hfree'
    (x := (⟨x, hx.1⟩ : A)) (y := (⟨a, ha⟩ : A))
    (fun he => hx1 (congrArg Subtype.val he)) (fun he => ha1 (congrArg Subtype.val he))
  have hh : (k : H) * x * (k : H)⁻¹ = a := congrArg Subtype.val hk
  exact hh ▸ (inferInstance : R.Normal).conj_mem x hx.2 k

/-- The actual distinguished closure lies in the literal commutator kernel.
Localization first forces its intersection with R to be nontrivial; the
actual torus orbit fills A, and coprime action gives A = [A,K]. -/
public theorem linear_distinguishedClosure_le_commutatorKernel_of_centralizerClosure
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t) :
    (closure (Z ∩ (M : Set G))).subgroupOf M ≤ linearCommutatorKernel M z t := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let R := linearCentralizerClosure M z t
  let K := (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M
  let J := (centralizer (residualGenerated M z t : Set G)).subgroupOf M
  let V := pCore 2 M
  let : A.Normal := distinguishedClosure_normal h.disconnected
  let : R.Normal := normalClosure_normal
  have hRV : R ≤ V := linearCentralizerClosure_le_twoCore hR
  have hVp : IsPGroup 2 V := pCore_isPGroup
  have hRp : IsPGroup 2 R := hVp.to_le hRV
  obtain ⟨_, _, hAcard⟩ := linear_distinguishedClosure_internal_facts
    h.disconnected r hz hzM ht htM hL hn e hAL
  obtain ⟨hKcard, hfree⟩ := linear_distinguishedClosure_torus_geometry
    h r hz hzM ht htM hL hn e hAL
  have hq : 4 ≤ 2 ^ n := (show 4 = 2 ^ 2 by norm_num) ▸
    Nat.pow_le_pow_right (by decide) hn
  have hlocal := linear_involution_localization_of_centralizerClosure h.disconnected r
    hz hzM ht htM hL hn e hAL hJ hcollapse
  have hAR : A ≤ R := root_le_normal_of_localization V R A J K hRp hRV
    subset_normalClosure (linearCentralizer_subgroupOf_card h.disconnected hz hzM hJ)
    (by change 2 < Nat.card (linearCentralizerClosure M z t); rw [hR]; nlinarith)
    hlocal (by rw [hAcard, hKcard]; omega) hfree
  have hAp : IsPGroup 2 A := hVp.to_le (hAR.trans hRV)
  let : Group.IsNilpotent A := hAp.isNilpotent
  have hodd : Odd (Nat.card K) := by
    rw [show Nat.card K = Nat.card
      (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) from
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).toEquiv]
    exact pair_inf_proper_residualGenerated_odd h.disconnected r hz hzM ht htM hL
  have hcop : Nat.Coprime (Nat.card K) (Nat.card A) := by
    obtain ⟨m, hm⟩ := hAp.exists_card_eq
    rw [hm]
    exact hodd.coprime_two_right.pow_right m
  have hKnon : Nontrivial K := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    change 1 < Nat.card ((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M)
    rw [hKcard]
    omega
  let : Nontrivial K := hKnon
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  have hfix : A ⊓ centralizer (K : Set M) = ⊥ := by
    apply le_bot_iff.mp
    rw [← hfree k k.property (fun he => hk (Subtype.ext he))]
    apply inf_le_inf_left
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp ha k k.property).symm
  have hsplit := eq_commutator_sup_centralizer_of_solvable_coprime A K
    (le_trans le_top le_normalizer_of_normal) inferInstance hcop
  rw [hfix, sup_bot_eq] at hsplit
  exact hsplit.le.trans (commutator_mono hAR le_rfl)

end BenderSuzuki.ZD
