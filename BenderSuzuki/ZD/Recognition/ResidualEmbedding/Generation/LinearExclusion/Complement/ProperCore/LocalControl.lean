module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Algebra
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.Foundations
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupAction.CoprimeQuotientOrbitBound

/-!
# Local control from centralizer localization and linear torus geometry

Write `A = M°`, `J = C_G(L)`, `K = D ∩ L`, `V = O₂(M)`, and
`R = ⟨Jᴹ⟩`, with all calculations performed inside `M`.
Suppose `C_V(J) ≤ AJ` and every nonidentity element of `K` has trivial
centralizer in `A`. Then `C_V(k)` has a self-centralizing subgroup `J`
of order two. The normalizer condition gives `C_V(k) = J`.

Because `J ≤ R`, coprime fixed-point lifting makes `K` act freely on
`V/R` away from its identity. Thus `R < V` and `|K| = q-1` imply
`|V/R| ≥ q`. Together with `|R| = 2q²`, `D ∩ V = J`, and
`|M| = q³|D|`, this proves `M = DV` by the subgroup product formula.
This route uses the given normal closure directly; it requires no
identification with the source's intermediate normalizer `R₁`.

The centralizer localization, distinguished-closure torus action, and
order formulas remain explicit earlier-source premises. These conditional
results do not yet establish the source branch under the original model
hypotheses. The source assembly must discharge those premises.
Source: GLS, Volume 4, Chapter 2, Lemmas 15.2, 15.6 and the proper-core
paragraph of 15.7 (`refs/KGroup/GLS4/Chapter2.tex`).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory

/-- Each nonidentity torus element fixes precisely `J` in the two-core,
provided its action on the distinguished closure is free and the
involution centralizer localizes into `M°J`. -/
public theorem linear_twoCore_element_centralizer_of_localization
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) {n : ℕ}
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hlocal : pCore 2 M ⊓
      centralizer ((centralizer (residualGenerated M z t : Set G)).subgroupOf M : Set M) ≤
      (closure (Z ∩ (M : Set G))).subgroupOf M ⊔
        (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (hAfixed : ∀ k ∈ (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M,
      k ≠ 1 → (closure (Z ∩ (M : Set G))).subgroupOf M ⊓
        centralizer ({k} : Set M) = ⊥) :
    ∀ k ∈ (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M,
      k ≠ 1 → pCore 2 M ⊓ centralizer ({k} : Set M) =
        (centralizer (residualGenerated M z t : Set G)).subgroupOf M := by
  let : ((closure (Z ∩ (M : Set G))).subgroupOf M).Normal :=
    distinguishedClosure_normal h
  intro k hk hkn
  apply inf_centralizer_eq_of_card_two_of_localization
    (pCore 2 M) ((closure (Z ∩ (M : Set G))).subgroupOf M)
    ((centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    pCore_isPGroup (linearCentralizer_subgroupOf_le_twoCore hR)
    (linearCentralizer_subgroupOf_card h hz hzM hJ) hlocal k _ (hAfixed k hk hkn)
  intro j hj
  apply mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  exact (mem_centralizer_iff.mp hj k hk.2).symm

/-- The actual quotient `V/⟨Jᴹ⟩` supplies the proper-core supplement and
fixed-point equality from the earlier local geometry and order formulas.
All additional source premises are displayed explicitly. -/
public theorem linear_localControl_of_localization_and_orders
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hproper : linearCentralizerClosure M z t < pCore 2 M)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hlocal : pCore 2 M ⊓
      centralizer ((centralizer (residualGenerated M z t : Set G)).subgroupOf M : Set M) ≤
      (closure (Z ∩ (M : Set G))).subgroupOf M ⊔
        (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (hAfixed : ∀ k ∈ (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M,
      k ≠ 1 → (closure (Z ∩ (M : Set G))).subgroupOf M ⊓
        centralizer ({k} : Set M) = ⊥)
    (hKcard : Nat.card ((residualPairStabilizer M t ⊓
      residualGenerated M z t).subgroupOf M) = 2 ^ n - 1)
    (hMcard : Nat.card M = (2 ^ n) ^ 3 * Nat.card (residualPairStabilizer M t)) :
    (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤ ∧
      pCore 2 M ⊓ centralizer
        (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
        (centralizer (residualGenerated M z t : Set G)).subgroupOf M := by
  let V := pCore 2 M
  let R := linearCentralizerClosure M z t
  let D := (residualPairStabilizer M t).subgroupOf M
  let K := (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M
  let J := (centralizer (residualGenerated M z t : Set G)).subgroupOf M
  have hJc : Nat.card J = 2 := linearCentralizer_subgroupOf_card h hz hzM hJ
  have hJV : J ≤ V := linearCentralizer_subgroupOf_le_twoCore hR
  have hJC : J ≤ centralizer (K : Set M) := by
    intro j hj k hk
    apply Subtype.ext
    exact mem_centralizer_iff.mp hj k hk.2
  have helement : ∀ k ∈ K, k ≠ 1 → V ⊓ centralizer ({k} : Set M) = J :=
    linear_twoCore_element_centralizer_of_localization h hz hzM hJ hR hlocal hAfixed
  have hq : 4 ≤ 2 ^ n := (show 4 = 2 ^ 2 by norm_num) ▸
    Nat.pow_le_pow_right (by decide) hn
  have hKnon : Nontrivial K := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hKcard]
    omega
  let : Nontrivial K := hKnon
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  have hkM : (k : M) ≠ 1 := fun hh => hk (Subtype.ext hh)
  have hfixed : V ⊓ centralizer (K : Set M) = J := by
    apply le_antisymm _ (le_inf hJV hJC)
    intro v hv
    have hvc : v ∈ centralizer ({(k : M)} : Set M) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hv.2 k k.property).symm
    rw [← helement k k.property hkM]
    exact ⟨hv.1, hvc⟩
  have hDV : D ⊓ V = J := linear_pair_inf_twoCore_eq_of_fixed_centralizer
    h r hz hzM ht htM hL (linear_pair_le_normalizer_inter_of_normalizes hDN) hfixed
  let : R.Normal := by unfold R linearCentralizerClosure; infer_instance
  have hRV : R ≤ V := hproper.le
  have hInv : IsInvariant K V (R.subgroupOf V) := by
    constructor
    intro k v
    change (v : M) ∈ R ↔ (k : M) * (v : M) * (k : M)⁻¹ ∈ R
    exact mem_normalizer_iff.mp
      (show (k : M) ∈ normalizer (R : Set M) from le_normalizer_of_normal (mem_top _)) v
  have hVp : IsPGroup 2 V := pCore_isPGroup
  let : Group.IsNilpotent V := hVp.isNilpotent
  have hodd : Odd (Nat.card K) := by
    have hc : Nat.card K = Nat.card
        (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) :=
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).toEquiv
    rw [hc]
    exact pair_inf_proper_residualGenerated_odd h r hz hzM ht htM hL
  have hcop : Nat.Coprime (Nat.card K) (Nat.card V) := by
    obtain ⟨m, hm⟩ := hVp.exists_card_eq
    rw [hm]
    exact hodd.coprime_two_right.pow_right m
  have hRne : R.subgroupOf V ≠ ⊤ := fun hh =>
    hproper.not_ge (subgroupOf_eq_top.mp hh)
  have hQcard := Theory.GroupAction.card_actor_lt_card_quotient_of_fixed_le
    (B := K) (R.subgroupOf V) hInv inferInstance hcop hRne (by
      intro k hkn v hv
      have hknM : (k : M) ≠ 1 := fun hh => hkn (Subtype.ext hh)
      have hvC : (v : M) ∈ centralizer ({(k : M)} : Set M) := by
        apply mem_centralizer_singleton_iff.mpr
        have hh := congrArg Subtype.val hv
        change (k : M) * (v : M) * (k : M)⁻¹ = v at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
      have hvJ : (v : M) ∈ J := by
        rw [← helement k k.property hknM]
        exact ⟨v.property, hvC⟩
      exact (show J ≤ R from subset_normalClosure) hvJ)
  have hqQ : 2 ^ n ≤ Nat.card (V ⧸ R.subgroupOf V) := by
    rw [hKcard] at hQcard
    omega
  have hRR : Nat.card (R.subgroupOf V) = Nat.card R :=
    Nat.card_congr (subgroupOfEquivOfLe hRV).toEquiv
  have hVcard : Nat.card V = Nat.card R * Nat.card (V ⧸ R.subgroupOf V) := by
    rw [← (R.subgroupOf V).card_mul_index, index_eq_card, hRR]
  have hVbound : 2 * (2 ^ n) ^ 3 ≤ Nat.card V := by
    calc
      2 * (2 ^ n) ^ 3 = (2 * (2 ^ n) ^ 2) * 2 ^ n := by ring
      _ ≤ (2 * (2 ^ n) ^ 2) * Nat.card (V ⧸ R.subgroupOf V) :=
        Nat.mul_le_mul_left _ hqQ
      _ = Nat.card V := by rw [← hR, ← hVcard]
  have hDcard : Nat.card D = Nat.card (residualPairStabilizer M t) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hprod : Nat.card V * Nat.card D = 2 * Nat.card (D ⊔ V : Subgroup M) := by
    rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes V D le_normalizer_of_normal,
      inf_comm V D, hDV, hJc, sup_comm V D]
  have hbound : 2 * Nat.card M ≤ 2 * Nat.card (D ⊔ V : Subgroup M) := by
    calc
      2 * Nat.card M = (2 * (2 ^ n) ^ 3) * Nat.card D := by rw [hMcard, hDcard]; ring
      _ ≤ Nat.card V * Nat.card D := Nat.mul_le_mul_right _ hVbound
      _ = 2 * Nat.card (D ⊔ V : Subgroup M) := hprod
  refine ⟨?_, hfixed⟩
  apply Subgroup.eq_of_le_of_card_ge le_top
  simpa using (show Nat.card M ≤ Nat.card (D ⊔ V : Subgroup M) by omega)

end BenderSuzuki.ZD
