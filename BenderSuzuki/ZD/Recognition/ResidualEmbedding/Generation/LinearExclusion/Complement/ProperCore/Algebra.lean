module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Definitions
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupAction.Quotient

/-!
# The algebraic complement construction in the proper-core branch

GLS, Volume 4, Chapter 2, Lemma 15.7 constructs a normal homocyclic
subgroup `R₀` and proves `V/R₀` elementary abelian, where `V = O₂(M)`.
The final complement argument needs only an abelian quotient with normal
kernel disjoint from the fixed subgroup `C_V(K) = D ∩ V`.

Coprime action gives `V = C_V(K)[K,V]`. In the abelian quotient its fixed
and moving subgroups intersect trivially, so `[K,V] ∩ C_V(K)` lies in the
kernel and is therefore trivial. Finally, `D` normalizes `[K,V]` because
it normalizes `K` and `V`, while `V` always normalizes `[K,V]`. Thus
`M = DV` makes the constructed complement normal in `M`.

This is a conditional construction, not a proof of the local hypotheses
or of the source Lemma 15.7. In particular it does not assume a complement
or replace the distinguished closure `M°` by a different subgroup.
-/

noncomputable section

namespace BenderSuzuki.ZD

open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped IsMulCommutative

/-- Normalization of `L` by `D` gives normalization of `K = D ∩ L`,
including after both subgroups are viewed inside `M`. The premise is the
source orbit-control conclusion, not ambient normality of `K`. -/
public theorem linear_pair_le_normalizer_inter_of_normalizes
    {G : Type*} [Group G] {M : Subgroup G} {z t : G}
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G)) :
    (residualPairStabilizer M t).subgroupOf M ≤
      normalizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) := by
  have hDK : residualPairStabilizer M t ≤
      normalizer ((residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) : Set G) :=
    (le_inf (residualPairStabilizer M t).le_normalizer hDN).trans
      inf_normalizer_le_normalizer_inf
  exact (Subgroup.comap_mono hDK).trans (Subgroup.le_normalizer_comap M.subtype)

private theorem disjoint_fixed_moving {P B : Type*} [Group P] [Group B] [Finite P] [Finite B]
    [MulDistribMulAction B P] (A : Subgroup P) [A.Normal]
    (hA : IsInvariant B P A)
    (hcop : Nat.Coprime (Nat.card B) (Nat.card P))
    [IsMulCommutative (P ⧸ A)]
    (hdis : Disjoint A (fixedPointSubgroup B P)) :
    Disjoint (fixedPointSubgroup B P) (commutatorAction B P) := by
  let : MulDistribMulAction B (P ⧸ A) := quotientMulDistribMulAction A hA
  let : MulAction.QuotientAction B A := quotientAction_of_isInvariant A hA
  let q := QuotientGroup.mk' A
  have hcopQ : Nat.Coprime (Nat.card B) (Nat.card (P ⧸ A)) :=
    hcop.of_dvd_right A.index_dvd_card
  have hsplit :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := P ⧸ A) (A := B)
      (Group.isSolvable_of_comm (fun x y => mul_comm x y)) hcopQ inferInstance
  have hmap : commutatorAction B P ≤ (commutatorAction B (P ⧸ A)).comap q := by
    rw [commutatorAction_eq_closure]
    rw [Subgroup.closure_le]
    rintro x ⟨b, p, rfl⟩
    change q (p⁻¹ * b • p) ∈ commutatorAction B (P ⧸ A)
    have hq : q (b • p) = b • q p := (MulAction.Quotient.smul_coe A b p).symm
    rw [map_mul, map_inv, hq, commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨b, q p, rfl⟩
  apply Subgroup.disjoint_def.mpr
  intro x hxF hxC
  have hqF : q x ∈ fixedPointSubgroup B (P ⧸ A) := by
    intro b
    change b • q x = q x
    exact (MulAction.Quotient.smul_coe A b x).trans (congrArg q (hxF b))
  have hq1 : q x = 1 := Subgroup.disjoint_def.mp hsplit.disjoint hqF (hmap hxC)
  have hxA : x ∈ A := (QuotientGroup.eq_one_iff x).mp hq1
  exact Subgroup.disjoint_def.mp hdis hxA hxF

private theorem normal_moving {H : Type*} [Group H] (D V K : Subgroup H) [V.Normal]
    (hDV : D ⊔ V = ⊤) (hDK : D ≤ normalizer (K : Set H)) :
    (⁅K,V⁆).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hDV]
  refine sup_le ?_ (normalizer_commutator_ge_right K V)
  intro d hd
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hDK hd),
    mem_normalizer_iff_map_conj_eq.mp
      (show d ∈ normalizer (V : Set H) from le_normalizer_of_normal (mem_top d))]

/-- A normal candidate containing the centralizer is its actual normal closure
once the two orders agree. This identifies the source normalizer `R₁` with
`linearCentralizerClosure`; normality here is relative to `M`. -/
public theorem linearCentralizerClosure_eq_of_normal_of_card
    {G : Type*} [Group G] [Finite G] {M : Subgroup G} {z t : G}
    (R₁ : Subgroup M) [R₁.Normal]
    (hJ : (Subgroup.centralizer (residualGenerated M z t : Set G)).subgroupOf M ≤ R₁)
    (hcard : Nat.card R₁ = Nat.card (linearCentralizerClosure M z t)) :
    R₁ = linearCentralizerClosure M z t := by
  symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.normalClosure_le_normal hJ)
  exact hcard.le

private theorem complement_from_abelian_quotient
    {H : Type*} [Group H] [Finite H]
    (D V K A : Subgroup H) [V.Normal] [A.Normal]
    (hDV : D ⊔ V = ⊤) (hDK : D ≤ normalizer (K : Set H))
    (hsolv : Group.IsSolvable V)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card V))
    (hfixed : V ⊓ centralizer (K : Set H) = D ⊓ V)
    [IsMulCommutative (V ⧸ A.subgroupOf V)]
    (hdis : Disjoint A (D ⊓ V)) :
    (⁅K,V⁆).Normal ∧ (⁅K,V⁆ ≤ V) ∧
      (D.subgroupOf V).IsComplement' ((⁅K,V⁆).subgroupOf V) := by
  have hN : (⁅K,V⁆).Normal := normal_moving D V K hDV hDK
  let : (⁅K,V⁆).Normal := hN
  have hNV : ⁅K,V⁆ ≤ V := commutator_le_right K V
  have hfix : fixedPointSubgroup K V = D.subgroupOf V := by
    ext x
    constructor
    · intro hx
      have hc : (x : H) ∈ V ⊓ centralizer (K : Set H) := by
        refine ⟨x.property, ?_⟩
        change (x : H) ∈ centralizer (K : Set H)
        rw [mem_centralizer_iff]
        intro k hk
        have hh := congrArg Subtype.val (hx ⟨k, hk⟩)
        change k * (x : H) * k⁻¹ = x at hh
        exact mul_inv_eq_iff_eq_mul.mp hh
      rw [hfixed] at hc
      exact hc.1
    · intro hx k
      apply Subtype.ext
      change (k : H) * (x : H) * (k : H)⁻¹ = x
      have hc : (x : H) ∈ V ⊓ centralizer (K : Set H) := by
        rw [hfixed]
        exact ⟨hx, x.property⟩
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hc.2 k k.property)
  have hcomm : commutatorAction K V = (⁅K,V⁆).subgroupOf V := by
    apply Subgroup.map_injective V.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hNV,
      commutatorAction_subgroup_conj_map_eq_commutator V K le_normalizer_of_normal,
      commutator_comm]
  have hInv : IsInvariant K V (A.subgroupOf V) := by
    constructor
    intro k v
    change (v : H) ∈ A ↔ (k : H) * (v : H) * (k : H)⁻¹ ∈ A
    exact mem_normalizer_iff.mp
      (show (k : H) ∈ normalizer (A : Set H) from
        le_normalizer_of_normal (mem_top (k : H))) v
  have hd : Disjoint (A.subgroupOf V) (fixedPointSubgroup K V) := by
    rw [hfix]
    apply Subgroup.disjoint_def.mpr
    intro x hxA hxD
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdis hxA ⟨hxD, x.property⟩
  have hd' := disjoint_fixed_moving (A.subgroupOf V) hInv hcop hd
  rw [hfix, hcomm] at hd'
  have hs := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime hsolv hcop
  rw [hfix, hcomm] at hs
  refine ⟨hN, hNV, Subgroup.mul_injective_of_disjoint hd', ?_⟩
  intro x
  have hx : x ∈ D.subgroupOf V ⊔ (⁅K,V⁆).subgroupOf V := by
    rw [hs]
    exact mem_top x
  obtain ⟨d, hd, v, hv, heq⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  exact ⟨(⟨d, hd⟩, ⟨v, hv⟩), heq⟩

/-- Conditional algebraic step of GLS 15.7: construct the normal subgroup
`[K,V]`, where `K = D ∩ L` and `V = O₂(M)`, using an abelian quotient
whose kernel misses `D ∩ V`. The supplement, normalizer, centralizer and
quotient premises still have to be established by the source local analysis. -/
public theorem linear_twoCore_complement_of_abelian_quotient
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (A : Subgroup M) [A.Normal]
    [IsMulCommutative (pCore 2 M ⧸ A.subgroupOf (pCore 2 M))]
    (hDV : (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤)
    (hDK : (residualPairStabilizer M t).subgroupOf M ≤
      normalizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M))
    (hfixed : pCore 2 M ⊓
      centralizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (residualPairStabilizer M t).subgroupOf M ⊓ pCore 2 M)
    (hdis : Disjoint A ((residualPairStabilizer M t).subgroupOf M ⊓ pCore 2 M)) :
    ∃ N : Subgroup M, N.Normal ∧ N ≤ pCore 2 M ∧
      (((residualPairStabilizer M t).subgroupOf M).subgroupOf (pCore 2 M)).IsComplement'
        (N.subgroupOf (pCore 2 M)) := by
  let D := (residualPairStabilizer M t).subgroupOf M
  let V := pCore 2 M
  let K := (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M
  have hK : Odd (Nat.card K) := by
    have heq : Nat.card K = Nat.card
        (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).toEquiv
    rw [heq]
    exact pair_inf_proper_residualGenerated_odd h r hz hzM ht htM hL
  have hp : IsPGroup 2 V := pCore_isPGroup
  let : Group.IsNilpotent V := hp.isNilpotent
  have hcop : Nat.Coprime (Nat.card K) (Nat.card V) := by
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    rw [hm]
    exact hK.coprime_two_right.pow_right m
  exact ⟨⁅K,V⁆, complement_from_abelian_quotient D V K A hDV hDK inferInstance hcop hfixed hdis⟩

/-- The local centralizer equality also identifies the pair stabilizer's
intersection with the two-core. Since `K` is odd and normalized by `D`,
`[D ∩ V,K]` lies in both coprime subgroups `K` and `V` and is trivial.
This proves the intersection clause rather than assuming it separately. -/
public theorem linear_pair_inf_twoCore_eq_of_fixed_centralizer
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hDK : (residualPairStabilizer M t).subgroupOf M ≤
      normalizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M))
    (hfixed : pCore 2 M ⊓
      centralizer (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M) :
    (residualPairStabilizer M t).subgroupOf M ⊓ pCore 2 M =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M := by
  let D := (residualPairStabilizer M t).subgroupOf M
  let V := pCore 2 M
  let K := (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M
  have hK : Odd (Nat.card K) := by
    have heq : Nat.card K = Nat.card
        (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).toEquiv
    rw [heq]
    exact pair_inf_proper_residualGenerated_odd h r hz hzM ht htM hL
  have hp : IsPGroup 2 V := pCore_isPGroup
  have hcop : Nat.Coprime (Nat.card K) (Nat.card V) := by
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    rw [hm]
    exact hK.coprime_two_right.pow_right m
  have hKV : Disjoint K V := Subgroup.disjoint_of_coprime_natCard hcop
  have hcomm : ⁅D ⊓ V, K⁆ = ⊥ := by
    apply le_bot_iff.mp
    apply le_trans _ hKV.le_bot
    apply le_inf
    · exact le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hDK)
    · exact (commutator_mono inf_le_right le_rfl).trans (commutator_le_left V K)
  have hcent : D ⊓ V ≤ centralizer (K : Set M) :=
    commutator_eq_bot_iff_le_centralizer.mp hcomm
  apply le_antisymm
  · exact (le_inf inf_le_right hcent).trans hfixed.le
  · apply le_inf
    · intro x hx
      exact centralizer_residualGenerated_le_pair h hz hzM hx
    · exact hfixed.symm.le.trans inf_le_left


end BenderSuzuki.ZD
