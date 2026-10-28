module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCountGrowth.Base
public import Theory.GroupAction.CoprimeQuotientOrbitBound

/-!
# Coprime quotient actions on the source normalizers

The torus normalizes AU and its normalizer inside V. On any invariant section
P/N inside V with U≤N, the fixed-subgroup calculation C_V(k)=U and coprime
fixed-point lifting make the torus free away from the identity. Consequently
a proper such section has order at least q. These are the two quotient-action
steps of GLS IV, Chapter 2, Lemma 15.6 (R₁/AU and N_V(R₁)/R₁).
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.SourceCount
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "D" => residualPairStabilizer M t
local notation "K" => residualCommutator M t
local notation "V" => pointCore M
local notation "U" => twoCore M z t
local notation "A" => closure (Z ∩ (M : Set G))
local notation "R" => sourceNormalizer Z M z t

public theorem pair_normalizes_sup (hs : CentralizerLocalTwoData d) :
    D ≤ normalizer ((A ⊔ U : Subgroup G) : Set G) := by
  apply le_trans (le_inf ?_ ?_) (normalizer_inf_normalizer_le_normalizer_sup A U)
  · rw [distinguishedClosure_normalizer d.minimal.disconnected]
    exact inf_le_left
  · change D ≤ normalizer (((pCore 2 (centralizer (residualGenerated M z t : Set G))).map
      (centralizer (residualGenerated M z t : Set G)).subtype : Subgroup G) : Set G)
    rw [d.centralizer_twoCore_normalizer_eq hs.twoCore_ne_bot]
    exact d.pair_normalizes

public theorem pair_normalizes_sourceNormalizer (hs : CentralizerLocalTwoData d) :
    D ≤ normalizer (R : Set G) :=
  (le_inf (inf_le_left.trans point_normalizes_pointCore)
    ((pair_normalizes_sup d hs).trans le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

public theorem torus_normalizes_sup (hs : CentralizerLocalTwoData d) :
    K ≤ normalizer ((A ⊔ U : Subgroup G) : Set G) := by
  rw [d.torus_structure.1]
  exact inf_le_left.trans (pair_normalizes_sup d hs)

public theorem torus_normalizes_sourceNormalizer (hs : CentralizerLocalTwoData d) :
    K ≤ normalizer (R : Set G) := by
  rw [d.torus_structure.1]
  exact inf_le_left.trans (pair_normalizes_sourceNormalizer d hs)

/-- Literal ambient-element freeness on every suitable section of V. -/
public theorem torus_free_section (hs : CentralizerLocalTwoData d)
    (P N : Subgroup G) (hPV : P ≤ V) (_hNP : N ≤ P)
    (hPN : P ≤ normalizer (N : Set G)) (hUN : U ≤ N)
    (hKP : K ≤ normalizer (P : Set G)) (hKN : K ≤ normalizer (N : Set G)) :
    ∀ k ∈ K, k ≠ 1 → ∀ x ∈ P, x ∉ N → MulAut.conj k x * x⁻¹ ∉ N := by
  let rho : K →* MulAut P := (P).normalizerMonoidHom.comp (inclusion hKP)
  let : MulDistribMulAction K P := MulDistribMulAction.compHom P rho
  let Q := N.subgroupOf P
  let : Q.Normal := normal_subgroupOf_of_le_normalizer hPN
  have hQI : IsInvariant K P Q := ⟨fun k x => by
    change (x : G) ∈ N ↔ (k : G) * (x : G) * (k : G)⁻¹ ∈ N
    exact mem_normalizer_iff.mp (hKN k.property) x⟩
  have hP : IsPGroup 2 P := ((pCore_isPGroup (p := 2) (G := M)).map M.subtype).to_le hPV
  let : Group.IsNilpotent P := hP.isNilpotent
  have hcop : Nat.Coprime (Nat.card K) (Nat.card P) :=
    by
    obtain ⟨e, he⟩ := hP.exists_card_eq
    rw [he]
    exact d.torus_odd.coprime_two_right.pow_right e
  have hfix (k : K) (hk : k ≠ 1) (x : P) (hx : k • x = x) : x ∈ Q := by
    have he := congrArg Subtype.val hx
    change (k : G) * (x : G) * (k : G)⁻¹ = (x : G) at he
    apply hUN
    rw [← torus_centralizer_pointCore d hs k.property (fun he => hk (Subtype.ext he))]
    exact ⟨hPV x.property, mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp he).symm⟩
  let : MulDistribMulAction K (P ⧸ Q) := quotientMulDistribMulAction Q hQI
  intro k hk hkne x hx hxN hcomm
  let k' : K := ⟨k, hk⟩
  let x' : P := ⟨x, hx⟩
  let q := QuotientGroup.mk' Q
  have he : k' • q x' = q x' := by
    have hc : q (k' • x' * x'⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm
    rw [map_mul, map_inv] at hc
    exact mul_inv_eq_one.mp hc
  have ho := Theory.GroupAction.fixed_quotient_eq_one_of_fixed_le Q hQI
    (inferInstance : Group.IsSolvable P) hcop hfix k'
    (fun he => hkne (congrArg Subtype.val he)) (q x') he
  exact hxN ((QuotientGroup.eq_one_iff x').mp ho)

/-- The original relative index is at least q whenever this section is nontrivial. -/
public theorem torus_section_index_lower (hs : CentralizerLocalTwoData d)
    (P N : Subgroup G) (hPV : P ≤ V) (hNP : N < P)
    (hPN : P ≤ normalizer (N : Set G)) (hUN : U ≤ N)
    (hKP : K ≤ normalizer (P : Set G)) (hKN : K ≤ normalizer (N : Set G)) :
    2 ^ n ≤ N.relIndex P := by
  let rho : K →* MulAut P := (P).normalizerMonoidHom.comp (inclusion hKP)
  let : MulDistribMulAction K P := MulDistribMulAction.compHom P rho
  let Q := N.subgroupOf P
  let : Q.Normal := normal_subgroupOf_of_le_normalizer hPN
  have hQI : IsInvariant K P Q := ⟨fun k x => by
    change (x : G) ∈ N ↔ (k : G) * (x : G) * (k : G)⁻¹ ∈ N
    exact mem_normalizer_iff.mp (hKN k.property) x⟩
  have hP : IsPGroup 2 P := ((pCore_isPGroup (p := 2) (G := M)).map M.subtype).to_le hPV
  let : Group.IsNilpotent P := hP.isNilpotent
  have hcop : Nat.Coprime (Nat.card K) (Nat.card P) :=
    by
    obtain ⟨e, he⟩ := hP.exists_card_eq
    rw [he]
    exact d.torus_odd.coprime_two_right.pow_right e
  have hfix (k : K) (hk : k ≠ 1) (x : P) (hx : k • x = x) : x ∈ Q := by
    have he := congrArg Subtype.val hx
    change (k : G) * (x : G) * (k : G)⁻¹ = (x : G) at he
    apply hUN
    rw [← torus_centralizer_pointCore d hs k.property (fun he => hk (Subtype.ext he))]
    exact ⟨hPV x.property, mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp he).symm⟩
  have hproper : Q ≠ ⊤ := fun he => hNP.ne (le_antisymm hNP.le (subgroupOf_eq_top.mp he))
  have hb := Theory.GroupAction.card_actor_lt_card_quotient_of_fixed_le Q hQI
    (inferInstance : Group.IsSolvable P) hcop hproper hfix
  change Nat.card K < N.relIndex P at hb
  rw [d.torus_structure.2.2.1] at hb
  have hp := Nat.one_le_two_pow (n := n)
  omega

end BenderSuzuki.ZD.LinearExclusion.SourceCount
