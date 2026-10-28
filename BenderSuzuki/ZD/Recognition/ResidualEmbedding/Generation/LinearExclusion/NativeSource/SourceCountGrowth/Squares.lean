module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCountGrowth.Normality

/-!
# Squares in the original distinguished root

The free torus action on the q−1 nonidentity elements of R₁/AU is transitive.
Cauchy's theorem supplies an involution in this two-group, so every quotient
element has square one. For x outside AU, the published centralizer calculation
C_U(x)=1 and centrality of A give C_AU(x)=A. Since x² lies in AU and commutes
with x, it belongs to A. Elements already in AU have square one.

Source: GLS IV, Chapter 2, Lemma 15.6, third paragraph. This explicitly fills
the elementary-quotient step before using the source involution census.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.SourceCount
open Subgroup Theory.GroupTheory
open scoped Pointwise
universe u

private theorem square_one_of_free_action_card
    {Q B : Type*} [Group Q] [Finite Q] [Group B] [Finite B]
    [MulDistribMulAction B Q] (heven : 2 ∣ Nat.card Q)
    (hcard : Nat.card B = Nat.card Q - 1)
    (hfree : ∀ b : B, b ≠ 1 → ∀ x : Q, b • x = x → x = 1) :
    ∀ x : Q, x ^ 2 = 1 := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 heven
  have hu1 : u ≠ 1 := by intro he; rw [he, orderOf_one] at hu; omega
  have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  let f : B → {x : Q // x ≠ 1} := fun b => ⟨b • u, by
    intro he
    exact hu1 ((MulDistribMulAction.toMulEquiv Q b).injective
      (he.trans (smul_one b).symm))⟩
  have hi : Function.Injective f := by
    intro b c he
    have hv : b • u = c • u := congrArg Subtype.val he
    have hc : (c⁻¹ * b) • u = u := by rw [mul_smul, hv, inv_smul_smul]
    have heq : c⁻¹ * b = 1 := by
      by_contra hne
      exact hu1 (hfree _ hne _ hc)
    exact (inv_mul_eq_one.mp heq).symm
  have hs : Function.Surjective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hi, (hcard.trans (Census.card_nonidentity Q).symm)⟩ |>.2
  intro x
  by_cases hx : x = 1
  · simp only [hx, one_pow]
  obtain ⟨b, hb⟩ := hs ⟨x, hx⟩
  have he : b • u = x := congrArg Subtype.val hb
  rw [← he, ← smul_pow', hu2, smul_one]

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "K" => residualCommutator M t
local notation "V" => pointCore M
local notation "U" => twoCore M z t
local notation "A" => closure (Z ∩ (M : Set G))
local notation "R" => sourceNormalizer Z M z t

public theorem sourceNormalizer_square_mem_sup (hs : CentralizerLocalTwoData d)
    {x : G} (hx : x ∈ R) : x ^ 2 ∈ A ⊔ U := by
  let N := (A ⊔ U).subgroupOf R
  let : N.Normal := normal_subgroupOf_of_le_normalizer (show R ≤ normalizer
    ((A ⊔ U : Subgroup G) : Set G) from inf_le_right)
  let rho : K →* MulAut R := (R).normalizerMonoidHom.comp
    (inclusion (torus_normalizes_sourceNormalizer d hs))
  let : MulDistribMulAction K R := MulDistribMulAction.compHom R rho
  have hNI : IsInvariant K R N := ⟨fun k x => by
    change (x : G) ∈ A ⊔ U ↔ (k : G) * (x : G) * (k : G)⁻¹ ∈ A ⊔ U
    exact mem_normalizer_iff.mp (torus_normalizes_sup d hs k.property) x⟩
  let : MulDistribMulAction K (R ⧸ N) := quotientMulDistribMulAction N hNI
  have hR : IsPGroup 2 R := ((pCore_isPGroup (p := 2) (G := M)).map M.subtype).to_le inf_le_left
  let : Group.IsNilpotent R := hR.isNilpotent
  have hcop : Nat.Coprime (Nat.card K) (Nat.card R) := by
    obtain ⟨e, he⟩ := hR.exists_card_eq
    rw [he]
    exact d.torus_odd.coprime_two_right.pow_right e
  have hfix (k : K) (hk : k ≠ 1) (y : R) (hy : k • y = y) : y ∈ N := by
    have he := congrArg Subtype.val hy
    change (k : G) * (y : G) * (k : G)⁻¹ = (y : G) at he
    apply (show U ≤ A ⊔ U from le_sup_right)
    rw [← torus_centralizer_pointCore d hs k.property (fun he => hk (Subtype.ext he))]
    exact ⟨y.property.1, mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp he).symm⟩
  have hfree := Theory.GroupAction.fixed_quotient_eq_one_of_fixed_le N hNI
    (inferInstance : Group.IsSolvable R) hcop hfix
  have hcardQ : Nat.card (R ⧸ N) = 2 ^ n := sourceNormalizer_sup_index d hs
  have hsq := square_one_of_free_action_card
    (B := K) (Q := R ⧸ N)
    (hcardQ.symm ▸ dvd_pow_self 2 (by have := d.parameter; omega))
    (by rw [hcardQ]; exact d.torus_structure.2.2.1) hfree
  have he := hsq (QuotientGroup.mk' N ⟨x, hx⟩)
  rw [← map_pow] at he
  have hmem : (⟨x, hx⟩ : R) ^ 2 ∈ N := (QuotientGroup.eq_one_iff _).mp he
  change ((⟨x, hx⟩ : R) ^ 2 : G) ∈ A ⊔ U at hmem
  simpa only [Subgroup.coe_pow] using hmem

public theorem sourceNormalizer_square_mem_distinguished (hs : CentralizerLocalTwoData d)
    {x : G} (hx : x ∈ R) : x ^ 2 ∈ A := by
  by_cases hxAU : x ∈ A ⊔ U
  · rw [Census.sup_square d hs hxAU]
    exact (A).one_mem
  have hsx := sourceNormalizer_square_mem_sup d hs hx
  have hp : x ^ 2 ∈ ((A : Set G) * (U : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left A U
      ((twoCore_centralizes_distinguished d).trans (Subgroup.centralizer_le_normalizer _))]
    exact hsx
  obtain ⟨a, ha, v, hv, he⟩ := hp
  change a * v = x ^ 2 at he
  have hax : Commute a x := mem_centralizer_iff.mp
    (sourceNormalizer_centralizes_distinguished d hx) a ha
  have hvx : Commute v x := by
    have hh : a * v * x = x * (a * v) := by
      rw [he]
      simp only [pow_two, mul_assoc]
    rw [mul_assoc, ← mul_assoc x a v, ← hax.eq, mul_assoc] at hh
    exact mul_left_cancel hh
  have hvbot : v ∈ (⊥ : Subgroup G) := (eq_bot_iff.mp
    (twoCore_centralizer_outside_sup d hs hx hxAU))
      ⟨hv, mem_centralizer_singleton_iff.mpr hvx.eq⟩
  have hv1 : v = 1 := hvbot
  rw [← he, hv1, mul_one]
  exact ha

end BenderSuzuki.ZD.LinearExclusion.SourceCount
