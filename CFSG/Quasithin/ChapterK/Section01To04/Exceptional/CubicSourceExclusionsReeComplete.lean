module
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsReeShort
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order
public import Mathlib.GroupTheory.GroupAction.Quotient
/-!
# The Ree F₄ exclusion on the original cubic source domain

The saturated elementary actor has order q⁵, and the stronger short-root
involution estimate makes it long-root pure. Its equality with every
involution fixed kernel makes every conjugator between its nonidentity
elements normalize the actor. Long-root conjugacy therefore makes the
normalizer inside the original component transitive on the q⁵−1 nonidentity
elements. Orbit–stabilizer forces q⁵−1 to divide the genuine Ree order.
A prime divisor of q⁴+q³+q²+q+1 contradicts that divisibility when
q = 2^(2m+1). This replaces the centralizer-center step of GM04 Lemma 8.8
by an explicit order argument, while retaining the same source hypotheses.

The arbitrary central cover is identified through its literal quotient map,
and all original outer actors are retained until saturation puts the actor
inside the component. No FF hypothesis or model-geometry callback is used.
Source: Aschbacher–Smith K.3, printed p.457/PDF468; Guralnick–Malle II,
Lemma 8.8 and Theorem 8.1/Table 17. The order formula is GLS3 Table 2.2.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions
private theorem order_two_mod_five : orderOf (2 : ZMod 5) = 4 := by
  apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
  constructor
  · decide
  · intro k hk hk4
    interval_cases k <;> decide
private theorem ree_order_not_dvd (m : ℕ) :
    ¬ (2 ^ (2*m+1)) ^ 5 - 1 ∣
      (2 ^ (2*m+1)) ^ 12 * ((2 ^ (2*m+1)) ^ 6 + 1) *
      ((2 ^ (2*m+1)) ^ 4 - 1) * ((2 ^ (2*m+1)) ^ 3 + 1) * (2 ^ (2*m+1) - 1) := by
  let q := 2 ^ (2*m+1)
  change ¬ q^5-1 ∣ q^12*(q^6+1)*(q^4-1)*(q^3+1)*(q-1)
  have hq : 2 ≤ q := Nat.le_self_pow (by omega) 2
  let c := q^4+q^3+q^2+q+1
  have hc : c ≠ 1 := by dsimp [c]; omega
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd hc
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hq5 : 1 ≤ q^5 := one_le_pow₀ (by omega)
  have hq4 : 1 ≤ q^4 := one_le_pow₀ (by omega)
  have hfac : q^5-1 = (q-1)*c := by
    dsimp [c]
    zify [show 1 ≤ q by omega, hq5]
    ring
  have hp5 : p ∣ q^5-1 := hfac ▸ dvd_mul_of_dvd_right hpc (q-1)
  have hcz : (q : ZMod p)^4+(q : ZMod p)^3+(q : ZMod p)^2+(q : ZMod p)+1 = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff c p).mpr hpc
  have hz5 : (q : ZMod p)^5 = 1 := by
    have he := (ZMod.natCast_eq_zero_iff (q^5-1) p).mpr hp5
    rw [Nat.cast_sub hq5] at he
    simpa only [Nat.cast_pow, Nat.cast_one, sub_eq_zero] using he
  have hq1 : (q : ZMod p) ≠ 1 := by
    intro he
    rw [he] at hcz
    norm_num at hcz
    have hpD : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp hcz
    have heq : p = 5 := (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hpD |>.resolve_left hp.ne_one
    subst p
    have he : (2 : ZMod 5)^(2*m+1) = 1 := by simpa [q] using he
    have hord : orderOf (2 : ZMod 5) = 4 := order_two_mod_five
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [hord] at hd
    omega
  have ho : orderOf (q : ZMod p) = 5 := orderOf_eq_prime hz5 hq1
  have hn (k : ℕ) (hk : ¬ 5 ∣ k) : (q : ZMod p)^k ≠ 1 := by
    intro he
    exact hk (ho ▸ orderOf_dvd_of_pow_eq_one he)
  have hq0 : (q : ZMod p) ≠ 0 := by intro he; rw [he] at hz5; norm_num at hz5
  intro hd
  have he := (ZMod.natCast_eq_zero_iff _ p).mpr (hp5.trans hd)
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub hq4] at he
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, mul_eq_zero] at he
  rcases he with (((he | he) | he) | he) | he
  · exact (pow_ne_zero 12 hq0) he
  · exact hn 12 (by decide) (by calc
      (q : ZMod p)^12 = ((q : ZMod p)^6)^2 := by ring
      _ = 1 := by rw [eq_neg_of_add_eq_zero_left he]; ring)
  · exact hn 4 (by decide) (sub_eq_zero.mp he)
  · exact hn 6 (by decide) (by calc
      (q : ZMod p)^6 = ((q : ZMod p)^3)^2 := by ring
      _ = 1 := by rw [eq_neg_of_add_eq_zero_left he]; ring)
  · exact hq1 (sub_eq_zero.mp he)

private theorem normalizer_orbit_card {H : Type*} [Group H] [Finite H]
    (B : Subgroup H) (b : B) (hb : b ≠ 1)
    (ht : ∀ c : B, c ≠ 1 → ∃ g : (normalizer (B : Set H)), g • b = c) :
    Nat.card B - 1 ∣ Nat.card H := by
  classical
  have he : MulAction.orbit (normalizer (B : Set H)) b = {c : B | c ≠ 1} := by
    ext c
    constructor
    · rintro ⟨g, rfl⟩ hc
      apply hb
      exact (MulDistribMulAction.toMulAut (normalizer (B : Set H)) B g).injective
        (hc.trans (map_one _).symm)
    · exact ht c
  have hc : Nat.card (MulAction.orbit (normalizer (B : Set H)) b) = Nat.card B - 1 := by
    rw [he]
    let : Fintype B := Fintype.ofFinite B
    simp only [Nat.card_eq_fintype_card]
    change Fintype.card {c : B // ¬ c = 1} = Fintype.card B - 1
    rw [Fintype.card_subtype_compl]
    simp
  have hd : Nat.card (MulAction.orbit (normalizer (B : Set H)) b) ∣ Nat.card (normalizer (B : Set H)) := by
    refine ⟨Nat.card (MulAction.stabilizer (normalizer (B : Set H)) b), ?_⟩
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (normalizer (B : Set H)) b).symm
  rw [hc] at hd
  exact hd.trans (normalizer (B : Set H)).card_subgroup_dvd_card

universe u v
variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

private theorem ree_actor_conjugator_normalizes (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e : L ⧸ center L ≃* ReeF4.Model m)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A)
    (a g : G) (ha : a ∈ A) (ha1 : a ≠ 1) (hg : g*a*g⁻¹ ∈ A) :
    g ∈ normalizer (A : Set G) := by
  let B := A.map (MulAut.conj g).toMonoidHom
  have hB : IsElementaryTwo B := hA.map_conj g
  have hBs : fixedCodim ρ B ≤ 2 * rank B := by
    simpa only [B, fixedCodim_map_conj, rank_map_conj] using hsmall
  have hb : g*a*g⁻¹ ∈ B := mem_map.mpr ⟨a, ha, rfl⟩
  have hb1 : g*a*g⁻¹ ≠ 1 := by
    intro he
    exact ha1 ((MulAut.conj g).injective (he.trans (map_one _).symm))
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (ree_saturated_actor_eq_fixedKernel h hm e B hB hBs _ hb hb1).trans
    (ree_saturated_actor_eq_fixedKernel h hm e A hA hsmall _ hg hb1).symm

private theorem ree_long_root_conjugate {m : ℕ} (hm : 1 ≤ m)
    {x y : ReeF4.Model m}
    (hx : ReeF4.EvenInvolutionGeometry.IsLongRootInvolution x)
    (hy : ReeF4.EvenInvolutionGeometry.IsLongRootInvolution y) : IsConj x y := by
  obtain ⟨e⟩ := ReeF4.Subfield.nonempty_coefficientHom (k := 0) (m := m) (by simp)
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  have h₁ := ((ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.binaryRootNormalization
    m hm) e a ha).1.trans hax
  have h₂ := ((ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.binaryRootNormalization
    m hm) e b hb).1.trans hby
  exact h₁.symm.trans h₂

private theorem ree_actor_normalizer_transitive (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e₀ : L ⧸ center L ≃* ReeF4.Model m)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A)
    (a b : A.subgroupOf L) (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ g : normalizer (A.subgroupOf L : Set L), g • a = b := by
  obtain ⟨e, he⟩ := ree_source_model_equiv h hm e₀
  have haL : (a : L) ≠ 1 := fun hh => ha (Subtype.ext hh)
  have hbL : (b : L) ≠ 1 := fun hh => hb (Subtype.ext hh)
  have haR := ree_small_actor_long_root_pure h hm e₀ A hA hsmall a.val a.property haL
  have hbR := ree_small_actor_long_root_pure h hm e₀ A hA hsmall b.val b.property hbL
  have hea : e a.val = e₀ (QuotientGroup.mk' (center L) a.val) := DFunLike.congr_fun he a.val
  have heb : e b.val = e₀ (QuotientGroup.mk' (center L) b.val) := DFunLike.congr_fun he b.val
  have hc := ree_long_root_conjugate hm (hea.symm ▸ haR) (heb.symm ▸ hbR)
  have hab : IsConj a.val b.val := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      e.symm.toMonoidHom.map_isConj hc
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  have haG : ((a : L) : G) ≠ 1 := fun hh => haL (Subtype.ext hh)
  have hgg : (g : G) * ((a : L) : G) * (g : G)⁻¹ = ((b : L) : G) :=
    congrArg Subtype.val hg
  have hNA := ree_actor_conjugator_normalizes h hm e₀ A hA hsmall
    ((a : L) : G) (g : G) a.property haG (hgg ▸ b.property)
  have hNB : g ∈ normalizer (A.subgroupOf L : Set L) := by
    intro x
    exact hNA (x : G)
  refine ⟨⟨g, hNB⟩, ?_⟩
  exact Subtype.ext hg
/-- The positive Ree marking is impossible on Chapter K’s cubic source domain. -/
theorem ree_cubic_source_false (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m)
    (hq : Nonempty ((L ⧸ center L) ≃* ReeF4.Model m)) : False := by
  obtain ⟨e₀⟩ := hq
  obtain ⟨A, hA, _, hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.smallCubic
  have hsat := ree_small_actor_saturated h hm e₀ A hA hsmall
  let B := A.subgroupOf L
  obtain ⟨a, ha, ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  let b : B := ⟨⟨a, hsat.1 ha⟩, ha⟩
  have hb : b ≠ 1 := fun hh => ha1 (congrArg (fun z : B => (z.val : G)) hh)
  have hd := normalizer_orbit_card B b hb
    (fun c hc => ree_actor_normalizer_transitive h hm e₀ A hA hsmall b c hb hc)
  have hcard : Nat.card B = (2 ^ (2*m+1))^5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hsat.1).toEquiv,
      hA.card_eq_two_pow_rank, hsat.2.1, Nat.mul_comm 5 (2*m+1), pow_mul]
  obtain ⟨e, _⟩ := ree_source_model_equiv h hm e₀
  rw [hcard, Nat.card_congr e.toEquiv,
    ReeF4.CentralCovers.OddPrimary.Order.card_model] at hd
  exact ree_order_not_dvd m hd
end CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions
