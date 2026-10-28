module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Setup

/-!+# Fitting primes in overgroups of radical factors

If Ξ_q(L) ≤ K ≤ L, characteristic invariance in L makes Ξ_q(L) normal
in K. The map Ξ_q(L) → K/O₂(K) has kernel O₂(Ξ_q(L)): restriction of
O₂(K) gives one inclusion, and relative normality gives the other. Its
image is therefore isomorphic to Ξ_q(L)/O₂(Ξ_q(L)).

For an odd Fitting prime q of L/O₂(L), a Sylow subgroup of that Fitting
subgroup shows q divides |O_q(L/O₂(L))|. Cauchy's theorem makes its first
omega subgroup nontrivial. The established omega equivalence then makes
the image in K/O₂(K) a nontrivial normal q-group, so it lies in the actual
Fitting subgroup. Applying this to both contained factors transfers both
odd primes. No Thompson factorization or local-family hypotheses are needed
for this conditional transfer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed p.513, the sentence following X_q ≤ L_{C₀}.
The construction retains Ω₁(O_q), rather than replacing it by the q-core.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
variable {G : Type*} [Group G]

/-- Normality is relative to K, obtained by restricting characteristic invariance in L. -/
theorem XiP_normal_subgroupOf (q : ℕ) {L K : Subgroup G} (hKL : K ≤ L) :
    ((XiP q L).subgroupOf K).Normal :=
  normal_subgroupOf_of_le_normalizer
    (hKL.trans (L.le_normalizer.trans (normalizer_le_normalizer_XiP q L)))

/-- The actual inclusion of Ξ_q(L) in K, followed by the quotient by O₂(K). -/
def xiPToOvergroupQuotient (q : ℕ) {L K : Subgroup G} (hXK : XiP q L ≤ K) :
    XiP q L →* XiQuotient K :=
  (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hXK)

/-- Relative normality identifies the restricted quotient kernel with the intrinsic two-core. -/
theorem xiPToOvergroupQuotient_ker (q : ℕ) {L K : Subgroup G}
    (hXK : XiP q L ≤ K) (hKL : K ≤ L) :
    (xiPToOvergroupQuotient q hXK).ker = pCore 2 (XiP q L) := by
  change ((QuotientGroup.mk' (pCore 2 K)).comp (inclusion hXK)).ker = _
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  apply le_antisymm
  · exact le_sSup ⟨inferInstance,
      pCore_isPGroup.comap_of_injective _ (inclusion_injective hXK)⟩
  · have hc := pCoreIn_mono_of_normalizes (p := 2) hXK
      (hKL.trans (L.le_normalizer.trans (normalizer_le_normalizer_XiP q L)))
    intro x hx
    obtain ⟨y, hy, he⟩ := hc (mem_map.mpr ⟨x, hx, rfl⟩)
    have hyx : y = inclusion hXK x := Subtype.ext he
    change inclusion hXK x ∈ pCore 2 K
    exact hyx ▸ hy

/-- The image of Ξ_q(L) is normal in K/O₂(K). -/
theorem xiPToOvergroupQuotient_range_normal (q : ℕ) {L K : Subgroup G}
    (hXK : XiP q L ≤ K) (hKL : K ≤ L) :
    (xiPToOvergroupQuotient q hXK).range.Normal := by
  rw [xiPToOvergroupQuotient, MonoidHom.range_comp, inclusion_range]
  exact (XiP_normal_subgroupOf q hKL).map _ (QuotientGroup.mk'_surjective _)

/-- The first isomorphism theorem for the natural image in the overgroup quotient. -/
noncomputable def xiPQuotientEquivOvergroupImage (q : ℕ) {L K : Subgroup G}
    (hXK : XiP q L ≤ K) (hKL : K ≤ L) :
    XiQuotient (XiP q L) ≃* (xiPToOvergroupQuotient q hXK).range :=
  (QuotientGroup.quotientMulEquivOfEq (xiPToOvergroupQuotient_ker q hXK hKL).symm).trans
    (QuotientGroup.quotientKerEquivRange (xiPToOvergroupQuotient q hXK))

variable [Finite G]

/-- An odd prime of F(L/O₂(L)) makes the actual omega quotient of Ξ_q(L) nontrivial. -/
theorem XiP_quotient_nontrivial_of_fittingPrime (q : ℕ) [Fact q.Prime] (hq : Odd q)
    {L : Subgroup G} (hdiv : q ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    Nontrivial (XiQuotient (XiP q L)) := by
  have hd : q ∣ Nat.card (pCore q (XiQuotient L)) := by
    let F := fittingSubgroup (XiQuotient L)
    let S : Sylow q F := default
    have hS := S.dvd_card_of_dvd_card hdiv
    have hle := S.map_le_pCore inferInstance inferInstance q
    have hc : Nat.card S = Nat.card ((S : Subgroup F).map F.subtype) :=
      (Subgroup.card_map_of_injective F.subtype_injective).symm
    exact (hc ▸ hS).trans (Subgroup.card_dvd_of_le hle)
  have hω := omega₁_map_subtype_ne_bot (pCore q (XiQuotient L)) q hd
  have hne : omega (pCore q (XiQuotient L)) (p := q) 1 ≠ ⊥ := by
    intro he
    exact hω (by rw [omega₁, he, Subgroup.map_bot])
  let : Nontrivial (omega (pCore q (XiQuotient L)) (p := q) 1) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact (xiPQuotientEquivOmega hq L).toEquiv.nontrivial

/-- The natural image in K/O₂(K) is a q-group. -/
theorem xiPToOvergroupQuotient_range_isPGroup (q : ℕ) [Fact q.Prime] (hq : Odd q)
    {L K : Subgroup G} (hXK : XiP q L ≤ K) (hKL : K ≤ L) :
    IsPGroup q (xiPToOvergroupQuotient q hXK).range :=
  (XiP_quotient_isPGroup q hq L).of_equiv (xiPQuotientEquivOvergroupImage q hXK hKL)

/-- An original Fitting prime makes the natural image in K/O₂(K) nontrivial. -/
theorem xiPToOvergroupQuotient_range_nontrivial (q : ℕ) [Fact q.Prime] (hq : Odd q)
    {L K : Subgroup G} (hdiv : q ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hXK : XiP q L ≤ K) (hKL : K ≤ L) :
    Nontrivial (xiPToOvergroupQuotient q hXK).range := by
  let := XiP_quotient_nontrivial_of_fittingPrime q hq hdiv
  exact (xiPQuotientEquivOvergroupImage q hXK hKL).symm.toEquiv.nontrivial

/-- Containment of the actual radical factor transfers its odd Fitting prime. -/
theorem fittingPrime_dvd_of_XiP_le (q : ℕ) [Fact q.Prime] (hq : Odd q)
    {L K : Subgroup G} (hdiv : q ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hXK : XiP q L ≤ K) (hKL : K ≤ L) :
    q ∣ Nat.card (fittingSubgroup (XiQuotient K)) := by
  let I := (xiPToOvergroupQuotient q hXK).range
  have hqI : IsPGroup q I := xiPToOvergroupQuotient_range_isPGroup q hq hXK hKL
  let : Nontrivial I := xiPToOvergroupQuotient_range_nontrivial q hq hdiv hXK hKL
  have hle : I ≤ fittingSubgroup (XiQuotient K) :=
    le_sSup ⟨xiPToOvergroupQuotient_range_normal q hXK hKL, hqI.isNilpotent⟩
  exact (hqI.card_eq_or_dvd.resolve_left (Nat.ne_of_gt Finite.one_lt_card)).trans
    (card_dvd_of_le hle)

/-- Both specified odd Fitting primes survive when K contains both radical factors. -/
theorem fittingPrimes_dvd_of_XiP_le (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : Odd p) (hq : Odd q) {L K : Subgroup G}
    (hpdiv : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hqdiv : q ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hpK : XiP p L ≤ K) (hqK : XiP q L ≤ K) (hKL : K ≤ L) :
    p ∣ Nat.card (fittingSubgroup (XiQuotient K)) ∧
      q ∣ Nat.card (fittingSubgroup (XiQuotient K)) :=
  ⟨fittingPrime_dvd_of_XiP_le p hp hpdiv hpK hKL,
    fittingPrime_dvd_of_XiP_le q hq hqdiv hqK hKL⟩

/-- For distinct inputs, F(K/O₂(K)) has at least two distinct odd prime divisors. -/
theorem exists_two_odd_fittingPrimes_of_XiP_le (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : Odd p) (hq : Odd q) (hpq : p ≠ q) {L K : Subgroup G}
    (hpdiv : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hqdiv : q ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hpK : XiP p L ≤ K) (hqK : XiP q L ≤ K) (hKL : K ≤ L) :
    ∃ r s : ℕ, r.Prime ∧ Odd r ∧ s.Prime ∧ Odd s ∧ r ≠ s ∧
      r ∣ Nat.card (fittingSubgroup (XiQuotient K)) ∧
      s ∣ Nat.card (fittingSubgroup (XiQuotient K)) :=
  ⟨p, q, Fact.out, hp, Fact.out, hq, hpq,
    fittingPrimes_dvd_of_XiP_le p q hp hq hpdiv hqdiv hpK hqK hKL⟩

end CFSG.Quasithin.Chapter1.RadicalNormalizers
