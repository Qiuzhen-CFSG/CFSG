module
public import CFSG.Quasithin.Chapter16.Section04To05.Basic

/-!
# Inner involutions detected by conjugate products

The order-two bound in 16.4.9(1) implies the detector in 16.4.9(3): put
an inner involution into a Sylow subgroup of the relative normalizer. If
the conjugate were outside Δ₀, that Sylow subgroup would have order two,
so its omega subgroup would already lie in KL.

For 16.5.6(5), write u = cv with c centralizing L and c² = 1. Then
u uˡ = v vˡ. If this nonidentity product lies in X, conjugating back by
the chosen g produces an involution in another conjugate J of K. Its
projection on L is the conjugated product, so the detector places J in Δ₀.
The final theorem below proves this witness construction; excluding two-central
projections and constructing the model-specific product are separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1189 and 1197. Conjugation is left conjugation throughout. In particular,
the conjugate called (K')^(l g⁻¹) in the source is represented explicitly
by the conjugator g⁻¹ * l * g after changing conventions.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections
open Subgroup
variable {G : Type*} [Group G]

/-- Source 16.4.9(1) implies its inner-involution detection clause (3). -/
theorem mem_deltaZero_of_inner_involution [Finite G] {L J : Subgroup G}
    (hnormalizers : normalizer (centralizer (L : Set G) : Set G) =
      normalizer (L : Set G))
    (hsmall : ∀ J ∈ delta L, J ∉ deltaZero L →
      ∀ R : Subgroup G, SylowIn R
        (J ⊓ normalizer (centralizer (L : Set G) : Set G)) → Nat.card R = 2)
    (hJ : ∃ a : G, J = (centralizer (L : Set G)).conjBy a)
    {i : G} (hiJ : i ∈ J) (hi2 : orderOf i = 2)
    (hiKL : i ∈ centralizer (L : Set G) ⊔ L)
    (hiK : i ∉ centralizer (L : Set G)) : J ∈ deltaZero L := by
  let H := J ⊓ normalizer (centralizer (L : Set G) : Set G)
  have hiH : i ∈ H := by
    refine ⟨hiJ, ?_⟩
    rw [hnormalizers]
    exact (sup_le (centralizer_le_normalizer _) L.le_normalizer) hiKL
  have hiH2 : orderOf (⟨i, hiH⟩ : H) = 2 := by
    rwa [← orderOf_injective H.subtype H.subtype_injective]
  have hd : J ∈ delta L := by
    refine ⟨hJ, ?_, ?_⟩
    · intro he
      exact hiK (he ▸ hiJ)
    · exact even_iff_two_dvd.mpr (hiH2 ▸ orderOf_dvd_natCard (⟨i, hiH⟩ : H))
  by_contra hnot
  have hp : IsPGroup 2 (zpowers (⟨i, hiH⟩ : H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hiH2, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  let R := (S : Subgroup H).map H.subtype
  have hR : SylowIn R H := ⟨S, rfl⟩
  have hiR : i ∈ R := ⟨⟨i, hiH⟩, hS (mem_zpowers _), rfl⟩
  have hcard : Nat.card R = 2 := hsmall J hd hnot R hR
  have heq : zpowers i = R := eq_of_le_of_card_ge (zpowers_le.mpr hiR)
    (by rw [Nat.card_zpowers, hi2, hcard])
  apply hnot
  refine ⟨hd, R, hR, ?_⟩
  exact (omegaOneAmbient_le R).trans (heq ▸ zpowers_le.mpr hiKL)

/-- Cancelling the commuting involution factor gives the product of projections. -/
theorem product_of_projected_involutions {L : Subgroup G} {c v l : G}
    (hc : c ∈ centralizer (L : Set G)) (hc2 : c * c = 1)
    (hv : v ∈ L) (hl : l ∈ L) :
    (c * v) * (MulAut.conj l (c * v)) = v * MulAut.conj l v := by
  have hlc : MulAut.conj l c = c := by
    change l * c * l⁻¹ = c
    rw [mem_centralizer_iff.mp hc l hl, mul_inv_cancel_right]
  rw [map_mul, hlc]
  calc
    c * v * (c * MulAut.conj l v) = (c * (v * c)) * MulAut.conj l v := by group
    _ = (c * (c * v)) * MulAut.conj l v := by rw [mem_centralizer_iff.mp hc v hv]
    _ = v * MulAut.conj l v := by rw [← mul_assoc c c, hc2, one_mul]

/-- The conjugation calculation in 16.5.6(5): a product in X gives an
inner involution in a new conjugate of K, so 16.4.9(3) applies. -/
theorem exists_inner_involution_of_product
    {L X : Subgroup G} {g l u w : G}
    (hdisjoint : Disjoint L (centralizer (L : Set G)))
    (hXL : X ≤ L) (hgX : g ∈ normalizer (X : Set G))
    (hu : u ∈ (centralizer (L : Set G)).conjBy g) (hu2 : orderOf u = 2)
    (hwX : w ∈ X) (hw1 : w ≠ 1) (hw : w = u * MulAut.conj l u)
    (hdetect : ∀ (J : Subgroup G),
      (∃ a : G, J = (centralizer (L : Set G)).conjBy a) →
      ∀ i : G, i ∈ J → orderOf i = 2 →
        i ∈ centralizer (L : Set G) ⊔ L → i ∉ centralizer (L : Set G) →
        J ∈ deltaZero L) :
    ∃ (J : Subgroup G) (i k : G), J ∈ deltaZero L ∧ i ∈ J ∧ orderOf i = 2 ∧
      k ∈ centralizer (L : Set G) ∧
      i = k * MulAut.conj g⁻¹ w ∧ MulAut.conj g⁻¹ w ∈ L ∧
      MulAut.conj g⁻¹ w ≠ 1 := by
  let e := MulAut.conj g⁻¹
  let k := e u
  let i := e (MulAut.conj l u)
  let J := (centralizer (L : Set G)).conjBy (g⁻¹ * l * g)
  have hk : k ∈ centralizer (L : Set G) := by
    rcases hu with ⟨a, ha, rfl⟩
    simpa [k, e, MulAut.conj_apply, mul_assoc] using ha
  have hiJ : i ∈ J := by
    rcases hu with ⟨a, ha, rfl⟩
    refine ⟨a, ha, ?_⟩
    simp [i, e, MulAut.conj_apply, mul_assoc]
  have hi2 : orderOf i = 2 := by
    rw [show i = e (MulAut.conj l u) from rfl,
      e.orderOf_eq, (MulAut.conj l).orderOf_eq, hu2]
  have hk2 : k * k = 1 := by
    have hu' : u * u = 1 := by simpa [pow_two] using (orderOf_eq_prime_iff.mp hu2).1
    simpa [k, ← map_mul] using congrArg e hu'
  have hi : i = k * e w := by
    have hh : e w = k * i := by rw [hw, map_mul]
    rw [hh, ← mul_assoc, hk2, one_mul]
  have hqX : e w ∈ X := by
    have hn := (normalizer (X : Set G)).inv_mem hgX
    exact (mem_normalizer_iff.mp hn w).mp hwX
  have hqL : e w ∈ L := hXL hqX
  have hq1 : e w ≠ 1 := fun h => hw1 (e.injective (by simpa using h))
  have hiKL : i ∈ centralizer (L : Set G) ⊔ L := by
    rw [hi]
    exact mul_mem_sup hk hqL
  have hiK : i ∉ centralizer (L : Set G) := by
    intro hiK
    have hqK : e w ∈ centralizer (L : Set G) := by
      have hh := (centralizer (L : Set G)).mul_mem hk hiK
      rwa [hi, ← mul_assoc, hk2, one_mul] at hh
    exact hq1 (Subgroup.disjoint_def.mp hdisjoint hqL hqK)
  exact ⟨J, i, k, hdetect J ⟨g⁻¹ * l * g, rfl⟩ i hiJ hi2 hiKL hiK,
    hiJ, hi2, hk, hi, hqL, hq1⟩

end CFSG.Quasithin.Chapter16.Intersections
