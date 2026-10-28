module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.PrimeElements
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.HallFactors

/-!
# The original paired exclusion from prime-element Cartan coordinates

Apply the genuine preceding 11.0.4 clauses to cyclic subgroups of the odd
Hall subgroup. Lift the common field power through (A ∩ L) → L/O₂(L),
then contradict disjointness of A ∩ K and its conjugate under the same t.
Hall restriction reduces the prime-order premise to divisibility in the
actual component overlap.

These source applications require no abelian Hall decomposition or
square-centralizer assertion. They retain the literal quotient, the
original Sylow element and the compatible matrix marking. Construction
of that marking, the overlap divisor and recognition at n(H) remain local
obligations of the parameter-component owner. The preceding residual and
cubic clauses are supplied by the natural local-geometry owner, with full
source discharge retained by the shadow linear-geometry assembly owner.
This module is not an unconditional proof of 11.3.5.

Source: Aschbacher--Smith, 11.0.4 and 11.3.5(2), printed pp.760,771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Matrix
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
variable {G : Type*} [Group G] [Finite G]

theorem source_paired_prime_element_contradiction
    {T : Sylow 2 G} {L V H K : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (seed : ComponentSeed T H K)
    (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G)) (hodd : Odd (Nat.card A))
    (p : ℕ) (hp : p.Prime) (hd : p ∣ 2 ^ S.field.degree - 1)
    (hpB : p ∣ Nat.card (A ⊓ K : Subgroup G))
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (t : T) (htA : (t : G) ∈ normalizer (A : Set G))
    (htK : (t : G) ∉ normalizer (K : Set G))
    {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    (ρ : (L ⧸ pCore 2 L) →* Matrix ι ι S.field.Carrier) (hρ : Function.Injective ρ)
    (σ : S.field.Carrier ≃+* S.field.Carrier) (g : Matrix ι ι S.field.Carrier)
    (hg : g.IsUpperTriangular) (hdet : g.det ≠ 0)
    (hdiag : ∀ x : L, (x : G) ∈ A → orderOf (x : G) = p →
      ∃ d : ι → S.field.Carrier, ρ (QuotientGroup.mk' (pCore 2 L) x) = diagonal d)
    (hint : ∀ x : L, (x : G) ∈ A → orderOf (x : G) = p →
      g * (ρ (QuotientGroup.mk' (pCore 2 L) x)).map σ =
        ρ (quotientConjugation L t (D.sylow_normalizes_component t.property)
          (QuotientGroup.mk' (pCore 2 L) x)) * g) : False := by
  have hL := source_prime_order_mem S A hA p hp hd halt hres hcubic
  obtain ⟨j,hj⟩ := prime_order_power_of_triangular A L hodd p hL t htA
    (D.sylow_normalizes_component t.property) ρ hρ σ g hg hdet hdiag hint
  exact no_disjoint_factor_of_prime_order_power A (A ⊓ K) inf_le_left p hp hpB t
    (seed.paired_odd_factors_disjoint h pr hc hs A hodd t
      (h.outside.1.1.2 t.property) htK) (2 ^ j) hj

/-- Apply the new Hall-factor restriction to the original Cartan exclusion.
The remaining divisibility concerns the literal component overlap; a Hall
factor order and an abelian Hall decomposition are no longer premises. -/
theorem source_paired_hall_prime_contradiction
    {T : Sylow 2 G} {L V H K : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (seed : ComponentSeed T H K)
    (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (p : ℕ) (hp : p.Prime) (hd : p ∣ 2 ^ S.field.degree - 1)
    (hpOverlap : p ∣ Nat.card ((H ⊓ normalizer (L : Set G)) ⊓ K : Subgroup G))
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (t : T) (htA : (t : G) ∈ normalizer (A : Set G))
    (htK : (t : G) ∉ normalizer (K : Set G))
    {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    (ρ : (L ⧸ pCore 2 L) →* Matrix ι ι S.field.Carrier) (hρ : Function.Injective ρ)
    (σ : S.field.Carrier ≃+* S.field.Carrier) (g : Matrix ι ι S.field.Carrier)
    (hg : g.IsUpperTriangular) (hdet : g.det ≠ 0)
    (hdiag : ∀ x : L, (x : G) ∈ A → orderOf (x : G) = p →
      ∃ d : ι → S.field.Carrier, ρ (QuotientGroup.mk' (pCore 2 L) x) = diagonal d)
    (hint : ∀ x : L, (x : G) ∈ A → orderOf (x : G) = p →
      g * (ρ (QuotientGroup.mk' (pCore 2 L) x)).map σ =
        ρ (quotientConjugation L t (D.sylow_normalizes_component t.property)
          (QuotientGroup.mk' (pCore 2 L) x)) * g) : False := by
  have hodd : Odd (Nat.card A) := by
    have hh := OddHall.odd_hall_odd hHall
    rwa [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv] at hh
  have hn : ¬ (K.subgroupOf H).Normal := by
    intro hn
    exact htK ((normal_subgroupOf_iff_le_normalizer seed.component.1).mp hn
      (h.outside.1.1.2 t.property))
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    have hpow : 1 ≤ 2 ^ S.field.degree := Nat.one_le_pow _ _ (by decide)
    have h2 : 2 ∣ 2 ^ S.field.degree := dvd_pow_self 2 (by have := S.field.degree_pos; omega)
    have hx := Nat.mod_eq_zero_of_dvd hd
    have hy := Nat.mod_eq_zero_of_dvd h2
    omega
  have hpB := seed.paired_hall_factor_prime_dvd h pr hc hs hn A hA hHall p hp hp2 hpOverlap
  exact source_paired_prime_element_contradiction S h pr hc hs seed A hA hodd p hp hd hpB
    halt hres hcubic t htA htK ρ hρ σ g hg hdet hdiag hint

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
