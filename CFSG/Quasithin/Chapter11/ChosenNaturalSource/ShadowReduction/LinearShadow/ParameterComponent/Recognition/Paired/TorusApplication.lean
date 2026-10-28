module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.TorusDivisor

/-!
# The source Hall prime and Cartan exclusion from rank-one recognition

The Borel calculation discharges the component-overlap divisor in the
Hall construction. At the original generation parameter n or 2n, choose
an odd prime of 2^n - 1, an actual odd Hall subgroup A, and the same
Sylow exchange element t, with a moved prime-order element in A ∩ K.
The second application removes the overlap-divisibility premise from
the original prime-element Cartan contradiction.

The source counterexample, literal quotients and generation minimum are
unchanged. Recognition and compatible diagonal semilinear coordinates
remain explicit obligations of the parameter-component owner. These
conditional results do not complete 11.3.5 or discharge the original
fixed-point construction. Final source assembly remains with the shadow
linear-geometry owner, including the preceding residual/cubic clauses
from natural local geometry and the independent doubled exclusion.

Source: Aschbacher--Smith, 11.3.5(2), printed pp.771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Matrix
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- Choose the original Hall subgroup and moved prime element with the
component-overlap divisor proved from the actual rank-one model. -/
theorem ComponentSeed.exists_paired_hall_prime_element_at_parameter (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H))
    (hk : ChapterE.generationParameter H = S.field.degree ∨
      ChapterE.generationParameter H = 2 * S.field.degree)
    :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ S.field.degree - 1 ∧
      ∃ A : Subgroup G, A ≤ H ⊓ normalizer (L : Set G) ∧
        IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G))) ∧
        Odd (Nat.card A) ∧ ∃ t : T, (t : G) ∈ normalizer (A : Set G) ∧
          (t : G) ∉ normalizer (K : Set G) ∧
          Disjoint (A ⊓ K) ((A ⊓ K).map (MulAut.conj (t : G)).toMonoidHom) ∧
          ∃ x ∈ A ⊓ K, orderOf x = p ∧ (t : G)*x*(t : G)⁻¹ ≠ x := by
  exact s.exists_paired_hall_prime_element_of_parameter h pr hc hs hn hm hk
    (s.paired_linear_overlap_torus_dvd h pr hc hs hn hm)

namespace Paired
/-- The rank-one model discharges the Hall-factor order premise of the
original Cartan contradiction. All coordinates retain the same t. -/
theorem source_paired_hall_prime_contradiction_of_model
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
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H))
    (hk : ChapterE.generationParameter H = S.field.degree ∨
      ChapterE.generationParameter H = 2 * S.field.degree)
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
  have hn : ¬ (K.subgroupOf H).Normal := by
    intro hn
    exact htK ((normal_subgroupOf_iff_le_normalizer seed.component.1).mp hn
      (h.outside.1.1.2 t.property))
  have htorus : 2 ^ S.field.degree - 1 ∣ 2 ^ ChapterE.generationParameter H - 1 := by
    rcases hk with he | he
    · rw [he]
    · rw [he, Nat.mul_comm 2 S.field.degree, pow_mul]
      simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2
  have hdK := hd.trans (htorus.trans (seed.paired_linear_overlap_torus_dvd h pr hc hs hn hm))
  exact source_paired_hall_prime_contradiction S h pr hc hs seed A hA hHall p hp hd hdK
    halt hres hcubic t htA htK ρ hρ σ g hg hdet hdiag hint

end Paired
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
