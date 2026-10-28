module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.TheoremC
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.UnitaryClosure

/-!
# The remaining B-only odd-normalizer component models

The complete shared C catalogue, all alternating rows and arbitrary odd
PSL₂ rows are excluded using the actual local residual. In the odd
three-dimensional rows the exponent must therefore be two. The large
binary unitary-four exclusion leaves only its fixed-field-order-two case.
Every remaining alternative retains an actual group equivalence and the
original source parameter restrictions.

RemainingApplication applies this sieve to the elementary kernel selected
from the original Hall subgroup. These remaining rows are obligations, not
claimed exclusions or an unconditional proof of 4.4.3.
Source: Aschbacher--Smith A.2.2--4 and 4.4.10--12, printed pp.33,621--623,
applied in 10.2.3(2), printed p.745.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04

/-- The actual B-only component rows left after the shared C models,
alternating groups, arbitrary odd PSL₂ and large binary PSU₄ are excluded. -/
inductive SourceHallNormalizerRemainder (Q : Type*) [Group Q] : Prop
  | linear_three_square (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (model : ClassicalGroup.IsPSL Q 3 (p^2))
  | unitary_three_square (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (model : ClassicalGroup.IsPSU Q 3 (p^2))
  | symplectic_odd (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (model : ClassicalGroup.IsPSp Q 2 p)
  | g2_odd (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (model : ClassificationModels.IsG2At Q p)
  | linear_four (r : ℕ) (hp : r.Prime) (hf : ∃ k : ℕ, r = 2^(2^k)+1)
      (model : ClassicalGroup.IsPSL Q 4 r)
  | unitary_four (s : ℕ) (hp : s.Prime) (hm : ∃ b : ℕ, s+1 = 2^b)
      (model : ClassicalGroup.IsPSU Q 4 s)
  | unitary_four_two (model : ClassicalGroup.IsPSU Q 4 2)
  | unitary_five_four (model : ClassicalGroup.IsPSU Q 5 4)
  | symplectic_six_two (model : ClassicalGroup.IsPSp Q 3 2)
  | janko_three (model : Nonempty (Q ≃* Sporadic.Janko3.Model))
  | mcl (model : Nonempty (Q ≃* Sporadic.LeechRelated.McL.Carrier))

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
  (hu : UniqueMaximalOvergroup
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
      ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
  (K : Subgroup (normalizer (B : Set G)))
  (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
  (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
include D hn hBC hodd hBV hu hK hout

/-- The complete B catalogue narrows to genuine remaining models for the
actual normal component, with no unproved outer-solvability callback. -/
theorem source_nonnormal_oddNormalizer_remaining_models
    (hc : pCore 2 K = ⊥)
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K)) :
    SourceHallNormalizerRemainder (K ⧸ center K) := by
  have hC := source_nonnormal_oddNormalizer_no_theoremC_component
    D hn B hBC hodd hBV hu K hK hout hc
  cases hm with
  | alternating n hn9 e =>
    exact (source_nonnormal_oddNormalizer_no_alternating_component
      D hn B hBC hodd hBV K hu hK hout hn9 e.some).elim
  | odd hm =>
    cases hm with
    | linear_two q ho h =>
      exact (source_nonnormal_oddNormalizer_no_odd_linear_two_component
        D hn B hBC hodd hBV K hu hK hout ho h).elim
    | linear_three p e hp ho he h =>
      have he0 : e ≠ 0 := by
        intro hz
        obtain ⟨F,_,_,hF,_⟩ := h
        have hg : 1 < Nat.card F := Finite.one_lt_card
        simp only [hz,pow_zero] at hF
        omega
      have he1 : e ≠ 1 := by
        intro hz
        exact hC (.odd (.linear_three p hp ho (by simpa only [hz,pow_one] using h)))
      have he2 : e = 2 := by omega
      exact .linear_three_square p hp ho (he2 ▸ h)
    | unitary_three p e hp ho he h =>
      have he0 : e ≠ 0 := by
        intro hz
        obtain ⟨F,_,_,J,hF,_⟩ := h
        have hg : 1 < Nat.card F := Finite.one_lt_card
        simp only [hz,pow_zero,one_pow] at hF
        omega
      have he1 : e ≠ 1 := by
        intro hz
        exact hC (.odd (.unitary_three p hp ho (by simpa only [hz,pow_one] using h)))
      have he2 : e = 2 := by omega
      exact .unitary_three_square p hp ho (he2 ▸ h)
    | symplectic p hp ho h => exact .symplectic_odd p hp ho h
    | g2 p hp ho h => exact .g2_odd p hp ho h
    | linear_four r hp hf h => exact .linear_four r hp hf h
    | unitary_four s hp hm h => exact .unitary_four s hp hm h
  | bender h => exact (hC (.bender h)).elim
  | rank_two f h =>
    cases h with
    | linear hf h => exact (hC (.rank_two f (.linear hf h))).elim
    | unitary_four hf h =>
      by_cases hf1 : f = 1
      · exact .unitary_four_two (by simpa only [hf1,pow_one] using h)
      · exact (source_nonnormal_oddNormalizer_no_large_unitary_four_component
          D hn B hBC hodd hBV hu K hK hout (by omega) h).elim
    | unitary_five hf h =>
      exact .unitary_five_four (by simpa [hf] using h)
    | symplectic hf h => exact (hC (.rank_two f (.symplectic hf h))).elim
    | g2 hf h => exact (hC (.rank_two f (.g2 hf h))).elim
    | triality hf h => exact (hC (.rank_two f (.triality hf h))).elim
    | ree_f4 m hm hf h => exact (hC (.rank_two f (.ree_f4 m hm hf h))).elim
    | symplectic_derived hf h => exact (hC (.rank_two f (.symplectic_derived hf h))).elim
    | g2_derived hf h => exact (hC (.rank_two f (.g2_derived hf h))).elim
    | tits hf h => exact (hC (.rank_two f (.tits hf h))).elim
  | linear_binary n hn45 h => exact (hC (.linear_binary n hn45 h)).elim
  | symplectic_binary h => exact .symplectic_six_two h
  | sporadic h =>
    rcases h with ⟨name,⟨e⟩⟩ | ⟨e⟩ | ⟨e⟩
    · by_cases hj : name = .j3
      · subst name
        exact .janko_three ⟨e⟩
      · exact (hC (.sporadic (Or.inl ⟨name,hj,⟨e⟩⟩))).elim
    · exact (hC (.sporadic (Or.inr e))).elim
    · exact .mcl e

end CFSG.Quasithin.Chapter10
