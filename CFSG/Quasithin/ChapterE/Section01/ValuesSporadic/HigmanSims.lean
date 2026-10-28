module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.HigmanSims.QuotientRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.GeneratorCover

/-!
# Assembly for the Higman--Sims upper-generation bound

The HS clause of Aschbacher--Smith E.1.14(5), printed p.214, concerns finite
SQTK groups with simple `L = F*(G)`, `G = LT`, and `L` isomorphic to HS.
It includes outer 2-extensions. The book cites Asc82a, Lemma 4.9, but uses
the corrected local-tau definition in E.1.2 (printed pp.209--210).

Here an actual equivalence to the published degree-100 permutation carrier
transports its two generators. Covering these generators and `T` proves
generation by a family of Sylow overgroups. Rank at most two modulo each
overgroup's intrinsic two-core then reduces any available E-generation
bound to two. This is the family output needed for E.1.12.

This module supplies only conditional assembly. It does not construct the
HS local overgroups or prove their quotient ranks. Nor does it establish
general E-generation existence for even-order groups. Those premises must
be discharged before claiming E.1.14(5). Candidate local structures occur
in A.3.12(18) and I.4.8: the involution centralizer with quotient `S₅`, and
the `4³` normalizer with quotient `L₃(2)`. Their realization and behavior in
the permitted outer extensions remain mathematical obligations.
-/

public section

namespace CFSG.Quasithin.ChapterE.HigmanSims

open Subgroup
open Sporadic.LeechRelated.HS

variable {G : Type*} [Group G] [Finite G]

/-- Conditional local-family assembly. The finite-even existence input and
the concrete local rank/coverage inputs are separate proof obligations. -/
theorem rankTwo_family_of_generator_cover
    (L : Subgroup G) (T : Sylow 2 G) (e : L ≃* Carrier)
    (hLT : L ⊔ (T : Subgroup G) = ⊤)
    (Δ : Set (Subgroup G)) (hne : Δ.Nonempty)
    (hT : ∀ H ∈ Δ, (T : Subgroup G) ≤ H)
    (ha : (e.symm generatorAElement : G) ∈ sSup Δ)
    (hb : (e.symm generatorBElement : G) ∈ sSup Δ)
    (hrank : ∀ H ∈ Δ, primeRank 2 (H ⧸ pCore 2 H) ≤ 2)
    (hex : ∀ H ∈ Δ, Even (Nat.card H) → ∃ i : ℕ, IsEGenerated i H) :
    sSup Δ = ⊤ ∧ ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ IsEGenerated 2 H := by
  have hTs : (T : Subgroup G) ≤ sSup Δ := by
    obtain ⟨H, hH⟩ := hne
    exact (hT H hH).trans (le_sSup hH)
  refine ⟨sSup_eq_top_of_generators_mem L (T : Subgroup G) e hLT Δ hTs ha hb, ?_⟩
  intro H hH
  refine ⟨hT H hH, ?_⟩
  by_cases ho : Odd (Nat.card H)
  · exact isEGenerated_of_odd ho
  · exact isEGenerated_of_quotient_rank_le (hrank H hH)
      (hex H hH (Nat.not_odd_iff_even.mp ho))

end CFSG.Quasithin.ChapterE.HigmanSims
