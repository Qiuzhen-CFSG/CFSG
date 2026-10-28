module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.QuotientTransport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair

/-!
# Reduction of the forced outer action to the inner Sylow pair

If T acts by inner automorphisms on B/O₂(B), every element of N_T(P)
acts on the complement image through an inner automorphism preserving
both that image and the image of T ∩ B. A proper invariant subgroup for
these inner pair automorphisms contradicts the genuine LocalInput
irreducibility, transported along the actual complement isomorphism.

The Sylow hypothesis restricts to B because B is normal in B T, and then
descends to B/O₂(B). The complement and normalizer-factor conditions give
permutation of the two subgroup images. The final theorem assembles these
steps against the explicitly unproved intrinsic L₄(2) pair calculation;
it is a conditional reduction, not the completed source action theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 1.3.9(1), printed p.514, using the local input of 1.3.2 and 1.3.4.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions
open XiEmbedding XiEmbedding.InvariantThree
universe u
variable {Q : Type u} [Group Q]

/-- A proper nonzero subgroup fixed by the inner automorphisms of a Sylow pair. -/
def InnerPairInvariant (S R : Subgroup Q) : Prop :=
  ∃ A : Subgroup (R ⧸ frattini R), A ≠ ⊥ ∧ A ≠ ⊤ ∧
    ∀ α : MulAut R,
      (∃ q : Q, (∀ x : Q, MulAut.conj q x ∈ S ↔ x ∈ S) ∧
        ∀ x : R, (α x : Q) = MulAut.conj q x) →
      ∀ x ∈ A, quotientAut (frattini R) α x ∈ A

variable {G : Type u} [Group G]

/-- A common invariant for the inner Sylow pair forces a genuinely outer action. -/
theorem not_le_innerNormalizer_of_innerPairInvariant
    {T X P H B : Subgroup G} (h : LocalInput 3 T X P H)
    (hPB : P ≤ B) (hTB : T ≤ normalizer (B : Set G))
    (hinv : InnerPairInvariant (quotientImage B T) (quotientImage B P)) :
    ¬ T ≤ innerTwoQuotientNormalizer B := by
  intro hinner
  obtain ⟨A, hAb, hAt, hA⟩ := hinv
  apply (component_normalizer_irreducible h hPB A ?_).elim hAb hAt
  intro s
  apply hA (normalizerAction h hPB s)
  obtain ⟨q, hq⟩ := (mem_innerNormalizer_iff_quotient_action
    (⟨s, hTB s.property.1⟩ : normalizer (B : Set G))).mp (hinner s.property.1)
  have hact : componentAction hTB ⟨s, s.property.1⟩ = MulAut.conj q := hq
  refine ⟨q, ?_, ?_⟩
  · intro x
    rw [← hact]
    exact componentAction_preserves_two_intersection hTB _ x
  · intro x
    rw [← hact]
    exact normalizerAction_coe h hPB hTB s x

/-- The intrinsic matrix calculation needed for the forced outer action.
The permuting Sylow pair is essential; an arbitrary E₉ subgroup does not suffice. -/
def LinearFourInnerPairTheorem : Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q], ClassicalGroup.IsPSL Q 4 2 →
    ∀ (S : Sylow 2 Q) (R : Subgroup Q), XiOddQuotient 3 R →
      (R : Set Q) * (S : Set Q) = (S : Set Q) * (R : Set Q) →
      InnerPairInvariant (S : Subgroup Q) R

/-- Conditional assembly of the forced outer action from the intrinsic pair calculation.
The complete LocalInput, including complement, residual and irreducibility, is retained. -/
theorem forced_outer_of_innerPairTheorem [Finite G]
    (hpair : LinearFourInnerPairTheorem.{u})
    {T X P H B : Subgroup G} (h : LocalInput 3 T X P H)
    (hT : IsSylowIn 2 T H) (hH : H = B ⊔ T)
    (hXB : X ≤ B) (hTB : T ≤ normalizer (B : Set G))
    (hmodel : ClassicalGroup.IsPSL (XiQuotient B) 4 2) :
    ¬ T ≤ innerTwoQuotientNormalizer B := by
  have hPB : P ≤ B := (le_sup_right.trans h.complement.le).trans hXB
  have hBH : B ≤ H := hH ▸ le_sup_left
  have hBn : (B.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBH).mpr
      (hH ▸ sup_le B.le_normalizer hTB)
  obtain ⟨S, hS⟩ := component_quotient_sylow hT hBH hBn
  apply not_le_innerNormalizer_of_innerPairInvariant h hPB hTB
  rw [← hS]
  apply hpair (XiQuotient B) hmodel S (quotientImage B P)
  · exact h.odd_complement.of_mulEquiv (complementEquiv h hPB)
  · simpa only [← hS, Sylow.coe_coe] using component_quotient_permute h hPB

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions
