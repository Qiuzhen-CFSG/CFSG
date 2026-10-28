module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.PairIndex.Geometry
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.PairIndex.FactorNormalizer.StandardLevi

/-!
# Factor normalizers from concrete Levi geometry

Conjugation places the supplied component on the standard fixed B₂ Levi.
The normalizer inside the maximal subgroup embeds into that Levi's ambient
normalizer. Meanwhile, the commuting components have trivial intersection
and their join has order `|Sz(q)|²`. An ambient upper bound of the same size
therefore identifies the relative normalizer with that join.

The conditional assembly below retains two genuine geometric obligations:
placement of the actual component, and the concrete Levi normalizer bound.
It does not yet assert `identifiedFactorNormalizer`. Placement is shared
with the carrier-identification argument; no placement of the second factor,
normality of the join, or component-exhaustion hypothesis is used.

Source context: Malle, J. Algebra 139 (1991), 52--69,
DOI 10.1016/0021-8693(91)90283-E; the Sz(q)≀2 entry reproduced in
the proof of Theorem 5 of arXiv:0910.4758, pp.2--3. The counting argument
uses the radical-free component product of Aschbacher--Smith A.3.3(5)--(6).
-/

public section

namespace ReeF4.MaximalSubgroups.CommutingComponents

open Subgroup BenderSuzuki.MatrixGroups CarrierIdentification FactorNormalizer

private theorem relative_normalizer_le_of_conjugate_card
    {G : Type*} [Group G] [Finite G] {M : Subgroup G} {L K : Subgroup M}
    (hR : solvableRadical M = ⊥) (hL : L.IsCComponent) (hc : ⁅L, K⁆ = ⊥)
    {A : Subgroup G} (g : G)
    (hg : (L.map M.subtype).map (MulAut.conj g).toMonoidHom = A)
    (hcard : Nat.card (normalizer (A : Set G)) ≤ Nat.card L * Nat.card K) :
    normalizer (L : Set M) ≤ L ⊔ K := by
  have hjoin : L ⊔ K ≤ normalizer (L : Set M) := by
    apply sup_le L.le_normalizer
    exact (commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm])).trans
      (centralizer_le_normalizer (L : Set M))
  have hamb : Nat.card (normalizer (L : Set M)) ≤
      Nat.card (normalizer (A : Set G)) := by
    calc
      _ = Nat.card ((normalizer (L : Set M)).map M.subtype) :=
        (card_map_of_injective M.subtype_injective).symm
      _ ≤ Nat.card (normalizer (L.map M.subtype : Set G)) :=
        card_le_of_le (L.le_normalizer_map M.subtype)
      _ = Nat.card ((normalizer (L.map M.subtype : Set G)).map
          (MulAut.conj g).toMonoidHom) :=
        (card_map_of_injective (MulAut.conj g).injective).symm
      _ = _ := by rw [map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective, hg]
  obtain ⟨e, _⟩ := hL.exists_mulEquiv_prod_sup_of_solvableRadical_eq_bot hR hc
  have hjcard : Nat.card (L ⊔ K : Subgroup M) = Nat.card L * Nat.card K := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod]
  exact (eq_of_le_of_card_ge hjoin (hjcard ▸ hamb.trans hcard)).ge

/-- A concrete placement of the first factor and the corresponding ambient
cardinality bound suffice. The second factor keeps its supplied embedding. -/
theorem factorNormalizer_le_of_leviConjugacy_of_card
    {m : ℕ} {M : Subgroup (Model m)} {L K : Subgroup M}
    (hR : solvableRadical M = ⊥) (hL : L.IsCComponent) (hc : ⁅L, K⁆ = ⊥)
    (eL : L ≃* SuzukiMatrixGroup m) (eK : K ≃* SuzukiMatrixGroup m)
    (g : Model m)
    (hg : (L.map M.subtype).map (MulAut.conj g).toMonoidHom = standardSuzukiLevi m)
    (hcard : Nat.card (normalizer (standardSuzukiLevi m : Set (Model m))) ≤
      Nat.card (SuzukiMatrixGroup m) ^ 2) :
    normalizer (L : Set M) ≤ L ⊔ K := by
  apply relative_normalizer_le_of_conjugate_card hR hL hc g hg
  simpa only [Nat.card_congr eL.toEquiv, Nat.card_congr eK.toEquiv, pow_two] using hcard

/-- Conditional assembly reusing the geometric placement from carrier
identification. Both displayed geometric premises still need proofs. -/
theorem identifiedFactorNormalizer_of_leviConjugacy_of_normalizerCard
    (hconj : ComponentLeviConjugacy) (hcard : StandardLeviNormalizerCardBound) :
    IdentifiedFactorNormalizer := by
  intro m hm M hM hsolv hR L K hL hK hne hc eL eK
  obtain ⟨g, hg⟩ := hconj m hm M hM hsolv hR L K hL hK hne hc
  exact factorNormalizer_le_of_leviConjugacy_of_card hR hL hc eL eK g hg (hcard m hm)

end ReeF4.MaximalSubgroups.CommutingComponents
