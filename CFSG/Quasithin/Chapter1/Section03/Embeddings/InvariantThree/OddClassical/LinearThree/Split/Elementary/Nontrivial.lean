module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Position
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Monomial
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction

/-!
# Nontrivial elementary intersections in split PSL₃

The involution-centralizer branch is proved in the supporting reduction.
For the monomial branch, transport the actual ambient Sylow and elementary
subgroup to the projective model. Permutability gives the exact product
order, and the supplied ambient three-rank transfers through the model
isomorphism. A concrete monomial intersection calculation then pulls back.

The final theorem discharges both geometric inputs using the proved position
dichotomy and monomial calculation. The conditional assembly is retained as
a separate interface.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of refs/quasithin.pdf); GLS3, Theorem 6.5.3(a–d).
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split

open Theory.GroupTheory ElementaryNontrivial

variable {Q : Type*} [Group Q]

/-- Conditional assembly of the two geometric branches. The position
dichotomy and the concrete monomial calculation are explicit inputs here,
discharged in `projective_elementary_intersection_ne_bot` below. -/
theorem projective_elementary_intersection_ne_bot_of_position
    [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hm : ClassicalGroup.IsPSL Q 3 p) (he : IsElementaryAbelian 3 R)
    (hc : Nat.card R = 9)
    (hpos : InvolutionPosition (S : Subgroup Q) R ∨ MonomialPosition p (S : Subgroup Q) R)
    (hmono : ∀ (F : Type) [Field F] [Finite F], Nat.card F = p →
      ∀ (T : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
        (U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)),
        IsElementaryAbelian 3 U → Nat.card U = 9 →
        primeRank 3 (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = 2 →
        Nat.card (U ⊔ (T : Subgroup _) : Subgroup _) = 9 * Nat.card T →
        U ⊔ (T : Subgroup _) ≤ Matrix.SL3.SplitMonomial.projective F →
        (centralizerDerived (T : Subgroup _)).subgroupOf U ≠ ⊥) :
    (centralizerDerived (S : Subgroup Q)).subgroupOf R ≠ ⊥ := by
  rcases hpos with hpos | ⟨F, _, _, hF, e, hplace⟩
  · exact intersection_ne_bot_of_involutionPosition h.oddComplement.not_isCyclic hp hlarge hm hpos
  · let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
    let U := R.map e.toMonoidHom
    have hT : (T : Subgroup _) = (S : Subgroup Q).map e.toMonoidHom :=
      Sylow.coe_mapSurjective e.surjective S
    have hUT : U ⊔ (T : Subgroup _) = (R ⊔ (S : Subgroup Q)).map e.toMonoidHom := by
      rw [hT, Subgroup.map_sup]
    have hcardT : Nat.card T = Nat.card S :=
      (Nat.card_congr ((S : Subgroup Q).equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
    have hcardU : Nat.card U = 9 :=
      (Nat.card_congr (R.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm.trans hc
    have hprod : Nat.card (U ⊔ (T : Subgroup _) : Subgroup _) = 9 * Nat.card T := by
      rw [hUT, ← Nat.card_congr ((R ⊔ (S : Subgroup Q)).equivMapOfInjective
        e.toMonoidHom e.injective).toEquiv, EvenRankTwo.product_card h, hc, hcardT]
    have hrank : primeRank 3 (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = 2 :=
      (primeRank_equiv 3 e).symm.trans h.rank
    have hU : IsElementaryAbelian 3 U := by
      let _ := he
      let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact IsElementaryAbelian.map e.toMonoidHom
    have hne := hmono F hF T U hU hcardU hrank hprod (by rwa [hUT])
    apply intersection_ne_bot_of_map (S : Subgroup Q) R e
    rwa [hT] at hne

/-- An elementary complement of order nine permuting with the ambient Sylow
two-subgroup in an actual split PSL₃ model meets the derived centralizer of
the whole intrinsic Sylow center nontrivially. -/
theorem projective_elementary_intersection_ne_bot
    [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p) (hmod : p % 3 = 1)
    (hm : ClassicalGroup.IsPSL Q 3 p) (he : IsElementaryAbelian 3 R)
    (hc : Nat.card R = 9) :
    (centralizerDerived (S : Subgroup Q)).subgroupOf R ≠ ⊥ := by
  apply projective_elementary_intersection_ne_bot_of_position h hp hlarge hm he hc
    (elementary_position h hp ho hlarge hmod hm he hc)
  intro F _ _ hF T U hU hcard hrank hprod hmono
  exact monomial_intersection_ne_bot hF hp ho hlarge hmod T U hU hcard hrank hprod hmono

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split
