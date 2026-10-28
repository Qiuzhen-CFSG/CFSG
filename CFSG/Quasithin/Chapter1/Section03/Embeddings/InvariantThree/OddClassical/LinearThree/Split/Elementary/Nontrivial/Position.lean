module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Position.Model
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Position.Reducible
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Position.Irreducible

/-!
# Assembly of the elementary PSL₃ position dichotomy

Split according to reducibility of the full inverse image of RS in SL₃.
The reducible case requires an involution centralizer containing R and
centralizing the whole intrinsic Sylow center. In the irreducible case,
a permuted line basis gives monomial placement; the Singer and primitive
extraspecial order alternatives are excluded by the ambient Sylow's factor
sixteen.

The theorem `elementary_position` discharges both geometric cases using the
reducible involution construction and the irreducible invariant-basis theorem.
The original conditional assembly is retained as a separate interface.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); GLS3, Theorem 6.5.3(a–d) and its proof,
`refs/KGroup/GLS3/chapter6.tex`.
-/

public section

open Subgroup Matrix.SL3.SplitMonomial
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial
variable {Q : Type*} [Group Q]

/-- Assemble the placement dichotomy from the two natural-module cases.
The reducible placement and irreducible classification remain explicit
premises; this is not the unconditional source theorem. -/
theorem elementary_position_of_geometric_cases [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {p : ℕ} (hodd : Odd p) (hm : ClassicalGroup.IsPSL Q 3 p)
    (he : IsElementaryAbelian 3 R) (hc : Nat.card R = 9)
    (hred : ∀ (F : Type) [Field F] [Finite F], Nat.card F = p →
      ∀ (T : Sylow 2 PSL(3,F)) (U : Subgroup PSL(3,F)), ModelInput T U →
        ReduciblePreimage (U ⊔ (T : Subgroup _)) →
        InvolutionPosition (T : Subgroup _) U)
    (hirr : ∀ (F : Type) [Field F] [Finite F], Nat.card F = p →
      ∀ (T : Sylow 2 PSL(3,F)) (U : Subgroup PSL(3,F)), ModelInput T U →
        ¬ ReduciblePreimage (U ⊔ (T : Subgroup _)) →
        HasInvariantBasis (projectivePreimage (U ⊔ (T : Subgroup _))) ∨
          Odd (Nat.card (U ⊔ (T : Subgroup _) : Subgroup _)) ∨
          Nat.card (U ⊔ (T : Subgroup _) : Subgroup _) ∣ 216) :
    InvolutionPosition (S : Subgroup Q) R ∨ MonomialPosition p (S : Subgroup Q) R := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let U := R.map e.toMonoidHom
  have hinput : ModelInput T U := modelInput_of_pair h he hc e
  have hUT : U ⊔ (T : Subgroup _) = (R ⊔ (S : Subgroup Q)).map e.toMonoidHom := by
    change R.map e.toMonoidHom ⊔ (S : Subgroup Q).map e.toMonoidHom = _
    exact (Subgroup.map_sup _ _ _).symm
  by_cases hW : ReduciblePreimage (U ⊔ (T : Subgroup _))
  · exact Or.inl (involutionPosition_of_map (S : Subgroup Q) R e (hred F hF T U hinput hW))
  · rcases hirr F hF T U hinput hW with hb | ho | hs
    · apply Or.inr
      exact monomialPosition_of_invariantBasis hF e (hUT ▸ hb)
    · exact (product_not_odd (hF ▸ hodd) T U ho).elim
    · exact (product_card_not_dvd_216 (hF ▸ hodd) T U hs).elim

/-- An elementary subgroup of order nine permuting with the ambient Sylow
two-subgroup lies either in an involution centralizer centralizing the whole
intrinsic Sylow center, or together with the Sylow in a split monomial model. -/
theorem elementary_position [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hlarge : 3 < p) (hsplit : p % 3 = 1)
    (hm : ClassicalGroup.IsPSL Q 3 p)
    (he : IsElementaryAbelian 3 R) (hc : Nat.card R = 9) :
    InvolutionPosition (S : Subgroup Q) R ∨ MonomialPosition p (S : Subgroup Q) R := by
  apply elementary_position_of_geometric_cases h hodd hm he hc
  · intro F _ _ hF T U hinput hred
    exact involutionPosition_of_reducible hp hodd hlarge hsplit hF T U hinput hred
  · intro F _ _ hF T U hinput hirr
    exact invariantBasis_or_small_of_irreducible hp hodd hlarge hsplit hF T U hinput hirr

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial
