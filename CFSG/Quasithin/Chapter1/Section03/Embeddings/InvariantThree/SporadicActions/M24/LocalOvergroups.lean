module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.LocalData
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.LocalOvergroups.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.LocalOvergroups.TrioPlacement
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.LocalOvergroups.TrioQuotient

/-!
# Reducibility or a local quotient for every M₂₄ Sylow pair

The proved placement alternative puts every source pair either in the
reducible case or in a conjugate of the explicit octad-trio stabilizer.
Transporting the proved standard-trio quotient gives an actual overgroup
containing both members of the pair, with a surjection onto S₃ × SL₃(2)
and two-group kernel. `localQuotientEquiv` identifies the target with the
source's S₃ × L₃(2).

`localOvergroup_of_not_pairReducible` selects this overgroup under exactly
the additional premise supplied by an irreducible extending action. No
geometric coverage or quotient-construction premise remains. The source
consumer must derive that premise, or use the reducibility alternative
directly. The original unconditional `LocalOvergroups` contract and the
non-trio E₉ obstruction are preserved; `localOvergroups` remains unresolved.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528 of
`refs/quasithin.pdf`); GLS3, Table 5.3e; Aschbacher, *Sporadic Groups*,
Lemma 20.2, printed p.97.
-/

public section

open Sporadic.Mathieu
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.M24PairAction

/-- Every source pair is reducible or lies in an actual local extension with
the full product quotient and a two-group kernel. Both placement and the
standard-stabilizer quotient are proved inputs. -/
theorem reducible_or_local_overgroup
    {S : Sylow 2 M24} {R : Subgroup M24} (h : PairInput S R) :
    PairReducible S.toSubgroup R ∨
      ∃ H : Subgroup M24, S.toSubgroup ≤ H ∧ R ≤ H ∧
        ∃ f : H →* LocalQuotient, Function.Surjective f ∧ IsPGroup 2 f.ker := by
  rcases reducibleOrTrioPlacement S R h with hred | ⟨g, hg⟩
  · exact Or.inl hred
  · exact Or.inr ⟨conjugateTrioStabilizer g, le_sup_right.trans hg,
      le_sup_left.trans hg, quotient_of_standard_trio standardTrioQuotient g⟩

/-- The local-overgroup conclusion with precisely the nonreducibility premise
available from the source's irreducible extending action. -/
theorem localOvergroup_of_not_pairReducible
    {S : Sylow 2 M24} {R : Subgroup M24} (h : PairInput S R)
    (hirr : ¬ PairReducible S.toSubgroup R) :
    ∃ H : Subgroup M24, S.toSubgroup ≤ H ∧ R ≤ H ∧
      ∃ f : H →* LocalQuotient, Function.Surjective f ∧ IsPGroup 2 f.ker :=
  (reducible_or_local_overgroup h).resolve_left hirr

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.M24PairAction
