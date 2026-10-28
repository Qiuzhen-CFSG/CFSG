module
public import Stellmacher.MainType.EightSix
public import Stellmacher.SectionEight.GeneratedEightSixObstruction

/-!
# A nonsolvable two-local in the Omega-six-minus-three type

The source-local configuration (8.6)(b) contains an elementary subgroup W of
order sixteen with nonsolvable normalizer in its graph group. The injective
embedding takes W to a nontrivial ambient two-subgroup and embeds its native
normalizer into the full ambient normalizer. The latter is therefore the
required nonsolvable two-local. No global local-solvability or Section Seven
hypothesis is imposed on the type predicate.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6)(b3), printed p.41,
the type definition on p.45, and the last assertion of Theorem 1.
-/

namespace Stellmacher
open SectionEight
universe u

public theorem IsOfOmegaSixMinusThreeType.exists_nonsolvable_twoLocal
    {H : Type u} [Group H] [Finite H]
    (h : IsOfOmegaSixMinusThreeType H) :
    ∃ U : Subgroup H, IsTwoLocal U ∧ ¬ Group.IsSolvable U := by
  obtain ⟨d⟩ := h
  let _ := d.groupK
  let _ := d.finiteK
  obtain ⟨W,_hWL,_hWN,helementary,hcard,hbad⟩ := d.caseB.normalizer_witness
  exact ambient_bad_local_of_elementary_sixteen_normalizer
    d.embedding d.embedding_injective W helementary hcard hbad

end Stellmacher
