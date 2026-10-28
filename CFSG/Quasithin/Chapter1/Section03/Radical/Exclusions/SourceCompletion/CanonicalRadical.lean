module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.SourceCompletion.MarkedA312
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.MarkedSource

/-!
# Starred membership of the original canonical radical

The actual marked A.3.12 embeddings discharge characteristic-normalizer
control for R = O₂(Ξ_p(L)T). The original radical configuration then excludes
both the exchanged rank-one and the invariant linear-three overgroups by
the proved C.2.7 model reductions. Thus Ξ_p(L) is starred under the original
maximal nonquasisimple local hypotheses, with no additional source premise.

Source: Aschbacher–Smith, Proposition 1.3.8, printed pp.512–514.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The canonical radical of a maximal nonquasisimple local member belongs
to the starred solvable uniqueness family (original 1.3.8). -/
theorem XiP_mem_XiStar_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G T)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    XiP p L ∈ XiStar G (T : Subgroup G) :=
  XiP_mem_XiStar_of_marked_A312 hG T hL hn ho hd
    (RadicalNormalizers.markedA312Input_knownSimple p L T)

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
