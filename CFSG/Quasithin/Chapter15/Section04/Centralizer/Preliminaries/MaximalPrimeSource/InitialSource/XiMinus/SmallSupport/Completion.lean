module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.SmallSupport.Factors
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.NormalizerTransport
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.OmegaCenter
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.ReducedAction

/-!
# Completion of the original five-factor implication

The original reducedness and X-kernel containment give the exact Sylow
centralizer. The omega-center comparison then makes N_G(X) intersect
N_G(O₂(XT)) preserve V. The canonical pair is equivariant under this group,
and the checked normalizer transport gives the same permutation property
for all of N_G(X). The three-or-five prime restriction and this pair prove
the original Xi-minus conclusion.

Only the original module conditions remain as premises; the source
assembly discharges them using faithful Xi membership and the independent
15.4.2(4) ratio bound. No pair or permutation is an input.
Source: Aschbacher--Smith, Lemma 3.2.13, printed pp.584--585.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual two Frattini factors are preserved by the full original normalizer. -/
theorem source_five_normalizer_frattini_pair (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ Chapter1.Xi G (T : Subgroup G))
    (hred : IsPReduced 2 (sourceModule (T : Subgroup G) X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2)
    (hp : Chapter1.XiOddQuotient 5 (Chapter1.XiQuotient X)) :
    HasNormalizerFrattiniPair X := by
  obtain ⟨B, E, hB, hE, hne, hsup, hperm⟩ :=
    source_moduleNormalizer_frattini_pair hX T.isPGroup' hred hk hratio hp
  apply source_frattini_pair_of_core_normalizer T hX B E hB hE hne hsup
  intro m
  exact hperm ⟨m, m.property.1⟩
    (source_normalizer_core_normalizes_module T X hred
      (source_sylow_centralizer_eq_core_of_kernel T hX ((sourceKernelInFrattini_iff hX).mp hk))
      m.property)

/-- The original module hypotheses imply Xi-minus membership, including its automizer bound. -/
theorem source_mem_XiMinus_of_module_conditions (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ Chapter1.Xi G (T : Subgroup G))
    (hred : IsPReduced 2 (sourceModule (T : Subgroup G) X))
    (hk : SourceKernelInFrattini hX)
    (hratio : Representation.BinaryOffender.cubicRatio (sourceRepresentation hX) ≤ 2) :
    X ∈ Chapter3.XiMinus G (T : Subgroup G) :=
  source_mem_XiMinus_of_five_pair hX T.isPGroup' hred hratio
    (source_five_normalizer_frattini_pair T hX hred hk hratio)

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
