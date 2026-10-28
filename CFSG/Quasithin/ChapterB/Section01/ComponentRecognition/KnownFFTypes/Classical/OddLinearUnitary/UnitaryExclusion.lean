module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.PrimeDegree
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.ConjugateGeneration
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.FiveOuterDisplacement

/-!
# The odd-prime unitary parameter restriction in K.2

For the actual finite SQTK actor, a faithful binary representation irreducible
on its quasisimple generalized Fitting subgroup with central quotient PSU₃(p)
has cubic ratio at most two only when the fixed-field prime p is three.

The binary degree minimum and five-conjugate bound leave only p = 3 or 5.
At five, four conjugates bound the degree by 24. The outer-involution
displacement estimate then places every small actor inside the component;
its two-rank bound gives degree at most 16, contradicting the minimum 20.
All three independent inputs to `SourceReduction` are discharged here.
The original central cover, Hermitian form, binary module and outer actions
are retained; no hypothesis is imposed on the full linear normalizer.

Sources: Aschbacher–Smith, K.2, printed p.453; Guralnick–Malle,
*Classification of 2F-modules I*, Proposition 4.3, manuscript pp.10–11.
The Chapter K consumer connection is in `UnitaryExclusion.SourceApplication`.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion

universe u v

/-- The source PSU₃(p) restriction, with every degree, generation and
outer-displacement premise discharged for the literal ambient action. -/
theorem source_parameter_eq_three
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L]
    {p : ℕ} (h : SourceHypotheses ρ L p) (hq : cubicRatio ρ ≤ 2) : p = 3 :=
  source_parameter_eq_three_of_inputs ρ L primeDegreeBound sourceConjugateBounds
    source_five_outer_displacement h hq

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
