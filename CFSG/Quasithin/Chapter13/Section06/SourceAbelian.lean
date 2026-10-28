module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Spans
public import Theory.GroupTheory.AbelianConjugateSpan
/-!
# The actual A₅ abelian-closure interface after 13.5.10

The source Sylow flag and F.9.1 now prove the span equivalence consumed by
13.6.2. The closure in the final D record is literally the span under C_G(z),
so it is also equivalent to containment of the original V in O₂(C_G(z)).
No span-equivalence callback or synthetic hyperplane marking is retained.

These are the proved 13.5.10 inputs to 13.6.2, not the still-open 13.5.12
classification. The normal and nonnormal branches of that classification
must establish the remaining abelianness under the two actual model exclusions.

Source: Aschbacher–Smith 13.5.10 and 13.6.2, printed pp.918 and 926.
-/
@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.SourceAbelian
open CentralizerReduction TerminalContradiction.Ratio Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]

/-- The exact span-equivalence field consumed by the original A₅ local setup. -/
theorem span_equivalence (d : Context T L V V₁ V₂ V₃) (z : G)
    (h : SourceF91 T L V V₃ V₁ (Gv z)) :
    IsMulCommutative (conjugateSpanBy V₃ (Gv z)) ↔
      IsMulCommutative (conjugateSpanBy V (Gv z)) :=
  (source_span_equivalences d h).1

/-- Original 13.5.10 for precisely the closure stored in EarlierA5Setup. -/
theorem closure_abelian_iff (d : Context T L V V₁ V₂ V₃) (z : G)
    (h : SourceF91 T L V V₃ V₁ (Gv z)) :
    IsMulCommutative (centralizerConjugateClosure V z) ↔
      IsMulCommutative (conjugateSpanBy V₃ (Gv z)) := by
  rw [centralizerConjugateClosure_eq_conjugateSpanBy]
  exact (span_equivalence d z h).symm

/-- The third equivalent condition of 13.5.10 on the same C_G(z). -/
theorem closure_abelian_iff_le_core (d : Context T L V V₁ V₂ V₃) (z : G)
    (h : SourceF91 T L V V₃ V₁ (Gv z)) :
    IsMulCommutative (centralizerConjugateClosure V z) ↔ V ≤ (Gv z).pCoreIn 2 :=
  (closure_abelian_iff d z h).trans (source_span_equivalences d h).2
end CFSG.Quasithin.Chapter13.Section06.SourceAbelian
