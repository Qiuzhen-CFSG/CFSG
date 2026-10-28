module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Reduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.Reduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.G2Cocycles

/-!
# Dual-cover exclusions in B.5.1(5)

The linear-two row is excluded by the actual Sylow-offender data and odd-index
averaging on the dual covering constructed from the original moved section.
The construction also proves C_V(L)=C_V(G), including a central lower
attachment. It makes no assumption that the original V was a dual covering.

For the G2 rows, the octonion cocycle normal form and both original-module
consumers are proved in G2Cocycles. The remaining geometric statement is
G2TraceDetection, separately over larger fields and the binary field. Until
those two concrete calculations are supplied, the G2 exclusions and hence the
requested three-row exclusion are unfinished.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(5),
printed pp.102–103; I.1.5–7, printed pp.408–409.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The linear-two constructor contradicts failure of the literal supplement
in B.5.1(5). Nonsplitting and the action equivalence need not be assumed: its
Sylow-offender, generation and ratio data already imply the supplement. -/
theorem linearTwo_excluded [Finite G] {K : CFSG.Quasithin.GroupClass.{u}}
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hn : s.space.toSubmodule ⊔ ρ.invariants ≠ ⊤)
    (hg : offenderSubgroup s.action = L)
    (hoff : ∀ A, IsBestOffender s.action A → ∃ S : Sylow 2 L,
      A = (S : Subgroup L).map L.subtype)
    (hq : quadraticRatio s.action = 1) : False :=
  hn (DualExtensions.linearTwo_supplement h s hg hoff hq)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
