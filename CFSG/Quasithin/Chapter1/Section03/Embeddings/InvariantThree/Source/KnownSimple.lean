module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.Source.TheoremC
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The full known-simple intrinsic p=3 invariant-component conclusion

The proved simultaneous A.2.1–3 theorem supplies both source implications
in the invariant-three sieve. Every family, central cover and pair-action
premise has already been discharged. The conclusion retains Held.

Source: Aschbacher–Smith Proposition 1.3.4, printed p.511 (PDF p.528),
with the adequate Held alternative described in quasithin-proof-basis.md.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.Source
universe u

/-- The complete catalogue specialization has only original local/Sylow and
component inputs; no universal classification premise remains. -/
theorem alternatives_knownSimple {G : Type u} [Group G] [Finite G]
    {T X P H L : Subgroup G}
    (h : LocalInput 3 T X P H) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hq : IsQuasisimple (XiQuotient L)) (hPL : P ≤ L) (hcomm : ⁅L, P⁆ = L) :
    Alternatives 3 T P L ∨ HeldAlternative 3 T P L :=
  alternatives_of_theoremAC h hH hT hLH hLn hq hPL hcomm
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.Source
