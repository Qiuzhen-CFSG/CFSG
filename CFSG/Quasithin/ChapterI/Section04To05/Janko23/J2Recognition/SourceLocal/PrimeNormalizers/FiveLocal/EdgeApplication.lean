module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.EdgeCentralizer

/-!
# Applying the five-local source theorem to an actual graph edge

The complete 47.2 calculation supplies `FiveNormalizerTypes` to the existing
edge-centralizer theorem. This identifies the literal C_G(F.B) with A₅ and
discharges the five-normalizer premise in the graph construction. The A₅
edge-fixer equivalence is an independent earlier input and remains explicit.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2, printed p.261, and the
subsequent J₂ subgroup-graph construction. Both centralizer and endpoints
are those of the original `EdgeFrame`; no new abstract model replaces them.
-/

public section

open Theory.GroupTheory.GraphUniquenessSystem

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal

/-- Source 47.2 discharges the five-local assumption in the existing
edge-centralizer calculation, retaining the actual edge-fixer input. -/
theorem edgeFrame_centralizer_equiv_of_selectedGeometry
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (hG : Nat.card G = 604800) (S : InvolutionGeometry.SelectedGeometry D)
    (F : EdgeFrame D)
    (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5))) :
    Nonempty (F.K ≃* alternatingGroup (Fin 5)) :=
  PrimeNormalizers.edgeFrame_centralizer_equiv F he
    (fiveNormalizerTypes_of_selectedGeometry hG S)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal
