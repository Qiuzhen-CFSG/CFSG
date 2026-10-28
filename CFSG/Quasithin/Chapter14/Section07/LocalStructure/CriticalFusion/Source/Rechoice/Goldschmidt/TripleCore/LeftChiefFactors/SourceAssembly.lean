module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SourceMarking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SourceNoncentrality

/-!+# The original five-factor bound after choosing compatible target coordinates

Choose the upper remarking supplied by SourceMarking and apply the checked
13.3.14-to-chief-count implication to that single datum. The remarking changes
only natural target coordinates: the original flag, H, U, L₁, quotient map,
source action and critical path remain the same. Thus its conclusion counts
the chief factors of the original L₁, with no marking premise on the input.

The remaining local input is precisely the earlier 13.3.14 assertion that
O₂(G₁) does not centralize V₂; here H = G₁ by definition. SourceNoncentrality
constructs the point commutator, and FiveChiefFactors constructs the duality
and the count. No other part of 14.5.21 is used by this application.

This is a conditional source calculation. The noncentrality producer must
still prove 13.3.14 on the original higher-rank setup. The universal structural
and uniqueness implications retain their Chapter 12 and Chapter 1 producers.
Their discharge, and the later Goldschmidt classification, are not asserted here.

Source: Aschbacher–Smith, Lemma 13.3.14, printed p.891; the preliminary
five-factor calculation in the proof of Lemma 14.7.70, printed p.1074.
-/

public section
noncomputable section
open Subgroup NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
open Chapter12.Section08 BorelRefinements
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- Choose one compatible target marking and obtain five noncentral binary
chief factors in every complete chief series of the original L₁. The sole local
earlier-source premise is the precise plane noncentrality of 13.3.14. -/
theorem originalChief_count_of_earlier_noncentrality
    (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (hmove : ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G))
    (t : ChiefSeries (F.Li L 1)) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    5 ≤ t.noncentralTwoCount :=
  originalChief_count_of_plane_moved (upperRemark d structural) c structural uniqueness
    (upperRemark_upperMarking d structural) hmove t ht0 ht1

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
