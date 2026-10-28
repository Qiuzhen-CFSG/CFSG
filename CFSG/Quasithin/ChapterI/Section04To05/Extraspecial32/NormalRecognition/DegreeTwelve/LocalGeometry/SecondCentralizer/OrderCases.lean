module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry

/-!
# Applying the second-centralizer theorem to Thompson's order formula

The selected configuration gives the two actual second-centralizer models and
the ambient mixed-pair counts 3 and 195. Applying the existing order formula
with the independently supplied census count 240 yields orders 12096 or 95040.
This discharges the second-centralizer premise of the local-geometry consumer;
the selected configuration and local census remain explicit earlier inputs.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 4.2–4.3.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The exact order-formula consumer, with its second-centralizer premise
discharged and the independently supplied local census retained. -/
public theorem order_cases_of_selectedFusion (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SelectedFusionData h) (t : G) (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t) (c : LocalInvolutionCensus z t) :
    Nat.card G = 12096 ∨ Nat.card G = 95040 :=
  (secondCentralizerAlternative h hn d a t htE ht hnt c.classes).order_cases h ht hnt c

end CFSG.Quasithin.Extraspecial32.DegreeTwelve
