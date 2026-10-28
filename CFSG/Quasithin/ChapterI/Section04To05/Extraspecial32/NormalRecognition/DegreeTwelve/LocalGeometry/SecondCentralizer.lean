module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Counts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Recognition

/-!
# The second centralizer: marked recognition and mixed-pair counting

The checked counts in `C₂ × S₄` and `C₂ × S₅` transport to the literal ambient
Thompson fiber along a marked isomorphism. This supplies both the isomorphism
and count required by `SecondCentralizerAlternative.order_cases`.

The selected core intersection supplies the marked local subgroup and its
Sylow placement. Two transfers, A₄/A₅ recognition and the extension
identifications then give the marked model of the whole centralizer. The final
theorem discharges these structural inputs from the original local hypotheses,
the selected configuration and two-class coverage. No ambient order or
simplicity hypothesis is needed.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 4.1–4.3.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve

open SecondCentralizer

variable {G : Type*} [Group G] [Finite G] {z t : G}

/-- Actual marked centralizer recognition supplies the original alternative,
including its ambient mixed-pair counts. The final theorem below supplies this
recognition premise from the selected local configuration. -/
public theorem secondCentralizerAlternative_of_markedModels (h : Hypotheses z)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (hc : ∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x)
    (hm : Nonempty (MarkedModel z t 4) ∨ Nonempty (MarkedModel z t 5)) :
    SecondCentralizerAlternative z t := by
  rcases hm with hm | hm
  · obtain ⟨m⟩ := hm
    exact Or.inl ⟨⟨m.equiv⟩,
      (m.kappa_eq h.involution ht hnt hc).trans card_modelFiber_four⟩
  · obtain ⟨m⟩ := hm
    exact Or.inr ⟨⟨m.equiv⟩,
      (m.kappa_eq h.involution ht hnt hc).trans card_modelFiber_five⟩

/-- The second-centralizer alternatives of source 4.2 and their mixed-pair
counts, from the selected configuration of 4.1 and the two ambient involution
classes. Local construction, both transfers, recognition and the extension
identifications are discharged; the counts refer to the ambient classes. -/
public theorem secondCentralizerAlternative (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SelectedFusionData h) (t : G) (htE : t ∈ coreIntersection z a.g)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (hclasses : ∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x) :
    SecondCentralizerAlternative z t := by
  obtain ⟨s⟩ := nonempty_localSeed h hn d a t htE ht hnt hclasses
  exact secondCentralizerAlternative_of_markedModels h ht hnt hclasses
    (markedModels_of_localSeed h.involution ht hnt hclasses s)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve
