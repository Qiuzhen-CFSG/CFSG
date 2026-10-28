module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.Recognition
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.Comparison
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.ResidualLocal
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.Extension

/-!
# Second-centralizer recognition through the two-residual

The local geometry already proves that K ∩ L has odd index in K and that
J = O²(K) is not contained in L when K is not. Exact residual transfer gives
J ∩ L = X, where X = O²(C_L(t)) uses both literal inclusions into G. Its
supported A₄ model supplies the four-group centralizer and involution fusion
needed to recognize J as A₅. Extending this recognition while agreeing with
the standard embedding of the local A₈ identifies K with C_A₉((01)(23))
and preserves the distinguished involution and both ambient classes.

`secondCentralizerData_of_source` discharges all residual and extension
premises from the original source inputs and the supplied `InvolutionData`.
The order-formula application retains only the independent `ModelCounts`
premise. Construction of the marking and the final index alternative belong
to the parent `Index` module, which is not imported here. The earlier
conditional assembly interfaces are preserved below.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38; Aschbacher–Smith I.4.6, printed p.417.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G} {L : Subgroup G}

/-- Recognize the residual, extend its model, and discharge the global fusion
fields, with the two intermediate producers explicit. -/
public theorem secondCentralizerData_of_residual_steps (d : InvolutionData z L)
    (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) (hK : ¬ d.K ≤ L)
    (r : ResidualFacts d)
    (extend : (d.J ≃* alternatingGroup (Fin 5)) → Nonempty (CentralizerExtension d)) :
    Nonempty (SecondCentralizerData d) := by
  obtain ⟨eJ⟩ := residual_equiv_alternating_five d hz hCL hK r
  obtain ⟨c⟩ := extend eJ
  exact ⟨c.secondCentralizerData hz hCL⟩

/-- Consumer application with all remaining source obligations and the actual
model counts explicit. No ambient order or index is assumed. -/
public theorem card_of_residual_steps (h : Hypotheses z)
    (local_intersections : ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g)
    (d : InvolutionData z L) (hCL : Centralizer z ≤ L) (hK : ¬ d.K ≤ L)
    (r : ResidualFacts d)
    (extend : (d.J ≃* alternatingGroup (Fin 5)) → Nonempty (CentralizerExtension d))
    (counts : ModelCounts) : Nat.card G = 181440 := by
  obtain ⟨c⟩ := secondCentralizerData_of_residual_steps d h.involution hCL hK r extend
  exact card_of_centralizer_comparison h d (odd_index h local_intersections L hCL) hCL c counts

/-- The second-centralizer comparison from the source inputs and the marked A₈
subgroup. Transfer, A₅ recognition, the literal extension and both ambient
fusion fields are all proved; no ambient order, simplicity or index is assumed. -/
public theorem secondCentralizerData_of_source (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z)
    (local_intersections : ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g)
    (h13 : Nat.card (CoreFusion z) = 13)
    (L : Subgroup G) (hCL : Centralizer z ≤ L) (d : InvolutionData z L)
    (hK : ¬ d.K ≤ L) : Nonempty (SecondCentralizerData d) := by
  let r := residualFacts_of_source h hn local_intersections h13 L hCL d hK
  exact secondCentralizerData_of_residual_steps d h.involution hCL hK r
    (Extension.centralizerExtension_of_residual d h.involution hCL r.intersection)

/-- Apply the completed second-centralizer recognition to Thompson's order
formula. The independent finite model counts remain explicit. -/
public theorem card_of_secondCentralizer_source (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z)
    (local_intersections : ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g)
    (h13 : Nat.card (CoreFusion z) = 13)
    (L : Subgroup G) (hCL : Centralizer z ≤ L) (d : InvolutionData z L)
    (hK : ¬ d.K ≤ L) (counts : ModelCounts) : Nat.card G = 181440 := by
  obtain ⟨c⟩ := secondCentralizerData_of_source h hn local_intersections h13 L hCL d hK
  exact card_of_centralizer_comparison h d (odd_index h local_intersections L hCL) hCL c counts

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
