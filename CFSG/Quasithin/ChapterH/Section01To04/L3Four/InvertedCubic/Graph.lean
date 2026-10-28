module

public import Theory.SpecificGroups.PSL3Four.InvolutionNormalForms.Graph
public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.InvertedCubic.LinearField

/-!
# Cubic inversion in the pure graph coset

Every involutory linear-times-graph actor on the actual PSL₃(4) is conjugate
to inverse transpose. Transporting the marked symmetric binary cubic through
that automorphism gives an actual element of order three inverted by the actor.

This discharges the pure graph branch of the inverted-cubic assertion in
Aschbacher–Smith H.4.7, printed pp.382–383 of refs/quasithin.pdf. The ambient
assembly and the separate graph–field branch remain with their owners.
-/

public section
open Matrix Matrix.PSL3Four Matrix.PSL3.OuterSolvable
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four.InvertedCubic

/-- Every involutory actor in the pure graph coset inverts a cubic in PSL₃(4). -/
theorem linear_graph_inverts_cubic (m : GL (Fin 3) F)
    (hm : (linearConj F m * graph F)^2 = 1) :
    ∃ y : PSL, orderOf y = 3 ∧ (linearConj F m * graph F) y = y⁻¹ := by
  obtain ⟨d, hd⟩ := Matrix.PSL3Four.InvolutionNormalForms.graph_involution_conjugate m hm
  exact transport_inverted_cubic _ _ d hd graph_inverts_cubic

end CFSG.Quasithin.ChapterH.Section01To04.L3Four.InvertedCubic
