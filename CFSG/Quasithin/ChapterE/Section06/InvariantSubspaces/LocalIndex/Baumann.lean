module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.Reduction

/-!
# Assembly of the local single-block Baumann calculation

The normal-block centralizer theorem identifies C_H(U) with O₂(H). The
natural rank-one calculation puts Q = O₂(LS) in S. In the alternating-five
case, the alpha decomposition from Baumann's Argument gives the same bound.
The reductions then prove all three fields required by the local index
argument.

This assembly is conditional on the three explicitly named earlier inputs.
It does not yet prove `BaumannInput`: those inputs must be constructed from
the actual block models. No SQTK hypothesis on the ambient group or on A ⊔ H
is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4,
printed p.155; C.1.11, p.124; B.6.10, p.117; B.2.18, pp.80–81.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex

universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- Conditional C.5.4 assembly for one normal chi-zero block. The two
model calculations use the same independently supplied C.1.11 identity. -/
theorem baumannInput_of_local_calculations
    (hc : Baumann.SingleBlockCentralizerInput (G := G))
    (hr : Baumann.RankOneCoreInput (G := G) K)
    (ha : Baumann.AlternatingFiveAlphaInput (G := G) K) :
    BaumannInput (G := G) K := by
  intro A H R L h
  have hcentralizer := hc H R L h.characteristicTwo h.sylow h.normalizes_L
    h.join_eq h.block
  apply Baumann.structure_of_core_bound h hcentralizer
  rcases h.block with hL | hL | hL
  · exact hr A H R L h hcentralizer (Or.inl hL)
  · exact hr A H R L h hcentralizer (Or.inr hL)
  · exact Baumann.localCore_le_baumann_of_alpha h hcentralizer
      (ha A H R L h hcentralizer hL)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex

end
