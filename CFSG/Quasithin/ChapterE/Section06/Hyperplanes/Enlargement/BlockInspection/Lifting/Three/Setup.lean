module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Contracts

/-!
# The actual common Sylow in the A₃ envelope

The envelope R = C_H(E(H))Q has F*(R) = O₂(R) when H = C_G(A)
and the odd core of H vanishes. The common Sylow supplied by E.6.5
restricts to R and to R ∩ C_G(U). The original short block restricts
to the latter centralizer with its genuine subnormal chain.

These results provide the setup for the independent layer-placement and
block-detection obligations; neither obligation is assumed here.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.5
and E.6.23, printed pp.245 and 254 (PDF pp.256 and 265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
open ComponentBalance Three

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- The actual envelope has characteristic two and the same Sylow Q as
C_G(A). No placement of the original A₃ block is used in this construction. -/
theorem three_envelope_setup
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h21 : OddCoreFree V) {A : Subgroup G} (hA : A ∈ obstructionFamily M V) :
    let Q := sylowCentralizer (T : Subgroup G) V
    let R := layerEnvelope (centralizer (A : Set G)) Q
    R ≤ centralizer (A : Set G) ∧ Chapter1.IsSylowIn 2 Q R ∧
      generalizedFitting R = pCore 2 R := by
  dsimp only
  have hS : Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
      (centralizer (A : Set G)) := h.sylow_obstruction hA
  have hQH := (Chapter1.isSylowIn_iff.mp hS).2.1
  have hRH := layerEnvelope_le hQH
  exact ⟨hRH, hS.restrict le_sup_right hRH,
    layerEnvelope_fitting hQH (T.isPGroup'.to_le inf_le_left) (h21 A hA.1 hA.2.1)⟩

/-- Restriction of the original block to any intermediate centralizer
preserves its actual short group and relative subnormality. -/
theorem three_block_restrict {U L R : Subgroup G} (hL : SmallBlock U L) (hLR : L ≤ R) :
    ChapterC.IsBlock (L.subgroupOf (R ⊓ centralizer (U : Set G))) := by
  have hLI := le_inf hLR hL.1
  refine ⟨inferInstance, ?_, hL.2.1.subnormal.comap (inclusion inf_le_right)⟩
  exact (hL.2.1.short.of_mulEquiv (subgroupOfEquivOfLe hL.1)).of_mulEquiv
    (subgroupOfEquivOfLe hLI).symm

/-- After layer placement, the original block and Q lie in the centralizer
inside the envelope. This is the concrete starting point for block detection. -/
theorem three_localized_setup
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {U A L : Subgroup G} (hU : U ∈ obstructionFamily M V)
    (hL : SmallBlock U L)
    (hLC : L ≤ layerKernel (centralizer (A : Set G))) :
    let Q := sylowCentralizer (T : Subgroup G) V
    let R := layerEnvelope (centralizer (A : Set G)) Q
    L ≤ R ⊓ centralizer (U : Set G) ∧
      ChapterC.IsBlock (L.subgroupOf (R ⊓ centralizer (U : Set G))) ∧
      Chapter1.IsSylowIn 2 Q (R ⊓ centralizer (U : Set G)) := by
  dsimp only
  have hLR := hLC.trans (le_sup_left (b := sylowCentralizer (T : Subgroup G) V))
  have hS : Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
      (centralizer (U : Set G)) := h.sylow_obstruction hU
  exact ⟨le_inf hLR hL.1, three_block_restrict hL hLR,
    hS.restrict (le_inf le_sup_right (Chapter1.isSylowIn_iff.mp hS).2.1) inf_le_right⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
