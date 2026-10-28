module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.LineGeometry

/-!
# Literal large-center radical exclusion through the certified max4 eight

This consumer transports the native line/plane exclusion through an actual
ambient conjugator. It keeps the source radical, its center bound, maximality
of its whole normalizer, and the native-eight placement as literal hypotheses.
Thus it is usable once the independent h8/large-center placement producer is
available, without replacing that placement by an abstract group isomorphism.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals
open Janko4.LocalStructure.PureFirstNormalizers
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
attribute [local irreducible] Janko4.modelGroup matrixA matrixB

private theorem conjugate_plane_not_maximal
    (Y : Subgroup Model) [IsElementaryAbelian 2 Y]
    (g : Model) (hY : Y ≤ max4Eight.map (MulAut.conj g).toMonoidHom)
    (hcard : Nat.card Y = 4)
    (hmax : IsMaximalTwoLocal (normalizer (Y : Set Model))) : False := by
  let c := (MulAut.conj g).symm
  let Y' := Y.map c.toMonoidHom
  let : IsElementaryAbelian 2 Y' := IsElementaryAbelian.map c.toMonoidHom
  have hY' : Y' ≤ max4Eight := by
    change Y.map c.toMonoidHom ≤ max4Eight
    have hc : c.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id Model := by
      ext x
      exact (MulAut.conj g).symm_apply_apply x
    have hh : Y.map c.toMonoidHom ≤
        (max4Eight.map (MulAut.conj g).toMonoidHom).map c.toMonoidHom :=
      map_mono (f := c.toMonoidHom) hY
    have heq : (max4Eight.map (MulAut.conj g).toMonoidHom).map c.toMonoidHom =
        max4Eight := by
      rw [map_map, hc, map_id]
    exact hh.trans_eq heq
  have hcY : Nat.card Y' = 4 := by
    rw [card_map_of_injective c.injective]
    exact hcard
  have hmax' : IsMaximalTwoLocal (normalizer (Y' : Set Model)) := by
    simpa only [Y', map_equiv_normalizer_eq] using
      (Theory.Quasithin.isMaximalTwoLocal_map c hmax)
  exact contained_plane_not_maximal Y' hY' hcY hmax'

/-- A pure plane inside a large-center radical is incompatible with a maximal
whole-normalizer placed in a conjugate of the certified native max4 eight. -/
theorem large_center_pure_plane_not_native_eight
    (P Y : Subgroup Model) [IsElementaryAbelian 2 Y]
    (_hP : P.IsPRadical 2)
    (_hlarge : 64 ≤ Nat.card (center P))
    (hmax : IsMaximalTwoLocal (normalizer (P : Set Model)))
    (hYP : Y ≤ P) (hYcard : Nat.card Y = 4)
    (hnormal : normalizer (Y : Set Model) = normalizer (P : Set Model))
    (g : Model)
    (hplacement : normalizer (P : Set Model) ≤
      max4Eight.map (MulAut.conj g).toMonoidHom) : False := by
  have hYnormal : Y ≤ normalizer (P : Set Model) := hYP.trans P.le_normalizer
  have hY : Y ≤ max4Eight.map (MulAut.conj g).toMonoidHom :=
    hYnormal.trans hplacement
  have hmaxY : IsMaximalTwoLocal (normalizer (Y : Set Model)) := by
    rw [hnormal]
    exact hmax
  exact conjugate_plane_not_maximal Y g hY hYcard hmaxY

end Janko4.LocalStructure.LargeCenterRadicals
