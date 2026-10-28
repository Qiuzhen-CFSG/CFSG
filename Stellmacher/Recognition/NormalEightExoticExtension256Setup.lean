module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.C4SquareSelfCentralizing
public import Theory.GroupTheory.PGroup.C4SquareBasis
public import Theory.GroupTheory.PGroup.NormalFourAbelianBase
public import Theory.SpecificGroups.ExoticTwoGroup.ExtensionFrame

/-!
# The order-256 extension: base and faithful action reduction

For the supplied self-centralizing C₄-square base, conjugation has image
of order sixteen. Its restriction to the centralizer of the normal four
has image of order eight, while an elementary sixteen has image of order
four. The omega four can be identified with the two basis squares using
`C4SquareExtension.exists_basis`.

The remaining recognition obligations are existence of an `ActionFrame`
and a choice of lifts satisfying `ActionFrame.LiftRelations`. Neither
existence is asserted by the cardinal computations here. These are the
finite-action and extension steps in Janko–Thompson, Math. Z. 113 (1970),
1.4(c), printed p.386, used on p.395.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightExoticExtension256

/-- The action of an order-256 group on a self-centralizing C₄-square
has order sixteen. -/
public theorem card_conjugation_range
    {P : Type*} [Group P] [Finite P] (D : Subgroup P)
    [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model))
    (hcard : Nat.card P = 256) :
    Nat.card (MulAut.conjNormal : P →* MulAut D).range = 16 := by
  obtain ⟨e⟩ := hmodel
  have hD : Nat.card D = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hc := D.card_mul_index
  rw [hD, hcard] at hc
  rw [← index_ker, conjNormal_ker_eq_of_selfCentralizing_abelian D hDC]
  omega

/-- The centralizer of the normal four contributes an order-eight subgroup
of the faithful action; the supplied elementary sixteen contributes order four. -/
public theorem restricted_conjugation_cardinals
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W D B : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hW : Nat.card W = 4) (hB : Nat.card B = 16)
    (hWD : W ≤ D) (hWB : W ≤ B)
    (hDC : centralizer (D : Set S) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model))
    (hcard : Nat.card S = 256) :
    Nat.card ((MulAut.conjNormal : S →* MulAut D).comp
      (centralizer (W : Set S)).subtype).range = 8 ∧
    Nat.card ((MulAut.conjNormal : S →* MulAut D).comp B.subtype).range = 4 := by
  refine ⟨?_, card_conj_image_four_of_elementary_sixteen W D B hW hB hDC hDO hWB⟩
  let C := centralizer (W : Set S)
  let f := (MulAut.conjNormal : S →* MulAut D).comp C.subtype
  have hDCW : D ≤ C := fun d hd w hw => D.le_centralizer hd w (hWD hw)
  have hk : f.ker.map C.subtype = D := by
    change ((MulAut.conjNormal : S →* MulAut D).ker.comap C.subtype).map C.subtype = D
    rw [conjNormal_ker_eq_of_selfCentralizing_abelian D hDC,
      map_comap_eq, range_subtype, inf_eq_right.mpr hDCW]
  have hD : Nat.card D = 16 := by
    obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hkc : Nat.card f.ker = 16 := by
    have hh := congrArg (fun H : Subgroup S => Nat.card H) hk
    simpa only [card_map_of_injective C.subtype_injective, hD] using hh
  have hCi : C.index = 2 := NormalFourCentralOmegaTwo.centralizer_index_two S hZ W hW
  have hCc : Nat.card C = 128 := by
    have hh := C.card_mul_index
    rw [hCi, hcard] at hh
    omega
  have hf := f.ker.card_mul_index
  rw [index_ker, hkc, hCc] at hf
  change Nat.card f.range = 8
  omega

end Stellmacher.Recognition.NormalEightExoticExtension256
