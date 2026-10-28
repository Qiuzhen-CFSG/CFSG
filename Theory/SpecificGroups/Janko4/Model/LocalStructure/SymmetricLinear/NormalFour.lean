module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Words
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Numerics
public import Theory.ElementaryAbelian.Basic

/-!
# No normal four-group in the literal J₄ max4 subgroup

The ATLAS max4 generators x,y satisfy (xy)^35 = 1. A normal subgroup of
order four centralizes xy and its conjugate yx, since 35 is coprime to 4!.
The checked cyclic-row and annihilator certificates detect any matrix in
this common commutant by two binary entries. Four distinct invertible matrices
would exhaust the four pairs of entries, forcing one matrix to be zero.

This proves the obstruction for the literal program-output closure, without
assuming its expected extension shape, any global order or simplicity result,
or a pair-placement assertion. The last theorem has exactly the `hf4` type
used by Chapter 15's `SporadicModels.JankoFour` conditional assembly.

Source: Aschbacher–Smith, 15.3.43, printed p.1140, and GLS3 Table 5.3i.
ATLAS source bytes and attribution are retained in `SymmetricLinear/Model`;
the reproducible certificate construction is in `NormalFour/source/`.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear

/-- The literal order-35 words have a common commutant detected by two entries. -/
theorem NormalFour.smallCommutant : NormalFour.SmallCommutant := by
  intro T hC hD h00 h01
  rw [NormalFour.Certificate.image_cycle] at hC
  rw [NormalFour.Certificate.image_reverseCycle] at hD
  exact NormalFour.zero_of_cyclic_annihilator 0 1
    NormalFour.Certificate.cMatrix NormalFour.Certificate.dMatrix
    (fun i => decodeRows (NormalFour.Certificate.wordRows.get i))
    NormalFour.Certificate.qMatrix NormalFour.Certificate.qiMatrix
    NormalFour.Certificate.rMatrix NormalFour.Certificate.pMatrix
    NormalFour.Certificate.uMatrix NormalFour.Certificate.kernelRow
    NormalFour.Certificate.cyclic_rows NormalFour.Certificate.cyclic_left_inverse
    NormalFour.Certificate.word_commutation
    (fun M hMC hMD => by
      rw [← NormalFour.Certificate.annihilator_polynomial]
      exact NormalFour.Certificate.polynomial_commutation M hMC hMD)
    NormalFour.Certificate.annihilator_zero_row
    NormalFour.Certificate.annihilator_projection
    NormalFour.Certificate.projection_matrix T hC hD h00 h01

/-- The actual max4 subgroup has no normal subgroup of order four. -/
theorem max4_normal_card_ne_four (W : Subgroup max4Subgroup) [W.Normal] :
    Nat.card W ≠ 4 :=
  NormalFour.normal_card_ne_four_of_certificate
    NormalFour.Certificate.cycle_pow NormalFour.smallCommutant W

/-- Unconditional input for `hf4` in the Chapter 15 J₄ rank-one obstruction. -/
theorem max4_no_normal_elementary_four (W : Subgroup max4Subgroup)
    (hn : W.Normal) (_he : IsElementaryAbelian 2 W) : Nat.card W ≠ 4 := by
  let : W.Normal := hn
  exact max4_normal_card_ne_four W

end Janko4.LocalStructure.SymmetricLinear
