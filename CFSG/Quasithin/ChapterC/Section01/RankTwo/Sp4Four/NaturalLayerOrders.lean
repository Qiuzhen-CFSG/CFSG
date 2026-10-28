module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# The field order in the initial Sp₄(4) module layer

The B.4.2 list identifies its acting component with a concrete classical group.
A component of order 979200 cannot be SL₂(q), SL₃(q), or G₂(q): monotonicity
places that number strictly between consecutive values of each order formula.
For Sp₄(q), the same comparison forces q = 4 and binary field degree two.
These order tests feed the initial natural-layer recognition in the rank-two
MS argument, retaining the actual action supplied by B.4.2.

Source: Aschbacher--Smith, B.4.2, printed p.86, and C.1.31--32,
printed pp.135--136; the classical order formulas are proved in the imports.
-/

public section
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

private theorem triple_mono (a b c : ℕ) {q r : ℕ} (h : q ≤ r) :
    q ^ a * (q ^ b - 1) * (q ^ c - 1) ≤
      r ^ a * (r ^ b - 1) * (r ^ c - 1) := by
  gcongr

private theorem linear_two_mono {q r : ℕ} (h : q ≤ r) :
    q * (q ^ 2 - 1) ≤ r * (r ^ 2 - 1) := by
  gcongr

/-- The SL₂ row cannot have the order of Sp₄(4). -/
theorem card_sl_two_ne_sp4_four (F : Type*) [Field F] [Finite F] :
    Nat.card SL(2,F) ≠ 979200 := by
  rw [Atlas.card_sl_two]
  intro hc
  by_cases hq : Nat.card F ≤ 99
  · have hb := linear_two_mono hq
    norm_num at hb
    omega
  · have hb := linear_two_mono (show 100 ≤ Nat.card F by omega)
    norm_num at hb
    omega

private theorem card_sl_three (F : Type*) [Field F] [Finite F] :
    Nat.card SL(3,F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(3,F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Matrix.PSL3.LinearThree.card_projective_mul_scalar F

/-- The SL₃ row cannot have the order of Sp₄(4). -/
theorem card_sl_three_ne_sp4_four (F : Type*) [Field F] [Finite F] :
    Nat.card SL(3,F) ≠ 979200 := by
  rw [card_sl_three]
  intro hc
  by_cases hq : Nat.card F ≤ 5
  · have hb := triple_mono 3 3 2 hq
    norm_num at hb
    omega
  · have hb := triple_mono 3 3 2 (show 6 ≤ Nat.card F by omega)
    norm_num at hb
    omega

/-- The full G₂ row cannot have the order of Sp₄(4). -/
theorem card_g2_ne_sp4_four (F : Type*) [Field F] [Finite F] :
    Nat.card (Atlas.G2.Model F) ≠ 979200 := by
  rw [Atlas.G2.card_Model]
  intro hc
  by_cases hq : Nat.card F ≤ 2
  · have hb := triple_mono 6 6 2 hq
    norm_num at hb
    omega
  · have hb := triple_mono 6 6 2 (show 3 ≤ Nat.card F by omega)
    norm_num at hb
    omega

/-- The order of the actual symplectic matrix group determines its field size. -/
theorem card_eq_four_of_card_sp (F : Type*) [Field F] [Finite F]
    (hc : Nat.card (Matrix.symplecticGroup (Fin 2) F) = 979200) :
    Nat.card F = 4 := by
  rw [Theory.SpecificGroups.SymplecticFour.card_sp] at hc
  have hlo : 4 ≤ Nat.card F := by
    by_contra hq
    have hb := triple_mono 4 2 4 (show Nat.card F ≤ 3 by omega)
    norm_num at hb
    omega
  have hhi : Nat.card F ≤ 4 := by
    by_contra hq
    have hb := triple_mono 4 2 4 (show 5 ≤ Nat.card F by omega)
    norm_num at hb
    omega
  omega

/-- The binary field in the surviving symplectic row has degree two. -/
theorem degree_eq_two_of_card_sp (F : ChapterB.QuasisimpleSource.BinaryField)
    (hc : Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier) = 979200) :
    F.degree = 2 := by
  apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
  change 2 ^ F.degree = 2 ^ 2
  rw [← F.card_eq, card_eq_four_of_card_sp F.Carrier hc]

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
