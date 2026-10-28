module

public import Theory.SpecificGroups.MacWilliams.HallJankoLiftAlgebra
public import Theory.SpecificGroups.MacWilliams.HallJankoLiftFourControl
public import Theory.SpecificGroups.MacWilliams.HallJankoLiftParameters

/-!
# Normalization of Hall–Janko extension parameters

The algebraic normalization reduces to two structural facts: the elementary
sixteen contains the marked four, and the `tu` defect is outside that four.
Associativity supplies the extension parameters. The exclusion of normal
elementary eights forces their odd branch, for which explicit changes of lifts
give the required relations. The final theorem assembles these facts for an
arbitrary supplied frame, without depending on its construction.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386,
and MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace MacWilliamsSylow.HallJankoActionFrame

/-- Structural control of the marked four discharges the parity condition in
algebraic lift normalization. -/
public theorem exists_normalized_of_parameters
    {P : Type*} [Group P] {D W B : Subgroup P}
    (f : HallJankoActionFrame D W B) (p : f.LiftParameters)
    (hWB : W ≤ B) (hn : f.t * f.u * (f.u * f.t)⁻¹ ∉ W) :
    ∃ f' : HallJankoActionFrame D W B, f'.LiftRelations :=
  f.normalize_of_parameters hWB p (f.j_odd_of_defect_not_mem p hn)

/-- An action frame over a self-centralizing C₄-square can be normalized to
satisfy all three remaining Hall–Janko lift equations. The normal-elementary-eight
exclusion suffices; no additional assumption on the center or uniqueness of the
marked four is needed. -/
public theorem exists_normalized
    {P : Type*} [Group P] [Finite P] {D W B : Subgroup P}
    [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (f : HallJankoActionFrame D W B) (hcard : Nat.card P = 128)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hW : Nat.card W = 4) (hB : Nat.card B = 16)
    (hWD : W ≤ D) (hDC : Subgroup.centralizer (D : Set P) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))) :
    ∃ f' : HallJankoActionFrame D W B, f'.LiftRelations := by
  obtain ⟨hWB, hn⟩ :=
    f.four_le_and_tu_defect_not_mem hcard hno hW hB hWD hDC hDO hmodel
  obtain ⟨p⟩ := f.nonempty_liftParameters hDC hmodel
  exact f.exists_normalized_of_parameters p hWB hn

end MacWilliamsSylow.HallJankoActionFrame
