module

public import Theory.SpecificGroups.MacWilliams.HallJankoActionConstruction
public import Theory.SpecificGroups.MacWilliams.HallJankoLiftNormalization
public import Theory.SpecificGroups.MacWilliams.HallJankoExtension
public import Theory.SpecificGroups.MacWilliams.HallJankoRecognition

/-!
# Intrinsic recognition of the order-128 C₄-square extension

A self-centralizing normal C₄-square, together with an elementary sixteen and
the exclusion of normal elementary eights, determines the Hall–Janko model
when the central omega subgroup has order two. Construct an action frame,
normalize its lifts, and use its generating presentation to obtain the
isomorphism. The elementary sixteen may be replaced during construction.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386,
citing MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace MacWilliamsSylow

open Subgroup

variable {P : Type*} [Group P] [Finite P]

/-- The intrinsic C₄-square hypotheses supply the exact Hall–Janko generating
relations, without assuming that the given elementary sixteen contains the four. -/
public theorem exists_hallJanko_generators_of_c4Square
    (hP : IsPGroup 2 P) (hcard : Nat.card P = 128)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W D : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D]
    (hW : Nat.card W = 4) (hWD : W ≤ D)
    (hDC : centralizer (D : Set P) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) :
    ∃ x : Fin 7 → P, Relations hallJankoTable x ∧ closure (Set.range x) = ⊤ := by
  obtain ⟨B', hBe, hBc, ⟨f⟩⟩ :=
    exists_action_frame hP hcard hZ hno W D hW hDC hDO hmodel B hB
  let : IsElementaryAbelian 2 B' := hBe
  obtain ⟨f', hf'⟩ := f.exists_normalized hcard hno hW hBc hWD hDC hDO hmodel
  exact f'.exists_generators hf'

/-- Recognition of the order-128 extension from its intrinsic subgroup data. -/
public theorem nonempty_hallJanko_equiv_of_c4Square
    (hP : IsPGroup 2 P) (hcard : Nat.card P = 128)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W D : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D]
    (hW : Nat.card W = 4) (hWD : W ≤ D)
    (hDC : centralizer (D : Set P) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) :
    Nonempty (P ≃* HallJankoSylow) := by
  obtain ⟨x, hx, hgen⟩ := exists_hallJanko_generators_of_c4Square
    hP hcard hZ hno W D hW hWD hDC hDO hmodel B hB
  exact nonempty_hallJanko_equiv_of_generators hcard.ge x hx hgen

end MacWilliamsSylow
