module

public import Theory.SpecificGroups.MacWilliams.HallJankoActionGeneration
public import Theory.SpecificGroups.MacWilliams.HallJankoBaseActionSelection
public import Theory.GroupTheory.PGroup.C4SquareElementaryReplacement
public import Theory.GroupAction.C4SquareActionDichotomy
public import Theory.GroupTheory.PGroup.C4SquareSplitInversion
public import Theory.GroupTheory.PGroup.NormalFourElementaryCentralizer

/-!
# Intrinsic setup for the Hall–Janko action construction

Choose an elementary sixteen containing the marked omega four before applying
the intersection and conjugation-image formulas. Its product with the abelian
base is the four-centralizer; its action has order four inside the full
conjugation image of order eight. The construction of the six particular
base actions is the remaining finite selection step. Selected automorphisms
are lifted and upgraded to a generating frame by `actionFrame_of_autActions`.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386,
citing MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup
namespace MacWilliamsSylow

/-- Select an elementary sixteen with the exact intersection, centralizer,
and conjugation-image orders needed to classify the Hall–Janko actions. -/
public theorem exists_elementary_action_setup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcard : Nat.card P = 128)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (W D : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D]
    (hW : Nat.card W = 4)
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) :
    ∃ B' : Subgroup P, IsElementaryAbelian 2 B' ∧ Nat.card B' = 16 ∧ W ≤ B' ∧
      B' ⊓ D = W ∧ centralizer (W : Set P) = B' ⊔ D ∧
      Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B'.subtype).range = 4 ∧
      Nat.card (MulAut.conjNormal : P →* MulAut D).range = 8 := by
  obtain ⟨B', hBe, hBc, hWB⟩ :=
    C4SquareExtension.exists_elementary_sixteen_containing_omega_four
      hP hcard hZ W D hW hO hmodel B hB
  let : IsElementaryAbelian 2 B' := hBe
  refine ⟨B', hBe, hBc, hWB,
    elementary_inf_eq_of_omega_one_eq_four W D B' hO hWB,
    C4SquareExtension.centralizer_eq_sup_of_card_eq_128
      hP hZ W D B' hW hBc hWB hO hmodel hcard,
    card_conj_image_four_of_elementary_sixteen W D B' hW hBc hDC hO hWB, ?_⟩
  rw [← index_ker, conjNormal_ker_eq_of_selfCentralizing_abelian D hDC]
  exact C4SquareExtension.index_eq_eight_of_card_eq_128 D hmodel hcard

/-- Selected automorphisms of the actual conjugation image give a generating
Hall–Janko action frame. Generation follows from the order-128 hypothesis. -/
public theorem actionFrame_of_autActions
    {P : Type*} [Group P] [Finite P] (hcard : Nat.card P = 128)
    (D W B : Subgroup P) [D.Normal] [IsMulCommutative D]
    [IsElementaryAbelian 2 B]
    (hW : Nat.card W = 4)
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model))
    (f : C4SquareExtension.HallJankoAutActions
      ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range
      (MulAut.conjNormal : P →* MulAut D).range) :
    Nonempty (HallJankoActionFrame D W B) := by
  obtain ⟨g⟩ := baseActions_of_autActions D W B hO f
  exact ⟨g.toFrame (g.generate hcard hW hDC hmodel)⟩

/-- The intrinsic order-128 hypotheses produce a Hall--Janko action frame.

The elementary replacement supplies the exact four-centralizer and image
orders.  The elementary-centralizer inversion lemma supplies the nonbinary
inversion condition needed by the finite action dichotomy.  Its split branch
is excluded by the normal-elementary-sixteen obstruction.
-/
public theorem exists_action_frame
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hcard : Nat.card P = 128)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W D : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D]
    (hW : Nat.card W = 4)
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) :
    ∃ B' : Subgroup P, IsElementaryAbelian 2 B' ∧ Nat.card B' = 16 ∧
      Nonempty (HallJankoActionFrame D W B') := by
  obtain ⟨B', hBe, hBc, hWB, hBD, hC, hH, hK⟩ :=
    exists_elementary_action_setup hP hcard hZ W D hW hDC hO hmodel B hB
  let : IsElementaryAbelian 2 B' := hBe
  let H := ((MulAut.conjNormal : P →* MulAut D).comp B'.subtype).range
  let K := (MulAut.conjNormal : P →* MulAut D).range
  have hHK : H ≤ K := by
    intro α hα
    rcases hα with ⟨b, rfl⟩
    exact ⟨b, rfl⟩
  have hfix : ∀ α ∈ K, α ∈ H ↔ ∀ a : D, a ^ 2 = 1 → α a = a := by
    intro α hα
    exact C4SquareExtension.mem_elementary_conj_image_iff_fix_square_one
      W D B' hDC hO hWB hC α hα
  have hinv : ∀ α ∈ H, α ≠ 1 →
      ∃ a : D, α a = a⁻¹ ∧ a ^ 2 ≠ 1 := by
    intro α hα hne
    obtain ⟨b, rfl⟩ := hα
    obtain ⟨a, ha, ha2⟩ :=
      IsPGroup.exists_inverted_nonbinary_of_mem_elementary_conj_image
        hno W D B' hW hO hWB hC _ ⟨b, rfl⟩ hne
    exact ⟨a, ha, ha2⟩
  rcases C4SquareExtension.action_dichotomy hmodel H K hHK hH hK hfix hinv with hf | hf
  · obtain ⟨f⟩ := hf
    exact ⟨B', hBe, hBc, actionFrame_of_autActions hcard D W B' hW hDC hO hmodel f⟩
  · obtain ⟨f⟩ := hf
    have hindex : (centralizer (W : Set P)).index = 2 :=
      centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
        hP hZ W hW
    obtain ⟨N, hNn, hNe, hNc⟩ :=
      C4SquareExtension.SplitInversionAutActions.exists_normal_elementary_sixteen
        W D B' hW hO hWB hC hindex f
    exact (hno ⟨N, hNn, hNe, by rw [hNc]; omega⟩).elim

end MacWilliamsSylow
