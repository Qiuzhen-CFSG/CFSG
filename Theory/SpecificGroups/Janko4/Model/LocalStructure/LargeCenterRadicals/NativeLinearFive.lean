module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.LinearFiveLocal
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.RowExclusions
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Recognition

/-!
# The recognized native linear-five radical row

The native normalizer recognition supplies the full intrinsic quotient used
by the residual exclusions. Conjugation transports that same quotient and
the radical equation. This completes the actual F row, with no quotient or
action premise; it does not classify the other radicals inside N(F).

Source: Kleidman--Wilson (1988), Lemma 1.1.1, and An--O'Brien--Wilson
(2003), Table 1, p.124, the elementary order-1024 row.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals.LinearFiveLocal
attribute [local irreducible] modelGroup matrixA matrixB

/-- The full intrinsic quotient of every actual conjugate of N(F). -/
def recognizedConjugateQuotientEquiv (g : Model) :
    let M := LinearFive.fullNormalizer.map (MulAut.conj g).toMonoidHom
    M ⧸ pCore 2 M ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  nativeConjugateQuotientEquiv LinearFive.intrinsicNormalizerQuotient g

/-- The actual F row has the required large center. -/
theorem native_F_center_card : Nat.card (center LinearFive.F) = 1024 := by
  let := LinearFive.F_elementary
  rw [center_eq_top, card_top, LinearFive.F_card]

/-- The full normalizer quotient of every conjugate radical F. -/
def conjugateFNormalizerQuotientEquiv (g : Model) :
    let N := normalizer (LinearFive.F.map (MulAut.conj g).toMonoidHom : Set Model)
    N ⧸ pCore 2 N ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  (MathieuRows.conjugateNormalizerQuotientEquiv LinearFive.F g).trans
    LinearFive.intrinsicNormalizerQuotient

/-- Native recognition discharges the quotient premise in the maximal-local exit. -/
theorem maximal_local_not_le_recognized_conjugate
    (N : Subgroup Model) (hN : IsMaximalTwoLocal N)
    (hq : ¬ Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))
    (g : Model) :
    ¬ N ≤ LinearFive.fullNormalizer.map (MulAut.conj g).toMonoidHom :=
  maximal_local_not_le_native_conjugate N hN hq LinearFive.intrinsicNormalizerQuotient g

/-- The source quotient obstruction removes the actual F row and every conjugate. -/
theorem not_native_F_of_quotients_excluded (P : Subgroup Model)
    (h : let N := normalizer (P : Set Model)
      ¬ (Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
         Nonempty ((N ⧸ pCore 2 N) ≃* Sporadic.Mathieu.M24) ∨
         Nonempty ((N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 8)))) :
    ∀ g : Model, P ≠ LinearFive.F.map (MulAut.conj g).toMonoidHom := by
  intro g he
  subst P
  exact h (Or.inl ⟨conjugateFNormalizerQuotientEquiv g⟩)

end Janko4.LocalStructure.LargeCenterRadicals.LinearFiveLocal
