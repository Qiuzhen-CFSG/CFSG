module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.SolvableNineAction
public import Theory.GroupAction.ElementaryTwoTernaryLine

/-!
# Excluding elementary roots on a solvable nine-point panel

A solvable doubly transitive action of degree nine has a regular normal
ternary plane. Every elementary two-actor on that plane preserves a cubic
line. An actor fixing the panel base and transitive on its complement
would consequently put every translation in this line, contradicting the
orders three and nine. The same argument applies to the canonical simple
root through its literal action on the punctured panel, without (2B).

RegularUnitaryApplications combines this obstruction with odd Weyl
opposition and the original linear first factor. It excludes the affine
binary unitary exception on that global branch. No assertion about the
even Weyl branches or an arbitrary rank-two classification is made here.
Source: the solvable primitive argument in Fong--Seitz I (2A)--(2B),
and the elementary odd-opposition reduction for DGS, pp.80--81.
-/

public noncomputable section
open Subgroup MulAction
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel

/-- An elementary two-actor fixing one point cannot be transitive on the other
points of a solvable doubly transitive action of degree nine. -/
theorem no_elementary_two_punctured_transitivity
    {G Ω A : Type*} [Group G] [Finite G] [MulAction G Ω]
    [FaithfulSMul G Ω] [Finite Ω] [Group.IsSolvable G]
    [Group A] [IsElementaryAbelian 2 A]
    (ht : IsMultiplyPretransitive G Ω 2) (hc : Nat.card Ω = 9)
    (o : Ω) (f : A →* G) (hfix : ∀ a, f a • o = o)
    (htrans : ∀ x y : Ω, x ≠ o → y ≠ o → ∃ a : A, f a • x = y) : False := by
  obtain ⟨W,hWn,hWe,hWc,hreg⟩ := regular_nine_of_solvable ht hc o
  let := hWn
  let α : A →* MulAut W := (MulAut.conjNormal : G →* MulAut W).comp f
  obtain ⟨J,hJ,hstable⟩ := MulAut.exists_stable_three_of_elementary_two α hWc
  have hinj : Function.Injective (fun w : W => (w : G) • o) := by
    intro a b hab
    obtain ⟨c,hc,hu⟩ := hreg o ((a : G) • o)
    exact (hu a rfl).trans (hu b hab.symm).symm
  have hne (w : W) (hw : w ≠ 1) : (w : G) • o ≠ o := by
    intro he
    apply hw
    apply hinj
    simpa only [Subgroup.coe_one,one_smul] using he
  let : Nontrivial J := Finite.one_lt_card_iff_nontrivial.mp (by rw [hJ]; decide)
  obtain ⟨x,hx⟩ := exists_ne (1 : J)
  have hx' : (x : W) ≠ 1 := fun hh => hx (Subtype.ext hh)
  have htop : J = ⊤ := by
    apply top_unique
    intro y _
    by_cases hy : y = 1
    · simpa only [hy] using J.one_mem
    obtain ⟨a,ha⟩ := htrans (((x : W) : G) • o) ((y : G) • o) (hne _ hx') (hne _ hy)
    have hfi : (f a)⁻¹ • o = o := by
      have hh := congrArg (fun z : Ω => (f a)⁻¹ • z) (hfix a)
      simpa only [inv_smul_smul] using hh.symm
    have he : α a (x : W) = y := by
      apply hinj
      change (f a * ((x : W) : G) * (f a)⁻¹) • o = (y : G) • o
      rw [mul_smul,mul_smul,hfi]
      exact ha
    rw [←he]
    exact hstable a _ x.property
  have he := congrArg (fun H : Subgroup W => Nat.card H) htop
  rw [hJ,card_top,hWc] at he
  omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates UnitarySource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

/-- The simple root on a solvable nine-point panel is not elementary abelian. -/
theorem simpleRoot_not_elementary_of_solvable_nine
    (hs : Group.IsSolvable (localGroup Q split i))
    (hc : Nat.card (Panel Q i) = 9) : ¬ IsElementaryAbelian 2 (simpleRoot Q split i) := by
  intro he
  let := hs
  let := he
  let f : simpleRoot Q split i →* localGroup Q split i :=
    (localAction Q split i).rangeRestrict.comp
      (inclusion ((simpleRoot_le Q split i).trans (show split.U ≤ localClosure Q split i from le_sup_left)))
  have hf (r : simpleRoot Q split i) (a : Panel Q i) :
      f r • a = panelRoot Q split i r • a := by
    change localAction Q split i _ a = _
    rw [localAction_eq_panelAction]
    rfl
  apply BinaryPanel.no_elementary_two_punctured_transitivity
    (localGroup_two_pretransitive Q split i) hc (panelBase Q i) f
  · intro r
    rw [hf]
    exact panelRoot_fixes_base Q split i r
  · intro a b ha hb
    obtain ⟨r,hr,_⟩ := exists_unique_root_transport Q split i a b ha hb
    exact ⟨r,(hf r a).trans hr⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
