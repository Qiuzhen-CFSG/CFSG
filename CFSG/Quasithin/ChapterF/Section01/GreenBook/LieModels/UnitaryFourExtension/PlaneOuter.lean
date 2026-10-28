module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.BinaryOrders
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.FieldAction

/-!
# The outer field action on the unitary plane endpoint

The marked Frobenius automorphism induces the nontrivial field action on the
literal quotient of the plane local factor by its two-core. An inner action on
this quotient would preserve every SL₂ trace and hence fix every field element.
Thus the quotient action, and consequently the action on the local factor, is
outer. At q = 2 the local factor is the whole plane parabolic, giving the exact
ambient non-inner condition used to recognize its faithful doubled extension.

Source: Aschbacher--Smith, F.1.12, the plane quotient field action on printed
p.264; the binary extension in the normal A₅ branch of 13.1.7.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.Extension
variable (n : ℕ) (hn : 1 ≤ n)

/-- Frobenius is outer on the actual plane quotient by its two-core. -/
theorem L2QuotientAut_ne_inner (g : L2 n hn ⧸ pCore 2 (L2 n hn)) :
    L2QuotientAut n hn ≠ MulAut.conj g := by
  intro h
  have hf : Theory.PSL2.sl2FieldAut (fieldConj n) =
      MulAut.conj (L2QuotientEquivMatrixSL2 n hn g) := by
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := (L2QuotientEquivMatrixSL2 n hn).surjective x
    change Matrix.SpecialLinearGroup.map (fieldConj n).toRingHom
      (L2QuotientEquivMatrixSL2 n hn y) = _
    rw [← L2QuotientAut_field, h]
    simp only [MulAut.conj_apply, map_mul, map_inv]
  have hs := Theory.PSL2.sl2FieldAut_eq_conj_implies_refl (fieldConj n) _ hf
  obtain ⟨u, hu⟩ := PointLocal.fieldConj_nontrivial n hn
  exact hu (congrArg (fun f : MatrixField n ≃+* MatrixField n => f u) hs)

/-- Frobenius is outer on the actual projective plane local factor. -/
theorem L2Aut_ne_inner (g : L2 n hn) :
    L2Aut n hn ≠ MulAut.conj g := by
  intro h
  apply L2QuotientAut_ne_inner n hn (QuotientGroup.mk g)
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H a =>
    change QuotientGroup.mk (L2Aut n hn a) = _
    rw [h]
    simp only [MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

/-- On the whole binary plane parabolic, the ambient Frobenius action is not
conjugation by any element of that same parabolic. This is the literal endpoint
condition needed for the faithful extension comparison. -/
theorem binary_projectiveAut_not_plane_inner
    (g : planeParabolic 1 (Nat.le_refl 1)) :
    ¬ ∀ x : planeParabolic 1 (Nat.le_refl 1),
      projectiveAut 1 (Nat.le_refl 1) x.val = g.val * x.val * g.val⁻¹ := by
  intro h
  let g' : L2 1 (Nat.le_refl 1) := ⟨g.val, by
    rw [← BinaryCompletion.plane_eq_local]
    exact g.property⟩
  apply L2Aut_ne_inner 1 (Nat.le_refl 1) g'
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [L2Aut_val]
  exact h ⟨x.val, L2_le_planeParabolic 1 (Nat.le_refl 1) x.property⟩

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.Extension
