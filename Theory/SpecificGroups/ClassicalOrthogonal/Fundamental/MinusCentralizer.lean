module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Embedding
import Lean.Elab.Tactic.Omega

/-!
# Minus orthogonal fundamental subgroup and residual assembly

The proper fundamental SL₂ and the covering centralizer blocks are constructed
on `ClassicalGroup.POmegaMinus`, including over F₃. In ranks at least five,
two concrete cubic factors already give an elementary subgroup of order nine
in the literal projective block image. The exact common-scalar quotient is
identified with the nested residual as soon as its block-image equality is
proved.

The residual image equality, the complementary scalar-membership criterion,
and the cubic in the four-dimensional minus complement remain separate
structural obligations. The conditional quotient comparison below leaves its
image equality explicit; it is not an assertion of the completed A.2.17 branch.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.17,
printed p.39. The supplied maps match the orthogonal block consumer with
`n = r + 3` and complementary rank `n - 2 = r + 1`.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
variable {F : Type*} [Field F]

/-- Every source minus model has the proper injective marked fundamental SL₂. -/
theorem exists_proper_fundamental [Finite F] {p : ℕ} [CharP F p]
    (hp : p.Prime) (ho : Odd p) (n : ℕ) (hn : 4 ≤ n) :
    ∃ f : SpecialLinearGroup (Fin 2) F →* ClassicalGroup.POmegaMinus n F,
      Function.Injective f ∧ f.range ≠ ⊤ := by
  have hn' : n = (n - 3) + 3 := by omega
  rw [hn']
  exact ⟨fundamentalHom _ (field_card_gt_two hp ho),
    fundamentalHom_injective _ _, fundamentalHom_proper _ _⟩

/-- Above the smallest complement, the two concrete cubic factors survive in the
literal block image. Identifying this image with the residual is a separate step. -/
theorem higherBlock_contains_nine [Finite F] (r : ℕ) (hq : 2 < Nat.card F) :
    ∃ E : Subgroup (ClassicalGroup.POmegaMinus (r + 5) F),
      E ≤ (projectiveBlockHom (r + 2) hq).range ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨b, hb⟩ := higherMinus_exists_cubic r hq
  exact omegaProjective_contains_nine (Minus.quadraticForm F (r + 5))
    ⟨(0, (1, 0)), by simp [Minus.quadraticForm, Minus.plane_apply]⟩
    (coverBlockHom (r + 2) hq) (coverBlockHom_injective _ _) b hb

/-- An exact block-image equality identifies the scalar quotient with the literal
nested residual, retaining its actual centralizer inclusion. -/
def blockQuotientEquivResidual [Finite F] (p r : ℕ) (hq : 2 < Nat.card F)
    (hJ : (projectiveBlockHom r hq).range = centralizerResidualImage p r hq) :
    (SpecialLinearGroup (Fin 2) F ×
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) ⧸
      (projectiveBlockHom r hq).ker ≃* centralizerResidual p r hq :=
  ((blockQuotientEquivRange r hq).trans (MulEquiv.subgroupCongr hJ)).trans
    ((centralizerResidual p r hq).equivMapOfInjective _ Subtype.val_injective).symm


end ClassicalOrthogonal.Fundamental.MinusCentralizer
