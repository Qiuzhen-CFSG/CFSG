module
public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.Source
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.InvertedCubic.LinearField

/-!
# The ambient inverted-cubic reduction for H.4.7

Conjugation on the genuine generalized Fitting subgroup is faithful: its
centralizer lies in that subgroup, whose center is trivial because it is the
actual quotient PSL₃(4). Transport through the supplied equivalence therefore
preserves the order of the ambient involution. The intrinsic cubic witnesses
then transport back to literal conjugation in the original group.

The final theorem in this module is conditional on the two remaining graph
and graph–field matrix normal forms. The arbitrary-automorphism coverage,
nontriviality of the action, and inner and field branches are discharged.

Source: Aschbacher–Smith H.4.7, refs/quasithin.pdf, printed pp.382–383.
-/

public section
noncomputable section
open Matrix Matrix.PSL3Four Subgroup Theory.GroupTheory
open Matrix.PSL3.OuterSolvable
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four.InvertedCubic
variable {M : Type*} [Group M] [Finite M]

/-- Conjugation on the genuine generalized Fitting subgroup, transported
along the supplied PSL₃(4) equivalence. -/
def componentAction (e : PSL ≃* generalizedFitting M) : M →* MulAut PSL :=
  (MulAut.congr e.symm).toMonoidHom.comp MulAut.conjNormal

theorem componentAction_apply (e : PSL ≃* generalizedFitting M) (t : M) (y : PSL) :
    (e (componentAction e t y) : M) = t * (e y : M) * t⁻¹ := by
  change (e (e.symm ((MulAut.conjNormal t) (e y))) : M) = _
  rw [e.apply_symm_apply]
  exact MulAut.conjNormal_apply t (e y)

/-- Self-centralization and the trivial center of PSL₃(4) make the actual
ambient action faithful; this requires no representation hypothesis. -/
theorem componentAction_injective (e : PSL ≃* generalizedFitting M) :
    Function.Injective (componentAction e) := by
  apply (MulAut.congr e.symm).injective.comp
  apply MulAut.conjNormal_injective_of_centralizer_eq_bot
  apply le_bot_iff.mp
  intro x hx
  have hxL : x ∈ generalizedFitting M :=
    ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le hx
  have hz : (⟨x, hxL⟩ : generalizedFitting M) ∈ center (generalizedFitting M) := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext ((mem_centralizer_iff.mp hx) y y.property)
  have hz' := (Subgroup.centerCongr e).symm ⟨⟨x, hxL⟩, hz⟩ |>.property
  change e.symm ⟨x, hxL⟩ ∈ center PSL at hz'
  let : Group.IsPerfect SL := Atlas.sl_perfect 3 (by decide)
  rw [Group.IsPerfect.center_quotient_center_eq_bot SL] at hz'
  have he : e.symm ⟨x, hxL⟩ = 1 := hz'
  have h := congrArg (fun y : PSL => (e y : M)) he
  simpa using h

/-- The induced automorphism has precisely the order of the ambient actor. -/
theorem componentAction_orderOf (e : PSL ≃* generalizedFitting M) (t : M) :
    orderOf (componentAction e t) = orderOf t :=
  orderOf_injective (componentAction e) (componentAction_injective e) t

/-- An ambient involution induces a nonidentity involution of PSL₃(4). -/
theorem componentAction_involution (e : PSL ≃* generalizedFitting M)
    (t : M) (ht : orderOf t = 2) :
    componentAction e t ≠ 1 ∧ componentAction e t ^ 2 = 1 := by
  have h := (componentAction_orderOf e t).trans ht
  have hp := orderOf_eq_prime_iff.mp h
  exact ⟨hp.2, hp.1⟩

/-- The H.4.7 group-theoretic witness, conditional only on the two outstanding
matrix normal forms. This retains the literal ambient conjugation and the
genuine generalized Fitting subgroup. -/
theorem exists_inverted_cubic_of_graph_conjugacy
    (hgraph : ∀ m : GL (Fin 3) F, (linearConj F m * graph F) ^ 2 = 1 →
      ∃ d : MulAut PSL, MulAut.congr d (linearConj F m * graph F) = graph F)
    (hgraphField : ∀ m : GL (Fin 3) F,
      (linearConj F m * pslFrobenius * graph F) ^ 2 = 1 →
      ∃ d : MulAut PSL, MulAut.congr d (linearConj F m * pslFrobenius * graph F) =
        pslFrobenius * graph F)
    (e : PSL ≃* generalizedFitting M) (t : M) (ht : orderOf t = 2) :
    ∃ y : generalizedFitting M, orderOf y = 3 ∧
      t * (y : M) * t⁻¹ = (y : M)⁻¹ := by
  obtain ⟨hne, hsq⟩ := componentAction_involution e t ht
  obtain ⟨y, hy, hty⟩ := involution_inverts_cubic_of_graph_conjugacy
    hgraph hgraphField (componentAction e t) hne hsq
  refine ⟨e y, (e.orderOf_eq y).trans hy, ?_⟩
  rw [← componentAction_apply, hty, map_inv]
  rfl

end CFSG.Quasithin.ChapterH.Section01To04.L3Four.InvertedCubic
