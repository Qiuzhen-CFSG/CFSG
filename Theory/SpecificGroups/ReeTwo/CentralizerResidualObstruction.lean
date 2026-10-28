module

public import Theory.SpecificGroups.ReeTwo.Centralizer
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# The root-five obstruction to centralizing the two-residual

An order-five complement element and all its conjugates lie in the two-residual.
The conjugate by root 3 does not commute with root 5, as a direct calculation
in the verified semidirect product shows. Hence root 5 cannot generate the
centralizer of the two-residual inside the two-core.

Aschbacher, *The Tits group as a standard subgroup*, Math. Z. 181 (1982),
(3.2.7), printed p.234, asserts a centralizer formula for the cyclic-five
complement X, not for O²(H). This distinction matters in the use of that
formula in Aschbacher--Smith, Lemma 14.2.21, printed p.989. Here we prove the
obstruction in the concrete local model; its transport to an independently
constructed ambient Ree group remains separate.
-/

namespace ReeTwo.Centralizer
private def fiveComplement : Core.complement :=
  ⟨Core.c, FiveFour.c, Core.complementAction_c⟩

private def fiveElement : Centralizer := SemidirectProduct.inr fiveComplement

private theorem fiveElement_order : orderOf fiveElement = 5 := by
  rw [fiveElement, orderOf_injective _ SemidirectProduct.inr_injective,
    ← Subgroup.orderOf_coe]
  exact Core.orderOf_c

private def conjugateFive : Centralizer := root 0 * fiveElement * (root 0)⁻¹

private theorem conjugateFive_order : orderOf conjugateFive = 5 := by
  change orderOf ((MulAut.conj (root 0)) fiveElement) = 5
  rw [MulEquiv.orderOf_eq, fiveElement_order]

private theorem root_five_not_commute_conjugateFive :
    root 2 * conjugateFive ≠ conjugateFive * root 2 := by
  intro h
  have he := congrArg (fun x : Centralizer => x.left) h
  simp only [root, conjugateFive, fiveElement, SemidirectProduct.mul_left,
    SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl,
    SemidirectProduct.left_inr, SemidirectProduct.right_inr,
    map_one, MulAut.one_apply, one_mul, mul_one, inv_one,
    fiveComplement] at he
  change Core.root 2 * (Core.root 0 * Core.c (Core.root 0)⁻¹) =
    (Core.root 0 * Core.c (Core.root 0)⁻¹) * Core.c (Core.root 2) at he
  exact (by decide +kernel : Core.root 2 * (Core.root 0 * Core.c (Core.root 0)⁻¹) ≠
    (Core.root 0 * Core.c (Core.root 0)⁻¹) * Core.c (Core.root 2)) he

/-- Source root v5 does not centralize the actual two-residual of the local model. -/
public theorem root_five_not_mem_centralizer_twoResidual :
    root 2 ∉ Subgroup.centralizer (pResidual 2 Centralizer : Set Centralizer) := by
  intro h
  have hm : conjugateFive ∈ pResidual 2 Centralizer :=
    Subgroup.mem_pResidual_of_orderOf_coprime (by rw [conjugateFive_order]; decide)
  exact root_five_not_commute_conjugateFive
    (Subgroup.mem_centralizer_iff.mp h conjugateFive hm).symm

end ReeTwo.Centralizer
