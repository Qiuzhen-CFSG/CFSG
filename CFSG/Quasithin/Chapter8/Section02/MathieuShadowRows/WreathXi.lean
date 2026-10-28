module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeChiefQuotients
public import CFSG.Quasithin.Chapter1.Section03.Basic.MinimalParabolic
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import Theory.ElementaryAbelian.Injective

/-!
# The original wreath residual and its Xi action

The literal two-core quotient map identifies O²(H)/O₂(O²(H)) with
the elementary nine-group. The maximal-overgroup core is O₂(H), so the
minimal-parabolic invariant-subgroup dichotomy proves irreducibility for
the original Sylow action on its Frattini quotient. This constructs all
clauses of Xi without an assumed quotient-action intertwiner.

The actual application is `M22CodeXi`. Source: Aschbacher--Smith 1.3.1,
B.6.8 and 8.2.2(1), printed pp.508,113--114,715, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
variable {H : Type*} [Group H] [Finite H]

/-- The two-residual modulo its own two-core has the literal wreath base model. -/
def wreath_residual_core_equiv
    (e : (H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) :
    (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Multiplicative (Fin 2 → ZMod 3) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let r := (((pResidual 2 (H ⧸ pCore 2 H)).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr
      (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective))).trans
        WreathTwoResidual.residual_equiv_elementaryNine.some
  have hc : Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 9 := by
    rw [Nat.card_congr r.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hz : pCore 2 (pResidual 2 (H ⧸ pCore 2 H)) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rcases (pCore_isPGroup (p := 2) (G := pResidual 2 (H ⧸ pCore 2 H))).card_eq_or_dvd with h | h
    · exact h
    · have hd := h.trans (pCore 2 (pResidual 2 (H ⧸ pCore 2 H))).card_subgroup_dvd_card
      rw [hc] at hd
      norm_num at hd
  exact (q.pResidualCoreQuotientEquiv (QuotientGroup.mk'_surjective _) hk).trans
    (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans r)

/-- A literal minimal parabolic with wreath two-core quotient has the original
Sylow-irreducible elementary nine residual required by Xi. -/
theorem wreath_residual_mem_Xi
    (S : Sylow 2 H) (hp : ChapterB.IsMinimalParabolicOver S ⊤)
    (hH : (⊤ : Subgroup H) ∈ Chapter1.H H)
    (e : (H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) :
    pResidual 2 H ∈ Chapter1.Xi H (S : Subgroup H) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 H))
  have hk : f.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hcore := (wreath_parabolic_kernel S hp f hf).symm.trans hk
  let : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) := {
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (by decide +kernel) }
  let r := wreath_residual_core_equiv e
  let : IsElementaryAbelian 3 (Chapter1.XiQuotient (pResidual 2 H)) :=
    IsElementaryAbelian.of_injective r.toMonoidHom r.injective
  have hc : Nat.card (Chapter1.XiQuotient (pResidual 2 H)) = 3^2 := by
    rw [Nat.card_congr r.toEquiv]
    simp [Nat.card_eq_fintype_card]
  exact Chapter1.residual_mem_Xi_of_minimalParabolic_core_eq S hp hcore hH
    (by decide : Nat.Prime 3) (by decide : Odd 3) hc
end CFSG.Quasithin.Chapter8.MathieuShadowRows
