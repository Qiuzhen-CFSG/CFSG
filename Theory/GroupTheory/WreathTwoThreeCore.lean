module
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.ElementaryAbelian.Injective

/-!
# The three-core of the binary two-plane wreath actor

The previously constructed elementary subgroup of order nine is the two-residual.
It is therefore contained in the three-core. The quotient is a two-group, so
coprime disjointness forces the reverse inclusion. This identifies the actual
characteristic three-core, together with its elementary structure and order.

Source application: the four-block quotient in the symmetric-eight local models
of Aschbacher–Smith, Chapter E, Section 2.5; the wreath residual calculation is
Lemma 15.3.7, printed p.1122.
-/

open Subgroup
namespace Theory.GroupTheory.WreathTwoResidual
private instance : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Multiplicative.toAdd.injective
    ext i
    change (3 : ℕ) • x.toAdd i = 0
    exact (show ∀ a : ZMod 3, (3 : ℕ) • a = 0 by decide +kernel) _
private theorem residual_elementary : IsElementaryAbelian 3 (pResidual 2 Actor) := by
  obtain ⟨e⟩ := Theory.GroupTheory.WreathTwoResidual.residual_equiv_elementaryNine
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective
private theorem threeCore_eq_residual : pCore 3 Actor = pResidual 2 Actor := by
  have : IsElementaryAbelian 3 (pResidual 2 Actor) := residual_elementary
  apply le_antisymm
  · let f := QuotientGroup.mk' (pResidual 2 Actor)
    have hd : Disjoint ((pCore 3 Actor).map f) (⊤ : Subgroup (Actor ⧸ pResidual 2 Actor)) :=
      IsPGroup.disjoint_of_coprime (pCore_isPGroup.map f)
        ((isPGroup_quotient_pResidual (G := Actor) 2).to_subgroup ⊤) (by decide)
    have hz : (pCore 3 Actor).map f = ⊥ := by simpa using hd
    simpa only [f, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
  · exact le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 3 _⟩
public theorem threeCore_elementary :
    IsElementaryAbelian 3 (pCore 3 Theory.GroupTheory.WreathTwoResidual.Actor) := by
  rw [threeCore_eq_residual]
  exact residual_elementary
public theorem threeCore_card :
    Nat.card (pCore 3 Theory.GroupTheory.WreathTwoResidual.Actor) = 9 := by
  rw [threeCore_eq_residual]
  obtain ⟨e⟩ := Theory.GroupTheory.WreathTwoResidual.residual_equiv_elementaryNine
  rw [Nat.card_congr e.toEquiv]
  norm_num [Nat.card_eq_fintype_card]
public theorem threeCore_quotient_two :
    IsPGroup 2 (Theory.GroupTheory.WreathTwoResidual.Actor ⧸
      pCore 3 Theory.GroupTheory.WreathTwoResidual.Actor) := by
  exact (isPGroup_quotient_pResidual (G := Actor) 2).of_equiv
    (QuotientGroup.quotientMulEquivOfEq threeCore_eq_residual.symm)
end Theory.GroupTheory.WreathTwoResidual
