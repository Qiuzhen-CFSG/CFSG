module
public import Theory.SpecificGroups.AlternatingSeven.DoubleCentralizer
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Alternating.Seven

/-!
# The marked fixed subgroup on an A₇ central quotient

The original Sylow-fixing involution maps its full fixed subgroup onto the
fixed subgroup in the specified A₇ quotient. A pointwise fixer therefore
descends to the seven-point double centralizer, and perfectness lifts the
result back to the original component. The quotient and involution remain
the given ones throughout.

Source: Aschbacher–Smith 1.1.5(3d) and 12.4.8, printed pp.502–503,816.
-/

public section
open Subgroup Equiv Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.OddCore
open Chapter1.QuasisimpleInvolutions
variable {X : Type*} [Group X] [Finite X] [IsQuasisimple X]

/-- On a perfect cover of A₇, a pointwise fixer of the marked fixed group
is either trivial or the marked involution itself. -/
theorem marked_seven_fixed_fixer {α : MulAut X} {P : Sylow 2 X}
    (d : MarkedInvolution α P) (e : X ⧸ center X ≃* alternatingGroup (Fin 7))
    (β : MulAut X) (hβ : ∀ x ∈ α.fixedSubgroup, β x = x) :
    β = 1 ∨ β = α := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  let a := MulAut.centralQuotientAction e α
  let b := MulAut.centralQuotientAction e β
  have heq (x : X) : q (α x) = a (q x) :=
    (MulAut.centralQuotientAction_apply e α x).symm
  have hk : q.ker ≤ center X := by
    intro x hx
    change e (QuotientGroup.mk' (center X) x) = 1 at hx
    have hh : QuotientGroup.mk' (center X) x = 1 := e.injective (hx.trans e.map_one.symm)
    exact (QuotientGroup.eq_one_iff x).mp hh
  have hs := MulAut.fixedSubgroupMap_surjective_of_sylow_fixed α a q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hk heq
    (d.order_two ▸ pow_orderOf_eq_one α) P d.fixes
  have hb : ∀ y ∈ a.fixedSubgroup, b y = y := by
    intro y hy
    obtain ⟨x,hx⟩ := hs ⟨y,hy⟩
    have hxq : q x = y := congrArg Subtype.val hx
    rw [← hxq]
    change MulAut.centralQuotientAction e β (e (QuotientGroup.mk' (center X) x)) = _
    rw [MulAut.centralQuotientAction_apply, hβ x x.property]
    rfl
  obtain ⟨ho,hc,_⟩ := d.centralQuotient_model_inputs e
  obtain ⟨σ,hσ,hα⟩ := Alternating.seven_fixed_action a ho hc
  have hb' := AlternatingSeven.DoubleCentralizer.fixed_automorphism σ hσ b (hα ▸ hb)
  have hi := MulAut.centralQuotientAction_injective e
  rcases hb' with hh | hh
  · exact Or.inl (hi (hh.trans (map_one _).symm))
  · exact Or.inr (hi (hh.trans hα.symm))
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.OddCore
