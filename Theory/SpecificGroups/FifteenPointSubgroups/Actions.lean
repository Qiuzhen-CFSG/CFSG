module

public import Theory.SpecificGroups.FifteenPointSubgroups.AlternatingSeven
public import Theory.SpecificGroups.FifteenPointSubgroups.LinearFour

/-!
# Odd-index subgroups and fifteen-point coset actions

In PSL₄(2) or A₇, an odd-index subgroup H with intrinsic quotient
H/O₂(H) isomorphic to PSL₃(2) has index fifteen and a two-transitive
left-coset action. The order calculation gives core order eight in PSL₄(2),
where endpoint-parabolic recognition supplies the action. In A₇ the core
is trivial, so the actual PSL₃(2) subgroup action applies.

All statements retain an arbitrary ambient group with an actual model
isomorphism. The subgroup, its intrinsic core and its left cosets are
transported through that isomorphism, with no extra action hypotheses.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.4.12(2), printed p.97 / PDF p.108 of `refs/quasithin.pdf`.
The imported ATLAS comparisons retain their attribution and license.
-/

public section
open scoped MatrixGroups

namespace FifteenPointSubgroups
variable {G : Type*} [Group G] [Finite G]

/-- The PSL₄(2) branch under precisely the odd-index and core-quotient hypotheses. -/
theorem psl4_coset_action (e : G ≃* PSL(4, ZMod 2)) (H : Subgroup G)
    (hodd : Odd H.index)
    (hquot : Nonempty ((H ⧸ pCore 2 H) ≃* PSL(3, ZMod 2))) :
    MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 ∧ H.index = 15 := by
  obtain ⟨hi, hc, _⟩ := psl4_orders e H hodd hquot
  refine ⟨Subgroup.two_pretransitive_of_map e H ?_, hi⟩
  apply psl4_two_pretransitive
  · rw [Subgroup.index_map_of_bijective e.bijective]
    exact hi
  · let f : H ≃* H.map e.toMonoidHom := e.subgroupMap H
    have hf : (pCore 2 H).map f.toMonoidHom = pCore 2 (H.map e.toMonoidHom) :=
      pCore_map_iso 2 f
    rw [← hf, Subgroup.card_map_of_injective f.injective]
    exact hc

/-- The A₇ branch uses the subgroup isomorphism obtained from the trivial core. -/
theorem alternating7_coset_action (e : G ≃* alternatingGroup (Fin 7)) (H : Subgroup G)
    (hodd : Odd H.index)
    (hquot : Nonempty ((H ⧸ pCore 2 H) ≃* PSL(3, ZMod 2))) :
    MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 ∧ H.index = 15 := by
  obtain ⟨f⟩ := alternating7_equiv e H hodd hquot
  refine ⟨Subgroup.two_pretransitive_of_map e H ?_,
    (alternating7_orders e H hodd hquot).1⟩
  exact alternating7_two_pretransitive _ ⟨(e.subgroupMap H).symm.trans f⟩

/-- The complete subgroup-action input for B.4.12(2), on literal left cosets. -/
theorem coset_action (H : Subgroup G)
    (hmodel : Nonempty (G ≃* PSL(4, ZMod 2)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 7)))
    (hodd : Odd H.index)
    (hquot : Nonempty ((H ⧸ pCore 2 H) ≃* PSL(3, ZMod 2))) :
    MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 ∧ H.index = 15 := by
  rcases hmodel with hmodel | hmodel
  · obtain ⟨e⟩ := hmodel
    exact psl4_coset_action e H hodd hquot
  · obtain ⟨e⟩ := hmodel
    exact alternating7_coset_action e H hodd hquot

end FifteenPointSubgroups
