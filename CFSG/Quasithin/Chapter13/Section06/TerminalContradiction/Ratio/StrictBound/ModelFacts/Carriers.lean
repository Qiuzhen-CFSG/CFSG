module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Models
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterTwoGroup
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Centers, involutions, and sporadic outer orders for the terminal models

PSL₃(4) has trivial center by perfectness of SL₃ and Grün's lemma; its
projected transvection is an involution. The concrete J₂ permutation action
has trivial centralizer and its first ATLAS generator is an involution.
The existing M₂₃ design theorems supply centerlessness and an involution.
All statements transport through genuine group equivalences.

The J₂ permutation extension surjects onto Aut(J₂). After killing its
inner subgroup, the single additional involution generates the quotient,
so its order divides two. Every automorphism of the concrete M₂₃ is inner.
These strengthen the two-group results enough for the terminal rank bound.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), terminal
paragraph of §13.6, printed pp.934–935; GLS3, Tables 5.3d and 5.3g.
The imported J2G1-p100B0 certificates retain their ATLAS attribution.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.ModelFacts

theorem l3Four_center : center Components.L3Four = ⊥ := by
  let := Atlas.sl_perfect (F := Components.F4) 3 (by decide)
  exact Group.IsPerfect.center_quotient_center_eq_bot _

theorem j2_center : center Sporadic.LeechRelated.J2.Carrier = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply Subtype.ext
  have hc : x.val ∈ centralizer
      (Sporadic.LeechRelated.J2.generated : Set (Equiv.Perm (Fin 100))) := by
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)
  rwa [Sporadic.LeechRelated.J2.ExceptionalParabolics.permutation_centralizer_eq_bot] at hc

theorem l3Four_involution : ∃ t : Components.L3Four, orderOf t = 2 := by
  let u := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1)
    (1 : Components.F4)
  let q := QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 3) Components.F4))
  refine ⟨q u, orderOf_eq_prime ?_ ?_⟩
  · have hu : u ^ 2 = 1 := by
      dsimp [u]
      rw [pow_two, ← Matrix.SpecialLinearGroup.transvection_add]
      have h : (1 : Components.F4) + 1 = 0 := by
        exact CharTwo.add_self_eq_zero (1 : Components.F4)
      rw [h, Matrix.SpecialLinearGroup.transvection_coeff_zero]
    rw [← map_pow, hu, map_one]
  · intro he
    have hu := (QuotientGroup.eq_one_iff u).mp he
    exact one_ne_zero (Matrix.SpecialLinearGroup.transvection_mem_center_iff _ _ |>.mp hu)

theorem j2_involution : ∃ t : Sporadic.LeechRelated.J2.Carrier, orderOf t = 2 := by
  open Sporadic.LeechRelated.J2.GeneratorPair in
    refine ⟨a, orderOf_eq_prime a_pow_two ?_⟩
  intro h
  have he := congrArg (fun g : Sporadic.LeechRelated.J2.Carrier => g.val (0 : Fin 100)) h
  change Sporadic.LeechRelated.J2.generatorA 0 = 0 at he
  rw [Sporadic.LeechRelated.J2.GeneratorPair.generatorA_eq_table] at he
  exact (by decide : ¬ Sporadic.LeechRelated.J2.GeneratorPair.tableA 0 = 0) he

private theorem center_of_equiv {L M : Type*} [Group L] [Group M]
    (e : L ≃* M) (h : center M = ⊥) : center L = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply e.injective
  rw [map_one]
  have hx' : e x ∈ center M := (centerCongr e ⟨x, hx⟩).property
  rwa [h] at hx'

theorem exceptional_center {L : Type*} [Group L] (h : ExceptionalModel L) :
    center L = ⊥ := by
  unfold ExceptionalModel at h
  rcases h with h | h | h <;> let e := Classical.choice h
  · exact center_of_equiv e l3Four_center
  · exact center_of_equiv e Sporadic.Mathieu.M23Geometry.m23_center_eq_bot
  · exact center_of_equiv e j2_center

theorem exceptional_involution {L : Type*} [Group L] (h : ExceptionalModel L) :
    ∃ t : L, orderOf t = 2 := by
  unfold ExceptionalModel at h
  rcases h with h | h | h <;> let e := Classical.choice h
  · obtain ⟨t, ht⟩ := l3Four_involution
    exact ⟨e.symm t, (e.symm.orderOf_eq t).trans ht⟩
  · exact ⟨e.symm Sporadic.Mathieu.M23Geometry.involutionRepresentative,
      (e.symm.orderOf_eq _).trans Sporadic.Mathieu.M23Geometry.involutionRepresentative_order⟩
  · obtain ⟨t, ht⟩ := j2_involution
    exact ⟨e.symm t, (e.symm.orderOf_eq t).trans ht⟩

theorem m23_outer_card : Nat.card (MulAut.Outer Sporadic.Mathieu.M23) = 1 := by
  have h : MulAut.innerSubgroup Sporadic.Mathieu.M23 = ⊤ :=
    MonoidHom.range_eq_top.mpr Sporadic.Mathieu.m23_conj_surjective
  change Nat.card (MulAut Sporadic.Mathieu.M23 ⧸ _) = _
  rw [h]
  exact Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩

theorem j2_outer_card_dvd : Nat.card (MulAut.Outer Sporadic.LeechRelated.J2.Carrier) ∣ 2 := by
  open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
    Sporadic.LeechRelated.J2.GeneratorPair in
    let q := QuotientGroup.mk' (MulAut.innerSubgroup Carrier)
    let f := q.comp extensionAction
    have hs : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
      (extensionAction_surjective_of_pair_calculations first_generator_conjugate
        second_generator_orbits)
    let N := generated.subgroupOf extension
    have hgen : N ⊔ zpowers extensionInvolution = ⊤ := by
      apply (map_injective extension.subtype_injective)
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show generated ≤ extension from le_sup_left),
        MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype]
      rfl
    have hN : N.map f = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      intro x hx
      change q (extensionAction x) = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      refine ⟨⟨x, hx⟩, ?_⟩
      exact (extensionAction_inner ⟨x, hx⟩).symm
    have himg := congrArg (map f) hgen
    rw [Subgroup.map_sup, hN, bot_sup_eq, map_top_of_surjective f hs] at himg
    have hd : Nat.card (zpowers extensionInvolution) ∣ 2 := by
      rw [Nat.card_zpowers]
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      change involution ^ 2 = 1
      simpa only [pow_two] using involution_mul_self
    have hh := card_map_dvd (zpowers extensionInvolution) f
    rw [himg, Nat.card_congr topEquiv.toEquiv] at hh
    exact hh.trans hd

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.ModelFacts
