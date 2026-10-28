module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.SimpleSection
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.PrimeRankInvolutionLift

/-!
# Transport and order obstructions for the finite-model sieve

The ordinary fixed component has order 168, so seven divides both the fixed
subgroup and the ambient group. Three-rank two supplies an actual elementary
subgroup of order nine. An isomorphism of ambient groups transports the given
automorphism and its ordinary component, including the PSL₃(2) isomorphism.

These are the inputs used to inspect the finite alternatives of Theorem C in
Aschbacher–Smith, proof of 15.3.38, printed p.1137; Theorem C, printed p.33.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification

universe u v
variable {S : Type u} [Group S] (s : SimpleInput S)
include s

/-- The retained component is the actual group of order 168. -/
theorem SimpleInput.component_card : Nat.card s.component = 168 :=
  (Nat.card_congr s.equiv.toEquiv).trans Matrix.PSL3Two.card_PSL

/-- Seven divides the fixed subgroup, not merely a quotient of it. -/
theorem SimpleInput.seven_dvd_fixed_card : 7 ∣ Nat.card s.involution.fixedSubgroup :=
  (show 7 ∣ Nat.card s.component by rw [s.component_card]; norm_num).trans
    s.component.card_subgroup_dvd_card

/-- The fixed component also forces seven to divide the ambient order. -/
theorem SimpleInput.seven_dvd_card : 7 ∣ Nat.card S :=
  s.seven_dvd_fixed_card.trans s.involution.fixedSubgroup.card_subgroup_dvd_card

/-- Three-rank two forces nine to divide the ambient order. -/
theorem SimpleInput.nine_dvd_card [Finite S] : 9 ∣ Nat.card S := by
  obtain ⟨E, _, hE⟩ := exists_elementaryAbelian_card_primeRank (G := S) (p := 3)
  have h := E.card_subgroup_dvd_card
  simpa only [hE, s.rank, show (3 : ℕ) ^ 2 = 9 by norm_num] using h

/-- Transport the involution and its ordinary component to a concrete model.
The subgroup remains subnormal and quasisimple in the whole fixed subgroup. -/
theorem SimpleInput.fixed_component_of_equiv {T : Type v} [Group T] (e : S ≃* T) :
    ∃ a : MulAut T, orderOf a = 2 ∧
      ∃ D : Subgroup a.fixedSubgroup, IsComponent a.fixedSubgroup D ∧
        Nonempty (D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let f := MulAut.fixedSubgroupCongr e s.involution
  refine ⟨MulAut.congr e s.involution,
    ((MulAut.congr e).orderOf_eq _).trans s.involution_order,
    s.component.map f.toMonoidHom, s.isComponent.map_equiv f, ?_⟩
  exact ⟨(f.subgroupMap s.component).symm.trans s.equiv⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
