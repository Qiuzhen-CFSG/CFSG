module
public import Theory.GroupTheory.SymmetricThreeResidualKernel
public import Theory.GroupTheory.GeneralizedFitting.OddNormalObstruction
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual

/-!
# Characteristic-two subgroups obstruct three-by-two groups

If N is a normal three-group with two-group quotient, the two-residual
of every subgroup lies in N. In a characteristic-two subgroup that
residual is both a normal three-group and a subgroup of O₂, so it
vanishes. Such a subgroup is therefore a two-group and cannot have
S₃ as its quotient over O₂.

This excludes both solvable models in F.6.18(2) once the original
shifted actor K has characteristic two. For S₃ × S₃ the normal
three-group is its actual two-residual A₃ × A₃.
Source application: Aschbacher--Smith 14.3.31, printed p.1003.
-/

public section
open Subgroup Theory.GroupTheory
namespace SymmetricThreeTwoCore
variable {D : Type*} [Group D] [Finite D]

/-- Every characteristic-two subgroup of a three-by-two group is a two-group. -/
theorem characteristic_two_subgroup_of_three_by_two (C N : Subgroup D) [N.Normal]
    (hC : generalizedFitting C = pCore 2 C)
    (hN : IsPGroup 3 N) (hQ : IsPGroup 2 (D ⧸ N)) : IsPGroup 2 C := by
  have hR : pResidual 2 C ≤ N.subgroupOf C := by
    have h := pResidual_le_ker_of_isPGroup 2 ((QuotientGroup.mk' N).comp C.subtype) hQ
    intro x hx
    exact (QuotientGroup.eq_one_iff (N := N) (x : D)).mp (h hx)
  have hr : IsPGroup 3 (pResidual 2 C) := hN.comap_subtype.to_le hR
  have hb := normal_pGroup_eq_bot_of_generalizedFitting_eq_pCore
    (by decide : 2 ≠ 3) hC (pResidual 2 C) hr
  exact isPGroup_of_residual_isPGroup 2 (hb ▸ IsPGroup.of_bot)

/-- An S₃ quotient over O₂ excludes a normal three-group with two-group quotient. -/
theorem characteristic_two_not_three_by_two (C : Subgroup D)
    (hC : generalizedFitting C = pCore 2 C)
    (model : (C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3))
    (N : Subgroup D) [N.Normal] (hN : IsPGroup 3 N) : ¬ IsPGroup 2 (D ⧸ N) := by
  intro hQ
  have hc := characteristic_two_subgroup_of_three_by_two C N hC hN hQ
  have ht : pCore 2 C = ⊤ := top_unique (le_sSup ⟨inferInstance,hc.to_subgroup ⊤⟩)
  have hi := core_index model
  rw [ht,index_top] at hi
  omega

/-- In particular, the ambient group cannot be S₃ × S₃. -/
theorem characteristic_two_not_symmetric_three_product (C : Subgroup D)
    (hC : generalizedFitting C = pCore 2 C)
    (model : (C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3)) :
    ¬ Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  rintro ⟨e⟩
  have hr : IsPGroup 3 (pResidual 2 D) := by
    have hp : IsPGroup 3 (pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :=
      IsPGroup.of_card (n := 2) SymmetricThreeProductResidual.residual_card
    have he := map_pResidual_of_surjective 2 e.toMonoidHom e.surjective
    exact (he ▸ hp).of_equiv (e.subgroupMap (pResidual 2 D)).symm
  exact characteristic_two_not_three_by_two C hC model _ hr (isPGroup_quotient_pResidual 2)
end SymmetricThreeTwoCore
