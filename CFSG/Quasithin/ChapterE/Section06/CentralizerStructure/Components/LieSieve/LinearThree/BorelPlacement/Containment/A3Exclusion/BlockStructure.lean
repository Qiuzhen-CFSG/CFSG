module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Covers
public import Theory.GroupTheory.CentralPPerfectCoprime

/-!
# The order and center of an actual A₃ block

The quotient D/U(D) maps to D/O₂(D) with a central two-group kernel.
Two-perfection and the cyclic image of order three make this map injective,
so O₂(D) = U(D). The already proved coprime covering-module calculation
makes C_U(D)(D) trivial. Thus the genuine alternating-module clauses give
|U(D)| = 4, |D| = 12, and Z(D) = 1.

These consequences are proved from the short-group and alternating-module
definitions. No identification with A₄ is assumed. They retain the noncentral
module for the component-orbit argument; factoring out the entire two-core
would lose the information needed for Borel exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7 and
C.1.12–13, printed pp.123–125, applied in E.6.8, printed p.248.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment.A3Exclusion
variable {G : Type*} [Group G] {D : Subgroup G}

/-- The actual alternating quotient has order three. -/
theorem alternatingThree_quotient_card (h : IsAlternatingBlock D 3) : Nat.card (D ⧸ pCore 2 D) = 3 := by
  obtain ⟨e⟩ := h.2.2.quotient_iso
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num

/-- Two-perfection removes the central two-kernel above the cyclic quotient. -/
theorem alternatingThree_core_eq_blockU (h : IsAlternatingBlock D 3) : pCore 2 D = blockU D := by
  let : Finite D := h.2.1.finite
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := alternatingThree_quotient_card h
  let : IsCyclic (D ⧸ pCore 2 D) := isCyclic_of_prime_card hcard
  let f : (D ⧸ blockU D) →* (D ⧸ pCore 2 D) :=
    QuotientGroup.map (blockU D) (pCore 2 D) (MonoidHom.id D) blockU_le_core
  have hk : f.ker = (pCore 2 D).map (QuotientGroup.mk' (blockU D)) := by
    exact QuotientGroup.ker_map (blockU D) (pCore 2 D) (MonoidHom.id D) blockU_le_core
  have hi : Function.Injective f :=
    f.injective_of_isPPerfect_of_coprime_abelian_image
      (h.2.1.quotient_twoPerfect (blockU D))
      (by rw [hk]; exact blockU_core_image_le_center)
      (by rw [hk]; exact pCore_isPGroup.map _)
      (fun _ _ => mul_comm' _ _) (by decide : Nat.Coprime 2 3)
      (fun x => by simpa only [hcard] using (pow_card_eq_one' (x := f x)))
  apply le_antisymm _ blockU_le_core
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply hi
  exact (QuotientGroup.eq_one_iff x).mpr hx

/-- The full commutator module has order four; its central layer is trivial. -/
theorem alternatingThree_blockU_card (h : IsAlternatingBlock D 3) : Nat.card (blockU D) = 4 := by
  have hc := h.module_card_odd (by decide : Odd 3)
  have hz := InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.alternatingThreeCoverInput D h
  change Nat.card (blockU D ⧸ blockFixed D) = 4 at hc
  rw [hz] at hc
  exact (Nat.card_congr (QuotientGroup.quotientBot).toEquiv).symm.trans hc

/-- An A₃ block has order twelve, derived without an assumed A₄ identification. -/
theorem alternatingThree_card (h : IsAlternatingBlock D 3) : Nat.card D = 12 := by
  have hc := (pCore 2 D).card_mul_index
  rw [alternatingThree_core_eq_blockU h, alternatingThree_blockU_card h] at hc
  have hi : (blockU D).index = 3 := by
    rw [← alternatingThree_core_eq_blockU h]
    exact alternatingThree_quotient_card h
  rw [hi] at hc
  exact hc.symm

/-- The center of an A₃ block is trivial. -/
theorem alternatingThree_center_eq_bot (h : IsAlternatingBlock D 3) : center D = ⊥ := by
  have hz := InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.alternatingThreeCoverInput D h
  have hzU : blockU D ⊓ center D = ⊥ := by
    rw [← blockFixed_map, hz, Subgroup.map_bot]
  have hc : center D ≤ pCore 2 D := by
    let : CommGroup (center D) := IsMulCommutative.instCommGroup
    exact h.2.1.fitting ▸ (show center D ≤ fittingSubgroup D from
      le_sSup ⟨inferInstance, inferInstance⟩).trans (fitting_le_generalizedFitting D)
  apply bot_unique
  rw [← hzU]
  exact le_inf ((alternatingThree_core_eq_blockU h) ▸ hc) le_rfl
end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment.A3Exclusion
