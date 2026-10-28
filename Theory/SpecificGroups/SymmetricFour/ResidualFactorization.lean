module

public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.Data.Fintype.Perm

/-!
# Two-residuals over the symmetric four-group

The commutator subgroup and two-residual of S₄ are both A₄. For a
surjection onto S₄ with odd kernel, that kernel lies in the two-residual.
Equality of the two images then identifies the source two-residual with
its derived subgroup joined with the kernel. The only finite check gives
a single commutator expression for each of the twelve even permutations.

Source application: Aschbacher–Smith, 13.2.2(3), printed p.877.
-/

public section

open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymmetricFourResidual

private theorem even_commutator :
    ∀ g : Equiv.Perm (Fin 4), g.sign = 1 →
      ∃ a b : Equiv.Perm (Fin 4), ⁅a,b⁆ = g := by decide +kernel

theorem derived_eq : commutator (Equiv.Perm (Fin 4)) = alternatingGroup (Fin 4) := by
  apply le_antisymm alternatingGroup.commutator_perm_le
  intro g hg
  obtain ⟨a,b,rfl⟩ := even_commutator g hg
  exact commutator_mem_commutator (mem_top a) (mem_top b)

theorem residual_eq : pResidual 2 (Equiv.Perm (Fin 4)) = alternatingGroup (Fin 4) := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 4)).index = 2 ^ 1
    simp
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro g hg
    apply mem_pResidual_of_orderOf_coprime
    rw [Equiv.Perm.IsThreeCycle.orderOf hg]
    decide

theorem residual_eq_derived_sup_kernel {X : Type*} [Group X] [Finite X]
    (f : X →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f)
    (hk : Nat.Coprime 2 (Nat.card f.ker)) :
    pResidual 2 X = commutator X ⊔ f.ker := by
  have hkR : f.ker ≤ pResidual 2 X := by
    intro x hx
    apply mem_pResidual_of_orderOf_coprime
    apply hk.of_dvd_right
    simpa only [Subgroup.orderOf_mk] using orderOf_dvd_natCard (⟨x,hx⟩:f.ker)
  have hR : (pResidual 2 X).map f = alternatingGroup (Fin 4) := by
    rw [map_pResidual_of_surjective 2 f hf, residual_eq]
  have hD : (commutator X).map f = alternatingGroup (Fin 4) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf, ← commutator_def, derived_eq]
  have he : (pResidual 2 X).map f = (commutator X).map f := hR.trans hD.symm
  have hh := congrArg (Subgroup.comap f) he
  simpa only [comap_map_eq, sup_eq_left.mpr hkR] using hh

end Theory.SpecificGroups.SymmetricFourResidual

end
