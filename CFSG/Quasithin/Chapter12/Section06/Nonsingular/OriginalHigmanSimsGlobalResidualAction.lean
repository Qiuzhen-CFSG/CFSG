module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalSource
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsSingularComponents
public import Theory.Alternating.Aut

/-!
# The common HS residual is moved above the singular two-core

In a group with intrinsic two-core quotient S5, the centralizer of its
prime-to-three residual modulo that two-core is just the two-core. Indeed,
the residual image is A5 and its centralizer in S5 is trivial. This keeps
both the original residual and the entire quotient kernel.

Source application: the actual common subgroup in the original HS branch
of Aschbacher--Smith 12.6.12, printed pp.825--826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsGlobal

private theorem symmetricFive_primeToResidual :
    primeToResidual 3 (Equiv.Perm (Fin 5)) = alternatingGroup (Fin 5) := by
  apply primeToResidual_eq_of_generated (alternatingGroup (Fin 5))
    (by rw [alternatingGroup.index_eq_two]; decide)
    _ Equiv.Perm.closure_three_cycles_eq_alternating
  intro x hx
  refine ⟨1,?_⟩
  simpa only [pow_one,hx.orderOf] using pow_orderOf_eq_one x

/-- A subgroup centralizing the cubic residual modulo the original two-core
lies in that core when the literal quotient is S5. -/
theorem le_core_of_residual_commutator_le
    {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 5))
    (U : Subgroup A) (hc : ⁅U,primeToResidual 3 A⁆ ≤ pCore 2 A) :
    U ≤ pCore 2 A := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hr : (primeToResidual 3 A).map q = alternatingGroup (Fin 5) := by
    rw [map_primeToResidual_of_surjective 3 q hq,symmetricFive_primeToResidual]
  have hm : ⁅U.map q,alternatingGroup (Fin 5)⁆ = ⊥ := by
    apply bot_unique
    rw [←hr,←map_commutator]
    have h := map_mono (f := q) hc
    have hz : (pCore 2 A).map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hk.ge
    exact h.trans_eq hz
  have hu : U.map q = ⊥ := bot_unique ((commutator_eq_bot_iff_le_centralizer.mp hm).trans_eq
    (_root_.GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 5 (by decide)))
  rw [←hk]
  exact (Subgroup.map_eq_bot_iff _).mp hu

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsGlobal
