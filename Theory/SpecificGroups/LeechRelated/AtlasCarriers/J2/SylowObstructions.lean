module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Sylow
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.GroupTheory.SylowCyclicDerivedSections
public import Theory.GroupTheory.PGroup.CyclicInvolution
/-!
# Sylow obstructions for exceptional component sections

Two distinct commutator involutions prove that the derived Sylow subgroup
is not cyclic. A second pair gives noncommuting involutions in the same
literal Sylow. All finite checks use the existing native permutation tables;
Sylow conjugacy transports the witnesses to every Sylow subgroup.

Source application: Aschbacher–Smith A.3.12, pp.47–48, and the exceptional
seed in 13.6.27, p.934 (combined manuscript of 1 March 2004).
-/
public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Sporadic.LeechRelated.J2
open ExceptionalParabolics PairNormalizer PairNormalizer.SylowData
private abbrev P := SecondParabolic.sylow FirstParabolic.card_l₁
private def v (i : Fin 128) : P := ⟨sElement i, sElement_mem i⟩
private def f : P →* Equiv.Perm (Fin 100) := inclusion.comp (P : Subgroup Carrier).subtype
private theorem hf : Function.Injective f := inclusion_injective.comp Subtype.val_injective
private theorem fv (i : Fin 128) : f (v i) = sTable i := sElement_inclusion i

theorem sylow_derived_not_cyclic (S : Sylow 2 Carrier) : ¬ IsCyclic (commutator S) := by
  intro hc
  let := derived_cyclic_of_injective (P.equiv S).toMonoidHom (P.equiv S).injective hc
  let x : commutator P := ⟨⁅v 3,v 1⁆, commutator_mem_commutator (mem_top _) (mem_top _)⟩
  let y : commutator P := ⟨⁅v 3,v 2⁆, commutator_mem_commutator (mem_top _) (mem_top _)⟩
  have hx : orderOf x = 2 := by
    rw [← orderOf_coe, ← orderOf_injective f hf]
    change orderOf (f ⁅v 3,v 1⁆) = 2
    rw [map_commutatorElement, fv, fv]
    apply orderOf_eq_prime <;> decide +kernel
  have hy : orderOf y = 2 := by
    rw [← orderOf_coe, ← orderOf_injective f hf]
    change orderOf (f ⁅v 3,v 2⁆) = 2
    rw [map_commutatorElement, fv, fv]
    apply orderOf_eq_prime <;> decide +kernel
  have hne : f x.val ≠ f y.val := by
    change f ⁅v 3,v 1⁆ ≠ f ⁅v 3,v 2⁆
    rw [map_commutatorElement, map_commutatorElement, fv, fv, fv]
    decide +kernel
  exact hne (congrArg (fun z : commutator P => f z.val)
    (IsCyclic.eq_of_orderOf_eq_two hx hy))

theorem exists_noncommuting_sylow_involutions (S : Sylow 2 Carrier) :
    ∃ x y : S, x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ x*y ≠ y*x := by
  have hx : v 8 ^ 2 = 1 := by
    apply hf
    rw [map_pow, fv, map_one]
    decide +kernel
  have hy : v 1 ^ 2 = 1 := by
    apply hf
    rw [map_pow, fv, map_one]
    decide +kernel
  have hne : v 8 * v 1 ≠ v 1 * v 8 := by
    intro h
    have hh := congrArg f h
    rw [map_mul, map_mul, fv, fv] at hh
    exact (by decide +kernel : sTable 8 * sTable 1 ≠ sTable 1 * sTable 8) hh
  let e := P.equiv S
  refine ⟨e (v 8),e (v 1),?_,?_,?_⟩
  · rw [← map_pow, hx, map_one]
  · rw [← map_pow, hy, map_one]
  · intro h
    exact hne (e.injective (by simpa only [map_mul] using h))
end Sporadic.LeechRelated.J2

