module
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Fusion.Certificate
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
namespace Sporadic.Mathieu
open M23Geometry.FusionCertificate
private def v (i : Fin 128) : sylow := ⟨⟨perm i, rawSubgroup_le (perm_mem i)⟩, perm_mem i⟩
private def f : sylow →* Equiv.Perm (Fin 23) := M23.subtype.comp (sylow : Subgroup M23).subtype
private theorem hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
private theorem fv (i : Fin 128) : f (v i) = perm i := rfl

theorem m23_sylow_derived_not_cyclic (S : Sylow 2 M23) : ¬ IsCyclic (commutator S) := by
  intro hc
  let := derived_cyclic_of_injective (sylow.equiv S).toMonoidHom (sylow.equiv S).injective hc
  let x : commutator sylow := ⟨⁅v 2,v 1⁆, commutator_mem_commutator (mem_top _) (mem_top _)⟩
  let y : commutator sylow := ⟨⁅v 8,v 1⁆, commutator_mem_commutator (mem_top _) (mem_top _)⟩
  have hx : orderOf x = 2 := by
    rw [← orderOf_coe, ← orderOf_injective f hf]
    change orderOf (f ⁅v 2,v 1⁆) = 2
    rw [map_commutatorElement, fv, fv]
    apply orderOf_eq_prime <;> decide +kernel
  have hy : orderOf y = 2 := by
    rw [← orderOf_coe, ← orderOf_injective f hf]
    change orderOf (f ⁅v 8,v 1⁆) = 2
    rw [map_commutatorElement, fv, fv]
    apply orderOf_eq_prime <;> decide +kernel
  have hne : f x.val ≠ f y.val := by
    change f ⁅v 2,v 1⁆ ≠ f ⁅v 8,v 1⁆
    rw [map_commutatorElement, map_commutatorElement, fv, fv, fv]
    decide +kernel
  exact hne (congrArg (fun z : commutator sylow => f z.val)
    (IsCyclic.eq_of_orderOf_eq_two hx hy))

theorem m23_exists_noncommuting_sylow_involutions (S : Sylow 2 M23) :
    ∃ x y : S, x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ x*y ≠ y*x := by
  have hx : v 3 ^ 2 = 1 := by
    apply hf
    rw [map_pow, fv, map_one]
    decide +kernel
  have hy : v 1 ^ 2 = 1 := by
    apply hf
    rw [map_pow, fv, map_one]
    decide +kernel
  have hne : v 3 * v 1 ≠ v 1 * v 3 := by
    intro h
    have hh := congrArg f h
    rw [map_mul, map_mul, fv, fv] at hh
    exact (by decide +kernel : perm 3 * perm 1 ≠ perm 1 * perm 3) hh
  let e := sylow.equiv S
  refine ⟨e (v 3),e (v 1),?_,?_,?_⟩
  · rw [← map_pow, hx, map_one]
  · rw [← map_pow, hy, map_one]
  · intro h
    exact hne (e.injective (by simpa only [map_mul] using h))
end Sporadic.Mathieu
