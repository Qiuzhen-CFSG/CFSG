module

public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Automorphisms preserve the derived involution centralizer

An automorphism fixing the specified element preserves its full centralizer,
then its literal ambient derived subgroup. This is the characteristic block
used in the odd ternary case of Aschbacher--Smith6.1.4, printed p.666.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- Fixing the original element preserves the actual derived centralizer. -/
theorem derived_centralizer_map_eq_of_fixed
    {G : Type*} [Group G] (a : MulAut G) (z : G) (hz : a z=z) :
    ((commutator (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype).map a.toMonoidHom =
      (commutator (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype := by
  let C := centralizer ({z} : Set G)
  have hC : C.map a.toMonoidHom = C := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      change a y * z = z * a y
      have hh := congrArg a (mem_centralizer_singleton_iff.mp hy)
      simpa only [map_mul,hz] using hh
    · intro hx
      refine ⟨a.symm x,?_,a.apply_symm_apply x⟩
      apply mem_centralizer_singleton_iff.mpr
      apply a.injective
      simpa only [map_mul,a.apply_symm_apply,hz] using mem_centralizer_singleton_iff.mp hx
  rw [map_subtype_commutator,map_commutator,hC]

end Theory.GroupTheory
