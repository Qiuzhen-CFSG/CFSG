module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic.Group
/-!
# Subgroup images determined by agreement on a normal core

Two homomorphisms agreeing on a normal subgroup with self-centralizing image
can differ on any element only by multiplication by that core image.
Consequently they have the same image of every subgroup containing the core.

The source application is the full sixteen-core in Aschbacher--Smith 5.2.20(5),
printed pp.656--657. Once the two vertex markings agree on that core and both
carry H into the native heptad local, their images of the whole Ix coincide.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.QuasithinM23

/-- Maps agreeing on a normal core with self-centralizing image have the
same images of every overgroup of that core. -/
theorem map_eq_of_agree_on_selfCentralizing_normal
    {D E : Type*} [Group D] [Group E]
    (N R : Subgroup D) [N.Normal] (hNR : N ≤ R)
    (f g : D →* E) (hagree : ∀ n : N, f n = g n)
    (hself : centralizer (N.map f : Set E) ≤ N.map f) :
    R.map f = R.map g := by
  have hcore : N.map f = N.map g := by
    ext y
    constructor
    · rintro ⟨n,hn,rfl⟩
      exact ⟨n,hn,(hagree ⟨n,hn⟩).symm⟩
    · rintro ⟨n,hn,rfl⟩
      exact ⟨n,hn,hagree ⟨n,hn⟩⟩
  have hdis (a : D) : f a * (g a)⁻¹ ∈ N.map f := by
    apply hself
    apply mem_centralizer_iff.mpr
    rintro _ ⟨n,hn,rfl⟩
    have hin : a⁻¹ * n * a ∈ N := by
      simpa only [inv_inv] using (inferInstance : N.Normal).conj_mem n hn a⁻¹
    have hh := hagree ⟨_,hin⟩
    change f (a⁻¹*n*a) = g (a⁻¹*n*a) at hh
    rw [map_mul,map_mul,map_inv,map_mul,map_mul,map_inv,←hagree ⟨n,hn⟩] at hh
    have he := congrArg (fun z => f a * z * (g a)⁻¹) hh
    group at he
    simpa only [mul_assoc,zpow_neg_one] using he
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    have hd : f a * (g a)⁻¹ ∈ R.map g :=
      map_mono hNR (hcore ▸ hdis a)
    have hm := (R.map g).mul_mem hd (mem_map_of_mem g ha)
    simpa only [inv_mul_cancel_right] using hm
  · rintro _ ⟨a,ha,rfl⟩
    have hd : f a * (g a)⁻¹ ∈ R.map f := map_mono hNR (hdis a)
    have hm := (R.map f).mul_mem ((R.map f).inv_mem hd) (mem_map_of_mem f ha)
    simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hm
end Theory.GroupTheory.QuasithinM23
