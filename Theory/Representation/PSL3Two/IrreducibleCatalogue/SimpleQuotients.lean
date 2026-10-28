module

public import Theory.Representation.SubrepresentationLattice
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-!
# Simple quotients of extensions and product representations

A simple quotient of an extension of two simple modules is isomorphic to one
of those modules. The proof restricts the quotient map to the submodule; if
that restriction vanishes, the map factors through the actual quotient by its
kernel. Product restrictions and the one-dimensional binary trivial module
supply the remaining elementary cases.

These arguments assemble the four concrete binary SL₃(2) modules in
Aschbacher–Smith H.6.1 from the flag decomposition and core exact sequences.
They do not assume a representation catalogue.
-/

@[expose] public section

open Representation
namespace BinaryLinearThree.IrreducibleCatalogue

private theorem factor_intertwiner
    {k G X Y Z : Type*} [Field k] [Monoid G]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup Z] [Module k Z]
    {α : Representation k G X} {β : Representation k G Y} {γ : Representation k G Z}
    (π : α.IntertwiningMap β) (hπ : Function.Surjective π)
    (f : α.IntertwiningMap γ)
    (hker : LinearMap.ker π.toLinearMap ≤ LinearMap.ker f.toLinearMap) :
    ∃ g : β.IntertwiningMap γ, g.comp π = f := by
  let q := π.toLinearMap.quotKerEquivOfSurjective hπ
  let l := ((LinearMap.ker π.toLinearMap).liftQ f.toLinearMap hker).comp q.symm.toLinearMap
  have hl (x : X) : l (π x) = f x := by
    change (LinearMap.ker π.toLinearMap).liftQ f.toLinearMap hker
      (q.symm (π x)) = f x
    have hq : q.symm (π x) = Submodule.Quotient.mk x := by
      simpa only [q, IntertwiningMap.toLinearMap_apply] using
        (LinearMap.quotKerEquivOfSurjective_symm_apply (f := π.toLinearMap) hπ x)
    rw [hq]
    rfl
  let g : β.IntertwiningMap γ := {
    toLinearMap := l
    isIntertwining' := by
      intro a
      apply LinearMap.ext
      intro y
      obtain ⟨x,rfl⟩ := hπ y
      change l (β a (π x)) = γ a (l (π x))
      rw [← π.isIntertwining, hl, f.isIntertwining, hl] }
  exact ⟨g, IntertwiningMap.ext (LinearMap.ext hl)⟩

theorem simple_quotient_of_extension
    {k G A X B M : Type*} [Field k] [Monoid G]
    [AddCommGroup A] [Module k A] [AddCommGroup X] [Module k X]
    [AddCommGroup B] [Module k B] [AddCommGroup M] [Module k M]
    {α : Representation k G A} {ξ : Representation k G X}
    {β : Representation k G B} {ρ : Representation k G M}
    [IsIrreducible α] [IsIrreducible β] [IsIrreducible ρ]
    (i : α.IntertwiningMap ξ) (π : ξ.IntertwiningMap β)
    (hπ : Function.Surjective π)
    (hexact : LinearMap.range i.toLinearMap = LinearMap.ker π.toLinearMap)
    (f : ξ.IntertwiningMap ρ) (hf : f ≠ 0) :
    Nonempty (ρ.Equiv α) ∨ Nonempty (ρ.Equiv β) := by
  by_cases hi : f.comp i = 0
  · have hker : LinearMap.ker π.toLinearMap ≤ LinearMap.ker f.toLinearMap := by
      rw [← hexact]
      rintro _ ⟨a,rfl⟩
      exact congrArg (fun h : α.IntertwiningMap ρ => h a) hi
    obtain ⟨g,hg⟩ := factor_intertwiner π hπ f hker
    have hgne : g ≠ 0 := by
      intro hz
      apply hf
      rw [← hg, hz]
      ext x
      rfl
    obtain hbij | hz := IsIrreducible.bijective_or_eq_zero g
    · exact Or.inr ⟨(g.ofBijective hbij).symm⟩
    · exact False.elim (hgne hz)
  · obtain hbij | hz := IsIrreducible.bijective_or_eq_zero (f.comp i)
    · exact Or.inl ⟨((f.comp i).ofBijective hbij).symm⟩
    · exact False.elim (hi hz)

theorem nonzero_restriction_of_prod
    {k G A B M : Type*} [Field k] [Monoid G]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup M] [Module k M]
    {α : Representation k G A} {β : Representation k G B} {ρ : Representation k G M}
    (f : (α.prod β).IntertwiningMap ρ) (hf : f ≠ 0) :
    f.comp (IntertwiningMap.inl k α β) ≠ 0 ∨
      f.comp (IntertwiningMap.inr k α β) ≠ 0 := by
  by_contra! h
  apply hf
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have hl := congrArg (fun q : α.IntertwiningMap ρ => q x.1) h.1
  have hr := congrArg (fun q : β.IntertwiningMap ρ => q x.2) h.2
  have he : (x.1, (0 : B)) + (0, x.2) = x := by ext <;> simp
  rw [← he, map_add]
  change f (x.1,0) + f (0,x.2) = 0
  change f (x.1,0) = 0 at hl
  change f (0,x.2) = 0 at hr
  rw [hl,hr,add_zero]

theorem simple_quotient_of_binary_trivial
    {G M : Type*} [Monoid G] [AddCommGroup M] [Module (ZMod 2) M]
    {ρ : Representation (ZMod 2) G M} [IsIrreducible ρ]
    (f : (Representation.trivial (ZMod 2) G (ZMod 2)).IntertwiningMap ρ)
    (hf : f ≠ 0) : Nonempty (ρ.Equiv (Representation.trivial (ZMod 2) G (ZMod 2))) := by
  have hf1 : f 1 ≠ 0 := by
    intro h
    apply hf
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    fin_cases x
    · exact map_zero f
    · exact h
  have hi : Function.Injective f := by
    intro x y h
    fin_cases x <;> fin_cases y
    · rfl
    · exact False.elim (hf1 (h.symm.trans (map_zero f)))
    · exact False.elim (hf1 (h.trans (map_zero f)))
    · rfl
  obtain hs | hz := IsIrreducible.surjective_or_eq_zero f
  · exact ⟨(f.ofBijective ⟨hi,hs⟩).symm⟩
  · exact False.elim (hf hz)

end BinaryLinearThree.IrreducibleCatalogue
