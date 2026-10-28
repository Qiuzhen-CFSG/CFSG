module

public import Theory.Representation.EndFieldRep
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect groups commuting with an irreducible binary action

Schur's lemma identifies the endomorphisms of a finite irreducible binary
module with a finite field. A commuting perfect group maps to its abelian
unit group and consequently fixes the whole module. The representation and
its commuting action are retained, without choosing coordinates or assuming
absolute irreducibility.

Source: the Schur-lemma step in GLS3, proof of Theorem 6.5.3, p.347;
application to Aschbacher–Smith B.5.6(3a) and 10.1.1.
-/

public noncomputable section
open scoped MonoidAlgebra
open Representation
namespace Representation.BinaryOffender

theorem perfect_commuting_irreducible
    {A H W : Type*} [Group A] [Group H] [Group.IsPerfect H]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (α : Representation (ZMod 2) A W) [α.IsIrreducible]
    (τ : Representation (ZMod 2) H W)
    (hc : ∀ a h, τ h * α a = α a * τ h) : ∀ h v, τ h v = v := by
  let t : H →* IntertwiningMap α α := {
    toFun h := ⟨τ h,fun a => hc a h⟩
    map_one' := by ext v; exact LinearMap.congr_fun (map_one τ) v
    map_mul' := by intro a b; ext v; exact LinearMap.congr_fun (map_mul τ a b) v }
  let e := IntertwiningMap.equivAlgEnd α
  let f := (e.toMonoidHom.comp t).toHomUnits
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : IsMulCommutative f.range := inferInstance
  let : Subsingleton f.range := inferInstance
  intro h v
  have he : e (t h) = 1 := congrArg (fun x : f.range => (x.val : Module.End (ZMod 2)[A] α.asModule))
    (Subsingleton.elim (⟨f h,h,rfl⟩ : f.range) 1)
  have ht : t h = 1 := e.injective (he.trans (map_one e).symm)
  exact LinearMap.congr_fun (congrArg IntertwiningMap.toLinearMap ht) v

end Representation.BinaryOffender
