module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Transporting faithful graph actions

Graph isomorphisms conjugate the full automorphism groups. An actual faithful
permutation action preserving adjacency therefore remains faithful after
recognition of its graph. The original action maps are retained explicitly.
-/

@[expose] public section

namespace Theory.Combinatorics
variable {Ω Ξ:Type*} {G:SimpleGraph Ω} {H:SimpleGraph Ξ}

/-- Conjugate the full automorphism group through the actual graph isomorphism. -/
def graphAutomorphismEquiv (e:G≃gH) : (G≃gG)≃*(H≃gH) where
  toFun a:=e.symm.trans (a.trans e)
  invFun a:=e.trans (a.trans e.symm)
  left_inv a:=by ext x;simp
  right_inv a:=by ext x;simp
  map_mul' a b:=by ext x;simp

variable {A:Type*} [Group A]
/-- Lift an adjacency-preserving permutation action on the literal vertices. -/
def graphActionHom (ρ:A→*Equiv.Perm Ω)
    (hρ:∀a x y,G.Adj (ρ a x) (ρ a y) ↔ G.Adj x y) : A→*(G≃gG) where
  toFun a:={toEquiv:=ρ a,map_rel_iff':=fun {x y}=>hρ a x y}
  map_one':=by ext x;exact Equiv.congr_fun ρ.map_one x
  map_mul' a b:=by ext x;exact Equiv.congr_fun (ρ.map_mul a b) x

theorem graphActionHom_injective (ρ:A→*Equiv.Perm Ω)
    (hρ:∀a x y,G.Adj (ρ a x) (ρ a y) ↔ G.Adj x y)
    (hf:Function.Injective ρ) : Function.Injective (graphActionHom ρ hρ) := by
  intro a b hab
  apply hf
  ext x
  exact congrArg (fun f:G≃gG=>f x) hab
end Theory.Combinatorics
