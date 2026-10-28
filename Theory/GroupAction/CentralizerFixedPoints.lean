module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Centralizers acting on fixed points

An element's centralizer preserves its fixed points in every permutation
representation. Restricting the representation therefore gives a homomorphism;
the original element is in its kernel. This construction keeps the possible
central cover visible when identifying the permutation image.

The proof uses only commutation and injectivity of permutations. One application
is the involution-centralizer section in GLS3, Table 5.3t.
-/

public section

namespace Theory.GroupAction.CentralizerFixedPoints
variable {G X : Type*} [Group G]

/-- Points fixed by the given element in a permutation representation. -/
abbrev Points (ρ : G →* Equiv.Perm X) (t : G) := {x : X // ρ t x = x}

private theorem commutes (ρ : G →* Equiv.Perm X) (t : G)
    (g : Subgroup.centralizer ({t} : Set G)) (x : X) :
    ρ t (ρ g.val x) = ρ g.val (ρ t x) := by
  have h := (Subgroup.mem_centralizer_singleton_iff.mp g.property).symm
  simpa only [map_mul, Equiv.Perm.mul_apply] using congrArg (fun a : G => ρ a x) h

private theorem preserves (ρ : G →* Equiv.Perm X) (t : G)
    (g : Subgroup.centralizer ({t} : Set G)) (x : X) :
    ρ t (ρ g.val x) = ρ g.val x ↔ ρ t x = x := by
  rw [commutes]
  exact (ρ g.val).injective.eq_iff

/-- Restrict the centralizer to the fixed points. -/
def action (ρ : G →* Equiv.Perm X) (t : G) :
    Subgroup.centralizer ({t} : Set G) →* Equiv.Perm (Points ρ t) where
  toFun g := (ρ g.val).subtypePerm (preserves ρ t g)
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun e : Equiv.Perm X => e x.val) ρ.map_one
  map_mul' g h := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun e : Equiv.Perm X => e x.val) (ρ.map_mul g.val h.val)

theorem action_apply (ρ : G →* Equiv.Perm X) (t : G)
    (g : Subgroup.centralizer ({t} : Set G)) (x : Points ρ t) :
    (action ρ t g x).val = ρ g.val x.val := by rfl

/-- The element itself is in its centralizer. -/
@[expose] def centralElement (t : G) : Subgroup.centralizer ({t} : Set G) :=
  ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem centralElement_mem_ker (ρ : G →* Equiv.Perm X) (t : G) :
    centralElement t ∈ (action ρ t).ker := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact x.property

end Theory.GroupAction.CentralizerFixedPoints
