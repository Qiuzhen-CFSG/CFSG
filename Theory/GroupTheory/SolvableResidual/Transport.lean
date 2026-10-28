module

public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Maps on solvable residuals and prime-core quotients

A surjection of finite groups restricts to a surjection of their solvable
residuals. A prime-group kernel remains a prime-group kernel on restriction.
A surjection with prime-group kernel induces an isomorphism after dividing
both groups by their prime cores, with the original map on representatives.
These maps retain the coordinates needed for central-cover restrictions.
-/

@[expose] public section

namespace MonoidHom
open Subgroup
variable {X Y : Type*} [Group X] [Group Y]

/-- Restrict a homomorphism to the solvable residuals. -/
def solvableResidualMap (f : X →* Y) : solvableResidual X →* solvableResidual Y :=
  (f.comp (solvableResidual X).subtype).codRestrict _
    (fun x => map_solvableResidual_le f (mem_map_of_mem f x.property))

@[simp] theorem solvableResidualMap_apply (f : X →* Y) (x : solvableResidual X) :
    (f.solvableResidualMap x : Y) = f x := rfl

theorem solvableResidualMap_surjective [Finite X] (f : X →* Y)
    (hf : Function.Surjective f) : Function.Surjective f.solvableResidualMap := by
  intro y
  have hy : (y : Y) ∈ (solvableResidual X).map f :=
    (map_solvableResidual_eq f hf).symm ▸ y.property
  obtain ⟨x, hx, he⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

theorem solvableResidualMap_ker (f : X →* Y) :
    f.solvableResidualMap.ker = f.ker.comap (solvableResidual X).subtype := by
  ext x
  change f.solvableResidualMap x = 1 ↔ f x = 1
  exact Subtype.ext_iff

theorem solvableResidualMap_ker_isPGroup (f : X →* Y) {p : ℕ}
    (hk : IsPGroup p f.ker) : IsPGroup p f.solvableResidualMap.ker := by
  rw [solvableResidualMap_ker]
  exact hk.comap_of_injective _ (solvableResidual X).subtype_injective

/-- The canonical prime-core quotient equivalence retains the original map
on representatives. Its definition is re-exported from `PCoreFrattiniTransport`.
-/
@[simp] theorem pCoreQuotientEquiv_apply [Finite X] [Finite Y]
    {p : ℕ} [Fact p.Prime] (f : X →* Y) (hf : Function.Surjective f)
    (hk : IsPGroup p f.ker) (x : X) :
    f.pCoreQuotientEquiv hf hk (QuotientGroup.mk' (pCore p X) x) =
      QuotientGroup.mk' (pCore p Y) (f x) := rfl

end MonoidHom

namespace MulEquiv
open Subgroup
variable {X Y : Type*} [Group X] [Group Y] [Finite X]

/-- An isomorphism restricts to the canonical solvable residuals. -/
noncomputable def solvableResidualEquiv (e : X ≃* Y) :
    solvableResidual X ≃* solvableResidual Y :=
  MulEquiv.ofBijective e.toMonoidHom.solvableResidualMap ⟨by
    intro x y h
    exact Subtype.ext (e.injective (congrArg Subtype.val h)),
    e.toMonoidHom.solvableResidualMap_surjective e.surjective⟩

@[simp] theorem solvableResidualEquiv_apply (e : X ≃* Y) (x : solvableResidual X) :
    (e.solvableResidualEquiv x : Y) = e x := rfl

end MulEquiv
