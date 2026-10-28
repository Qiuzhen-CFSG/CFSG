module
public import Theory.Representation.QuadraticFourGroup.Basic
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Pulling irreducible sections through an equivariant quotient

An equivariant isomorphism preserves acting-group kernels. For an equivariant
epimorphism, pull back the section numerator and take the kernel of its map
to the old quotient. The first isomorphism theorem identifies the new literal
subquotient with the prescribed irreducible action.

This retains the exact quotient action in the14.6.22 FF exclusion, whose
consumer is ComponentSupports.Modules.Recognition.QuotientNonFF. Source:
Aschbacher--Smith F.9.18(6--7), printed pp.326,1038.
-/

public section
open Representation
namespace Representation.QuadraticFourGroup
variable {k D V W X : Type*} [Field k] [Group D]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X]
  {ρ : Representation k D V} {σ : Representation k D W} {τ : Representation k D X}

/-- An equivariant isomorphism preserves every acting-group kernel element. -/
theorem ker_le_of_equiv (b : ρ.Equiv σ) : ρ.ker ≤ σ.ker := by
  intro g hg
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := b.toLinearEquiv.surjective v
  have he := LinearMap.congr_fun (b.isIntertwining' g) w
  change b (ρ g w) = σ g (b w) at he
  rw [hg] at he
  exact he.symm

set_option backward.isDefEq.respectTransparency false in
/-- Pull an actual irreducible section through an equivariant epimorphism.
The new numerator is the literal inverse image and the denominator is the
kernel of the induced map to the original section. -/
theorem IsIrreducibleSection.of_surjective_intertwining
    (q : ρ.IntertwiningMap σ) (hq : Function.Surjective q)
    (hs : IsIrreducibleSection σ τ) : IsIrreducibleSection ρ τ := by
  obtain ⟨hi,U,N,⟨e⟩⟩ := hs
  let S : Subrepresentation ρ := {
    toSubmodule := U.toSubmodule.comap q.toLinearMap
    apply_mem_toSubmodule g v hv := by
      change q (ρ g v) ∈ U
      rw [q.isIntertwining]
      exact U.apply_mem_toSubmodule g hv }
  let f : S.toRepresentation.IntertwiningMap N.quotientRepresentation := {
    toLinearMap := N.toSubmodule.mkQ.comp
      ((q.toLinearMap.comp S.toSubmodule.subtype).codRestrict U.toSubmodule (fun v => v.property))
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      change N.toSubmodule.mkQ ⟨q (ρ g v.val),_⟩ =
        N.toSubmodule.mkQ ⟨σ g (q v.val),_⟩
      congr 1
      exact Subtype.ext (LinearMap.congr_fun (q.isIntertwining' g) v.val) }
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨u,rfl⟩ := N.toSubmodule.mkQ_surjective x
    obtain ⟨v,hv⟩ := hq u.val
    refine ⟨⟨v,show q v ∈ U from hv.symm ▸ u.property⟩,?_⟩
    change N.toSubmodule.mkQ ⟨q v,_⟩ = N.toSubmodule.mkQ u
    exact congrArg N.toSubmodule.mkQ (Subtype.ext hv)
  let d : f.ker.quotientRepresentation.Equiv N.quotientRepresentation := {
    toLinearEquiv := f.toLinearMap.quotKerEquivOfSurjective hf
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      induction v using Submodule.Quotient.induction_on with
      | _ v => exact LinearMap.congr_fun (f.isIntertwining' g) v }
  exact ⟨hi,S,f.ker,⟨d.trans e⟩⟩

end Representation.QuadraticFourGroup
