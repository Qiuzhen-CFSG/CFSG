module
public import Theory.Representation.QuadraticFourGroup.Basic
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.RepresentationTheory.Semisimple

/-!
# Irreducible sections of semisimple representations

An irreducible invariant subquotient of a semisimple representation is
isomorphic to an actual subrepresentation. Complement the kernel in the
ambient module and intersect that complement with the section numerator.
The original quotient map restricts to the required equivariant isomorphism.

This is the semisimple step in the occurrence argument used for the natural
component supports of Aschbacher--Smith 14.6.22, printed p.1038. It does not
split any central cover in the original, possibly nonsemisimple module.
-/

public noncomputable section
open Representation
namespace Representation.QuadraticFourGroup
variable {k D V W : Type*} [Field k] [Group D]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

set_option backward.isDefEq.respectTransparency false in
/-- Realize the given irreducible section inside its semisimple ambient action. -/
theorem IsIrreducibleSection.exists_equiv_subrepresentation
    {ρ : Representation k D V} {σ : Representation k D W}
    [IsSemisimpleRepresentation ρ] (hs : IsIrreducibleSection ρ σ) :
    ∃ J : Subrepresentation ρ, Nonempty (J.toRepresentation.Equiv σ) := by
  obtain ⟨_, U, N, ⟨e⟩⟩ := hs
  let R : Subrepresentation ρ := {
    toSubmodule := N.toSubmodule.map U.toSubmodule.subtype
    apply_mem_toSubmodule g v hv := by
      obtain ⟨u, hu, rfl⟩ := hv
      exact ⟨U.toRepresentation g u, N.apply_mem_toSubmodule g hu, rfl⟩ }
  have hRU : R ≤ U := Submodule.map_subtype_le _ _
  obtain ⟨C, hC⟩ := exists_isCompl R
  let J := U ⊓ C
  let f : J.toRepresentation.IntertwiningMap N.quotientRepresentation := {
    toLinearMap := N.toSubmodule.mkQ.comp
      (Submodule.inclusion (show J.toSubmodule ≤ U.toSubmodule from inf_le_left))
    isIntertwining' := fun _ => rfl }
  have hfi : Function.Injective f := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have hvN : (⟨v, v.property.1⟩ : U) ∈ N :=
      (Submodule.Quotient.mk_eq_zero N.toSubmodule).mp hv
    have hvR : (v : V) ∈ R := ⟨⟨v, v.property.1⟩, hvN, rfl⟩
    have hz : (v : V) ∈ (R ⊓ C).toSubmodule := ⟨hvR, v.property.2⟩
    rw [hC.inf_eq_bot] at hz
    exact Subtype.ext hz
  have hfs : Function.Surjective f := by
    intro w
    obtain ⟨u, rfl⟩ := N.toSubmodule.mkQ_surjective w
    have hu : (u : V) ∈ R.toSubmodule ⊔ C.toSubmodule := by
      change (u : V) ∈ (R ⊔ C).toSubmodule
      rw [hC.sup_eq_top]
      trivial
    obtain ⟨r, hr, c, hc, heq⟩ := Submodule.mem_sup.mp hu
    have hcU : c ∈ U := by
      have he : c = (u : V) - r := by rw [← heq]; abel
      rw [he]
      exact U.toSubmodule.sub_mem u.property (hRU hr)
    refine ⟨⟨c, hcU, hc⟩, ?_⟩
    change N.toSubmodule.mkQ ⟨c, hcU⟩ = N.toSubmodule.mkQ u
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    obtain ⟨r', hr', her⟩ := hr
    change (r' : V) = r at her
    have he : (⟨c, hcU⟩ : U.toSubmodule) - u = -r' := by
      apply Subtype.ext
      change c - (u : V) = -(r' : V)
      rw [← heq, her]
      abel
    rw [he]
    exact N.toSubmodule.neg_mem hr'
  let ef : J.toRepresentation.Equiv N.quotientRepresentation :=
    Representation.Equiv.mk (LinearEquiv.ofBijective f.toLinearMap ⟨hfi, hfs⟩) f.isIntertwining'
  exact ⟨J, ⟨ef.trans e⟩⟩

end Representation.QuadraticFourGroup
