module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalOrthogonality
public import Theory.Representation.BinaryOffender.Basic
/-!
# Moved spaces in the natural six-letter symplectic pairing

Pointwise fixation is equivalent to perpendicular displacement. Applying
that equivalence to a subgroup and taking perpendiculars identifies its
moved space with the perpendicular of its fixed space. Nondegeneracy then
makes moved dimension equal fixed codimension. These identities concern
the original binary natural quotient and its literal permutation action.

Source application: Meierfrankenfeld--Stellmacher (1993), (3.6), p.871.
-/

public section
open BinaryPermutation Representation.BinaryOffender
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing

theorem moved_eq_fixed_orthogonal (A : Subgroup (Equiv.Perm (Fin 6))) :
    subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A =
      form.orthogonal (fixedSpace (naturalRepresentation (Fin 6)) A) := by
  let D := subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A
  have hle : D ≤ form.orthogonal (fixedSpace (naturalRepresentation (Fin 6)) A) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    exact (NaturalOrthogonality.fixes_iff_displacement g
      (fixedSpace (naturalRepresentation (Fin 6)) A)).mp
      (fun x hx => hx ⟨g,hg⟩) v
  have hfix : form.orthogonal D ≤ fixedSpace (naturalRepresentation (Fin 6)) A := by
    intro v hv a
    apply (NaturalOrthogonality.fixes_iff_displacement a.val (form.orthogonal D)).mpr _ v hv
    intro w
    rw [LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl]
    exact Submodule.subset_span ⟨a.val,a.property,w,Submodule.mem_top,rfl⟩
  apply le_antisymm hle
  have hh := LinearMap.BilinForm.orthogonal_le (B := form) hfix
  rw [LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl] at hh
  exact hh

theorem moved_finrank_eq_fixedCodim (A : Subgroup (Equiv.Perm (Fin 6))) :
    Module.finrank (ZMod 2) (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A) =
      fixedCodim (naturalRepresentation (Fin 6)) A := by
  rw [moved_eq_fixed_orthogonal,LinearMap.BilinForm.finrank_orthogonal form_nondegenerate]
  have he := fixedCodim_add_finrank (naturalRepresentation (Fin 6)) A
  omega

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
