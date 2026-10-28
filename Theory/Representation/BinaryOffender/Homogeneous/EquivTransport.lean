module

public import Theory.Representation.BinaryOffender.Homogeneous.OrbitConsequences
public import Theory.Representation.SolvableDimension

/-!
# Homogeneous components under specified module equivalences

The existing invariant-subspace order isomorphism restricts to an
intertwining equivalence on each constituent. It therefore preserves
module isomorphism types and their full homogeneous components.

Source application: Aschbacher–Smith, 3.2.2(3), combined manuscript of
1 March 2004, printed p.579, retaining the literal centralizer quotient.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender.Homogeneous
namespace Representation.BinaryOffender.Homogeneous
variable {G V U : Type*} [Group G] {X : Subgroup G}
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup U] [Module (ZMod 2) U]
  {ρ : Representation (ZMod 2) X V} {σ : Representation (ZMod 2) X U}

noncomputable def equivSubrepresentation (e : ρ ≃ₗ σ) (A : Subrepresentation ρ) :
    A.toRepresentation ≃ₗ ((Representation.subrepresentationOrderIsoOfEquiv e) A).toRepresentation :=
  Representation.RepEquiv.mk (Submodule.equivMapOfInjective e.toLinearMap e.injective A.toSubmodule)
    (fun g => by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact LinearMap.congr_fun (e.isIntertwining' g) v)

theorem sameModule_equiv_iff (e : ρ ≃ₗ σ) (A B : Subrepresentation ρ) :
    SameModule ((Representation.subrepresentationOrderIsoOfEquiv e) A)
      ((Representation.subrepresentationOrderIsoOfEquiv e) B) ↔ SameModule A B := by
  simp only [sameModule_iff_repEquiv]
  constructor
  · rintro ⟨a⟩
    exact ⟨((equivSubrepresentation e A).trans a).trans (equivSubrepresentation e B).symm⟩
  · rintro ⟨a⟩
    exact ⟨((equivSubrepresentation e A).symm.trans a).trans (equivSubrepresentation e B)⟩

/-- A specified module equivalence preserves the full homogeneous component. -/
theorem homogeneousPart_map_equiv (e : ρ ≃ₗ σ) (A : Subrepresentation ρ) :
    (homogeneousPart A ⊤).map e.toLinearMap =
      homogeneousPart ((Representation.subrepresentationOrderIsoOfEquiv e) A) ⊤ := by
  let F := Representation.subrepresentationOrderIsoOfEquiv e
  simp only [homogeneousPart, Submodule.map_iSup]
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hB => ?_
    exact le_iSup_of_le (F B) (le_iSup_of_le
      ⟨le_top, (sameModule_equiv_iff e A B).mpr hB.2⟩ le_rfl)
  · refine iSup_le fun B => iSup_le fun hB => ?_
    obtain ⟨C, rfl⟩ := F.surjective B
    exact le_iSup_of_le C (le_iSup_of_le
      ⟨le_top, (sameModule_equiv_iff e A C).mp hB.2⟩ le_rfl)

end Representation.BinaryOffender.Homogeneous
