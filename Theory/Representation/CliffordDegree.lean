module
public import Theory.Representation.NormalConstituentDisplacement.FixedLine
public import Mathlib.LinearAlgebra.Projection

/-!
# Equal degrees in Clifford restriction

The constituents of an irreducible representation restricted to a normal
subgroup have equal dimension. Conjugates of one constituent span the whole
space. Projection onto another constituent is therefore nonzero on some
conjugate; simplicity makes that restricted projection an isomorphism.

Source: Isaacs, Character Theory of Finite Groups, Theorem 6.5. The actual
consumer is Chapter10's original constrained binary moved-module analysis.
-/

public noncomputable section
open scoped MonoidAlgebra
open Representation
namespace Representation
variable {k H V : Type*} [Field k] [Group H] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- Every two simple constituents of a normal restriction have equal degree. -/
theorem normal_constituent_finrank_eq
    (ρ : Representation k H V) (hi : IsIrreducible ρ)
    (K : Subgroup H) [K.Normal]
    (A B : Subrepresentation (ρ.comp K.subtype))
    (hA : IsIrreducible A.toRepresentation) (hB : IsIrreducible B.toRepresentation) :
    Module.finrank k A.toSubmodule = Module.finrank k B.toSubmodule := by
  let := NormalConstituentDisplacement.restriction_semisimple ρ hi K
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ.comp K.subtype)
  obtain ⟨C,hC⟩ := exists_isCompl (e A)
  have hAt := (e.isAtom_iff A).mpr ((Subrepresentation.irreducible_iff_isAtom A).mp hA)
  let : IsSimpleModule k[K] (e A) := isSimpleModule_iff_isAtom.mpr hAt
  have hex : ∃ g : H, ¬ e (conjugateSubrepresentation ρ K B g) ≤ C := by
    by_contra! hn
    have ht := congrArg e (iSup_conjugateSubrepresentations_eq_top ρ K hi B hB)
    rw [e.map_iSup,e.map_top] at ht
    have hc : C = ⊤ := top_unique (ht ▸ iSup_le hn)
    exact hAt.ne_bot (by simpa only [hc,inf_top_eq] using hC.inf_eq_bot)
  obtain ⟨g,hg⟩ := hex
  let B' := conjugateSubrepresentation ρ K B g
  have hB' : IsIrreducible B'.toRepresentation :=
    (Subrepresentation.irreducible_iff_isAtom B').mpr
      (by simpa only [conjugateSubrepresentationOrderIso_apply,inv_inv] using
        (((conjugateSubrepresentationOrderIso ρ K g⁻¹).isAtom_iff B).mpr
          ((Subrepresentation.irreducible_iff_isAtom B).mp hB)))
  let : IsSimpleModule k[K] (e B') := isSimpleModule_iff_isAtom.mpr
    ((e.isAtom_iff B').mpr ((Subrepresentation.irreducible_iff_isAtom B').mp hB'))
  let p := (e A).projectionOnto C hC
  let f := p.comp (e B').subtype
  have hf : f ≠ 0 := by
    intro hz
    apply hg
    intro w hw
    have he : p w = 0 := congrArg (fun l : (e B') →ₗ[k[K]] (e A) => l ⟨w,hw⟩) hz
    exact (Submodule.projectionOnto_apply_eq_zero_iff hC).mp he
  let F : (e B') ≃ₗ[k[K]] (e A) := LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf)
  obtain ⟨E⟩ := (isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv B' A).mpr ⟨F⟩
  exact E.toLinearEquiv.finrank_eq.symm.trans
    (conjugateSubrepresentationEquiv ρ K B g).toLinearEquiv.finrank_eq
end Representation
