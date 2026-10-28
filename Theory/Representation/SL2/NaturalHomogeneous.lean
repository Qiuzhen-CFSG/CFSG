module
public import Theory.Representation.SL2.NaturalMultiplicity
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.NormalType

/-!
# Natural constituents under the full normalizer

The canonical action of Aut(SL₂) corrects an ambient conjugation to an
intertwiner of natural constituents. Thus every ambient conjugate has the
same module type, including when the actor has odd field automorphisms.
Clifford generation in an irreducible ambient action then makes the whole
normal restriction homogeneous.

Source: Aschbacher--Smith D.3.21(3), printed pp.205--206.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender.Homogeneous
open scoped MatrixGroups
namespace Representation.SL2AutomorphismNatural
variable {F A V : Type*} [Field F] [Finite F] [CharP F 2] [Group A]
  [AddCommGroup V] [Module (ZMod 2) V]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- A natural constituent has invariant type under every compatible ambient
normalizer, including odd field automorphisms. -/
theorem natural_sameModule_conjugate
    (ρ : Representation (ZMod 2) A V) (K : Subgroup A) [K.Normal]
    (q : K →* SL(2,F)) (α : A → MulAut (SL(2,F)))
    (hα : ∀ (a : A) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp K.subtype))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = I.toRepresentation k (E v))
    (a : A) : SameModule I (conjugateSubrepresentationOrderIso ρ K a I) := by
  let J := conjugateSubrepresentationOrderIso ρ K a I
  let b := LinearEquiv.ofBijective (action (α a⁻¹)) (action.apply_bijective (α a⁻¹))
  let f := (I.toSubmodule.equivMapOfInjective (ρ a) (ρ.apply_bijective a).injective).trans
    (LinearEquiv.ofEq _ _ (conjugateSubrepresentationOrderIso_toSubmodule ρ K a I).symm)
  have hf (v : I.toSubmodule) : (f v : V) = ρ a v := rfl
  have hEs (k : K) (v : I.toSubmodule) :
      E.symm (I.toRepresentation k v) = (q k).val.mulVec (E.symm v) := by
    apply E.injective
    rw [E.apply_symm_apply,hE,E.apply_symm_apply]
  refine ⟨E.symm.trans (b.trans (E.trans f)),?_⟩
  intro k v
  apply Subtype.ext
  change (f (E (action (α a⁻¹) (E.symm (I.toRepresentation k v)))) : V) =
    ρ (k : A) (f (E (action (α a⁻¹) (E.symm v))))
  rw [hEs,action_intertwines,←hα a⁻¹ k,hE,hf,hf]
  change ρ a (ρ ((MulAut.conjNormal a⁻¹ k : K) : A) _) = ρ (k : A) (ρ a _)
  change ρ a (ρ (a⁻¹ * (k : A) * (a⁻¹)⁻¹) _) = _
  simp only [inv_inv,←Module.End.mul_apply,←map_mul,←mul_assoc,mul_inv_cancel,one_mul]
  rfl

/-- Irreducibility of the ambient action makes a natural normal constituent
homogeneous on the whole space; no isotypic decomposition is assumed. -/
theorem homogeneous_natural_of_irreducible
    (ρ : Representation (ZMod 2) A V) [ρ.IsIrreducible]
    (K : Subgroup A) [K.Normal]
    (q : K →* SL(2,F)) (α : A → MulAut (SL(2,F)))
    (hα : ∀ (a : A) (k : K), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp K.subtype)) (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = I.toRepresentation k (E v)) :
    homogeneousPart I ⊤ = ⊤ := by
  apply top_unique
  have hgen := iSup_conjugateSubrepresentations_eq_top ρ K inferInstance I hI
  have hh := congrArg Subrepresentation.toSubmodule hgen
  rw [toSubmodule_iSup] at hh
  change (⨆ a, (conjugateSubrepresentation ρ K I a).toSubmodule) = ⊤ at hh
  conv_lhs => rw [←hh]
  apply iSup_le
  intro a
  have ha : conjugateSubrepresentation ρ K I a =
      conjugateSubrepresentationOrderIso ρ K a⁻¹ I := by
    simp only [conjugateSubrepresentationOrderIso_apply,inv_inv]
  rw [ha]
  exact le_iSup_of_le (conjugateSubrepresentationOrderIso ρ K a⁻¹ I)
    (le_iSup_of_le ⟨le_top,natural_sameModule_conjugate ρ K q α hα I E hE a⁻¹⟩ le_rfl)
end Representation.SL2AutomorphismNatural
