module
public import Theory.Representation.BinaryOffender.FixedSpaceMovement
public import Theory.Representation.ConjugateRep
public import Theory.Representation.SubrepresentationLattice

/-!
# Faithful normal constituents in a restricted action

A subgroup commuting with C preserves C's fixed space. On any invariant
subspace faithful for a normal subgroup X, the pointwise actor kernel
centralizes X. A simple X-submodule that is moved to a distinct conjugate
injects into the quotient of a containing invariant space by the actor's
fixed vectors. Thus a strict dimension gap proves constituent invariance.

These statements retain the actual subspace action and its pointwise kernel.
They are used to select a stable Suzuki-pair constituent in the original
Chapter 10 Hall context, after D.2.7's strict fixed-space ratio decrease.
Source: Aschbacher--Smith D.3.7--9, printed pp.197--201; Clifford conjugation
is the small-displacement argument of 15.3.57(2), p.1148.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A commuting subgroup preserves the original fixed space. -/
theorem centralizer_le_fixedSpace_stabilizer (C X : Subgroup G)
    (hXC : X ≤ centralizer (C : Set G)) :
    X ≤ subspaceStabilizer ρ (fixedSpace ρ C) := by
  apply le_subspaceStabilizer
  intro x hx v hv c
  change ρ (c : G) (ρ x v) = ρ x v
  rw [← Module.End.mul_apply, ← map_mul, hXC hx c c.property,
    map_mul, Module.End.mul_apply]
  exact congrArg (ρ x) (hv c)

/-- An actor fixing a faithful normal-subgroup submodule centralizes that subgroup. -/
theorem subspaceKernel_le_centralizer_of_faithful
    (X A : Subgroup G) [X.Normal] (W : Submodule (ZMod 2) V)
    (hX : X ≤ subspaceStabilizer ρ W)
    (hf : Function.Injective (invariantSubspace ρ X W hX).toRepresentation) :
    subspaceKernel ρ W A ≤ A ⊓ centralizer (X : Set G) := by
  intro b hb
  refine ⟨hb.1, ?_⟩
  intro x hx
  have hbx : b * x * b⁻¹ = x := by
    have hbxX : b * x * b⁻¹ ∈ X := (inferInstance : X.Normal).conj_mem x hx b
    suffices he : (⟨b * x * b⁻¹, hbxX⟩ : X) = ⟨x, hx⟩ from
      congrArg Subtype.val he
    apply hf
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change ρ (b * x * b⁻¹) (w : V) = ρ x w
    have hbi := (subspaceKernel ρ W A).inv_mem hb
    simp only [map_mul, Module.End.mul_apply, hbi.2 w w.property]
    exact hb.2 _ ((hX hx w).2 w.property)
  exact (mul_inv_eq_iff_eq_mul.mp hbx).symm

variable [FiniteDimensional (ZMod 2) V]

/-- Small displacement on an invariant containing space fixes each sufficiently
large normal-subgroup constituent inside it. No invariance of that constituent
under the actor is assumed. -/
theorem map_constituent_eq_self_of_restricted_codim_lt
    (X A : Subgroup G) [X.Normal]
    (W : Submodule (ZMod 2) V) (hA : A ≤ subspaceStabilizer ρ W)
    (U : Subrepresentation (ρ.comp X.subtype)) (hU : U.toRepresentation.IsIrreducible)
    (hUW : U.toSubmodule ≤ W)
    (hsmall : fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) <
      Module.finrank (ZMod 2) U.toSubmodule) :
    ∀ a ∈ A, U.toSubmodule.map (ρ a) = U.toSubmodule := by
  intro a ha
  by_contra hne
  let Ua := conjugateSubrepresentationOrderIso ρ X a U
  have hUa : IsAtom Ua := ((conjugateSubrepresentationOrderIso ρ X a).isAtom_iff U).mpr
    ((Subrepresentation.irreducible_iff_isAtom U).mp hU)
  have hne' : Ua ≠ U := by
    intro he
    apply hne
    simpa only [Ua, conjugateSubrepresentationOrderIso_toSubmodule] using
      congrArg Subrepresentation.toSubmodule he
  have hd : Disjoint U.toSubmodule (U.toSubmodule.map (ρ a)) := by
    rw [disjoint_iff]
    have he := congrArg Subrepresentation.toSubmodule
      (((Subrepresentation.irreducible_iff_isAtom U).mp hU).disjoint_of_ne hUa hne'.symm).eq_bot
    change U.toSubmodule ⊓ Ua.toSubmodule = ⊥ at he
    simpa only [Ua, conjugateSubrepresentationOrderIso_toSubmodule] using he
  let τ := subspaceImageRepresentation ρ W
  let B := restrictedSubgroup ρ W A
  let f : U.toSubmodule →ₗ[ZMod 2] W ⧸ fixedSpace τ B :=
    (fixedSpace τ B).mkQ.comp (Submodule.inclusion hUW)
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    have hw : (⟨(v : V), hUW v.property⟩ : W) ∈ fixedSpace τ B :=
      (Submodule.Quotient.mk_eq_zero _).mp hv
    have hvA : (v : V) ∈ fixedSpace ρ A :=
      ((restrictedFixedSpaceEquiv ρ W A hA) ⟨_, hw⟩).property.2
    have hm : (v : V) ∈ U.toSubmodule.map (ρ a) :=
      ⟨v, v.property, hvA ⟨a, ha⟩⟩
    exact Subtype.ext ((Submodule.disjoint_def.mp hd) _ v.property hm)
  exact (not_le_of_gt hsmall) (LinearMap.finrank_le_finrank_of_injective hf)

end Representation.BinaryOffender
