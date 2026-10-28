module
public import Theory.Representation.CubicClifford.Inertia.Isotypic
public import Theory.LinearAlgebra.RankOneInvariantPairSwap
public import Theory.Representation.RankOneSymplectic.Basic

/-!
# Isotypic components moved by rank-one generators

Normal-subgroup conjugation permutes canonical isotypic components. Distinct
components are disjoint, so a rank-one operator moving one injects that component
into its displacement line. A component fixed by all generators is fixed by the
whole group and therefore fills an irreducible ambient module.

These are the component reductions for the homogeneous normal restriction used
after Aschbacher--Smith G.4.6, printed pp.339--340.
-/

public noncomputable section
open Subgroup Module
open scoped MonoidAlgebra
namespace Representation.RankOneSymplectic.Homogeneous
open CubicClifford.Inertia
variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]

theorem component_eq_or_disjoint (ρ : Representation F G V) (A B : Subrepresentation ρ)
    (hA : A.toRepresentation.IsIrreducible) (hB : B.toRepresentation.IsIrreducible) :
    component ρ A = component ρ B ∨ Disjoint (component ρ A) (component ρ B) := by
  by_cases he : Nonempty (A.toRepresentation ≃ₗ B.toRepresentation)
  · exact Or.inl (component_eq_of_equiv ρ he.some)
  · exact Or.inr (component_disjoint ρ A B hA hB he)

theorem stable_of_generators (ρ : Representation F G V) (N : Subgroup G) [N.Normal]
    (D : Set G) (A : Subrepresentation (ρ.comp N.subtype))
    (h : ∀ d∈D, conjugateSubrepresentationOrderIso ρ N d A=A)
    {g : G} (hg : g∈closure D) : conjugateSubrepresentationOrderIso ρ N g A=A := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => exact conjugateSubrepresentationOrderIso_one ρ N A
  | mul g k _ _ hg hk => rw [conjugateSubrepresentationOrderIso_mul,hk,hg]
  | inv g _ hg =>
    have hh := congrArg (conjugateSubrepresentationOrderIso ρ N g⁻¹) hg
    rw [←conjugateSubrepresentationOrderIso_mul,inv_mul_cancel,
      conjugateSubrepresentationOrderIso_one] at hh
    exact hh.symm

theorem eq_top_of_stable (ρ : Representation F G V) [ρ.IsIrreducible]
    (N : Subgroup G) [N.Normal] (A : Subrepresentation (ρ.comp N.subtype))
    (hA : A≠⊥) (hs : ∀ g, conjugateSubrepresentationOrderIso ρ N g A=A) : A=⊤ := by
  let J : Subrepresentation ρ := ⟨A.toSubmodule,fun g v hv => by
    have hm := congrArg Subrepresentation.toSubmodule (hs g)
    rw [conjugateSubrepresentationOrderIso_toSubmodule] at hm
    exact hm ▸ (show ρ g v∈A.toSubmodule.map (ρ g) from ⟨v,hv,rfl⟩)⟩
  have hn : J≠⊥ := fun h => hA (Subrepresentation.toSubmodule_injective
    (show A.toSubmodule=⊥ from congrArg Subrepresentation.toSubmodule h))
  apply Subrepresentation.toSubmodule_injective
  exact congrArg (fun K : Subrepresentation ρ => K.toSubmodule)
    ((IsSimpleOrder.eq_bot_or_eq_top J).resolve_left hn)

theorem exists_moving_generator (ρ : Representation F G V) [ρ.IsIrreducible]
    (N : Subgroup G) [N.Normal] (D : Set G) (hgen : closure D=⊤)
    (A : Subrepresentation (ρ.comp N.subtype)) (hn : A≠⊥) (ht : A≠⊤) :
    ∃ d∈D, conjugateSubrepresentationOrderIso ρ N d A≠A := by
  by_contra! h
  exact ht (eq_top_of_stable ρ N A hn (fun g =>
    stable_of_generators ρ N D A h (hgen ▸ mem_top g)))

variable [FiniteDimensional F V]
theorem moved_component_finrank_le_one (ρ : Representation F G V)
    (N : Subgroup G) [N.Normal] (A : Subrepresentation (ρ.comp N.subtype))
    (hA : A.toRepresentation.IsIrreducible) (d : G)
    (hr : finrank F (LinearMap.range (ρ d-LinearMap.id))=1)
    (hne : conjugateSubrepresentationOrderIso ρ N d
      (component (ρ.comp N.subtype) A)≠component (ρ.comp N.subtype) A) :
    finrank F (component (ρ.comp N.subtype) A).toSubmodule≤1 := by
  let c := conjugateSubrepresentationOrderIso ρ N d
  have ha : (c A).toRepresentation.IsIrreducible :=
    (Subrepresentation.irreducible_iff_isAtom _).mpr
      ((c.isAtom_iff A).mpr ((Subrepresentation.irreducible_iff_isAtom A).mp hA))
  have hd := (component_eq_or_disjoint (ρ.comp N.subtype) A (c A) hA ha).resolve_left
    (fun h => hne ((conjugate_component ρ N d A).trans h.symm))
  have hd' : Disjoint (component (ρ.comp N.subtype) A).toSubmodule
      (c (component (ρ.comp N.subtype) A)).toSubmodule := by
    rw [conjugate_component]
    rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule hd.eq_bot
  have h := LinearEquiv.finrank_le_displacement_of_disjoint_image
    (LinearEquiv.ofBijective (ρ d) (ρ.apply_bijective d)) _ _ hd' (fun x hx => by
      rw [conjugateSubrepresentationOrderIso_toSubmodule]
      exact ⟨x,hx,rfl⟩)
  exact h.trans_eq hr
end Representation.RankOneSymplectic.Homogeneous
