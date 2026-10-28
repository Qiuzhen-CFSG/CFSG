module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.MultiplicityCost
public import Theory.Representation.BinaryOffender.MarkedImageRank

/-!
# Multiplicity costs for a marked normal action with a kernel

All simple sections of an isotypic normal restriction retain the same faithful
model marking. Their full ambient images lie in that model's normalizer.
Combining invariant-section selection with kernel inclusion costs at least the
component-image rank on each section, and strictly more for a non-FF model.
No faithfulness of the whole elementary actor on a single factor is required.

The natural and Hermitian constituent consumers jointly exclude the genuine
two-kernel square. Source: Aschbacher--Smith A.1.42 and D.3.7, pp.32,199.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
open scoped MonoidAlgebra
namespace Representation.BinaryOffender.Homogeneous
universe u v w
variable {G : Type u} [Group G] [Finite G] {J : Type*} [Group J]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]

theorem marked_isotypic_multiplicity_cost
    (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]
    [IsSemisimpleModule (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))]
    (μ : Representation (ZMod 2) J W) (hμ : Function.Injective μ)
    (q : N →* J) (hq : Function.Surjective q) (α : G →* MulAut J)
    (hα : ∀ (a : G) (k : N), q (MulAut.conjNormal a k) = α a (q k))
    (I : Subrepresentation (ρ.comp N.subtype)) (hI : I.toRepresentation.IsIrreducible)
    (bI : Representation.Equiv I.toRepresentation (μ.comp q))
    (htype : IsIsotypicOfType (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype)) I.asSubmodule)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (k : ℕ) (hd : k * Module.finrank (ZMod 2) I.toSubmodule ≤ Module.finrank (ZMod 2) V)
    (hn : ¬ IsStrongFFModule (normalizerRepresentation μ)) :
    k * rank (A.map α) ≤ fixedCodim ρ A ∧
      (0 < rank (A.map α) → ¬ IsFFModule (normalizerRepresentation μ) →
        k * (rank (A.map α)+1) ≤ fixedCodim ρ A) := by
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let H := N ⊔ A
  let B := N.subgroupOf H
  let P := A.subgroupOf H
  let e := subgroupOfEquivOfLe (show N ≤ H from le_sup_left)
  let σ := ρ.comp H.subtype
  let I' := I.compActors e.toMonoidHom
  let q' := q.comp e.toMonoidHom
  let α' := α.comp H.subtype
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.subgroupOf (show A ≤ H from le_sup_right)
  have hα' (a : H) (b : B) : q' (MulAut.conjNormal a b) = α' a (q' b) := hα a.val (e b)
  let : IsSemisimpleModule (ZMod 2)[B] (Representation.asModule (σ.comp B.subtype)) :=
    comp_semisimple_of_surjective (ρ.comp N.subtype) e.toMonoidHom e.surjective
  have ht' : IsIsotypicOfType (ZMod 2)[B] (Representation.asModule (σ.comp B.subtype)) I'.asSubmodule :=
    isotypic_comp_equiv (ρ.comp N.subtype) e I htype
  have hmap : P.map α' = A.map α := by
    change (A.subgroupOf H).map (α.comp H.subtype) = A.map α
    rw [←Subgroup.map_map,map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right)]
  have hc : fixedCodim σ P = fixedCodim ρ A := fixedCodim_subgroupOf ρ (show A ≤ H from le_sup_right)
  let := hI
  let : Nontrivial I.toSubmodule := Subrepresentation.irreducible_module_nontrivial I.toRepresentation
  have hpos : 0 < Module.finrank (ZMod 2) I'.asSubmodule :=
    (show 0 < Module.finrank (ZMod 2) I.toSubmodule from Module.finrank_pos)
  have hd' : k * Module.finrank (ZMod 2) I'.asSubmodule ≤ Module.finrank (ZMod 2) V := hd
  have hsec {Y : Type v} [AddCommGroup Y] [Module (ZMod 2) Y]
      (τ : Representation (ZMod 2) H Y) (X : Subrepresentation τ)
      (hX : Nonempty ((X.compActors B.subtype).asSubmodule ≃ₗ[(ZMod 2)[B]] I'.asSubmodule)) :
      rank (P.map α') ≤ fixedCodim X.toRepresentation P ∧
        (0 < rank (P.map α') → ¬ IsFFModule (normalizerRepresentation μ) →
          rank (P.map α')+1 ≤ fixedCodim X.toRepresentation P) := by
    let er := equiv_of_asSubmodule_equiv (τ.comp B.subtype)
      ((ρ.comp N.subtype).comp e.toMonoidHom) (X.compActors B.subtype) I' hX.some
    let b' : Representation.Equiv I'.toRepresentation (μ.comp q') := {
      __ := bI.toLinearEquiv
      isIntertwining' b := bI.isIntertwining' (e b) }
    let b := er.trans b'
    have hk := marked_normal_action_kernel_le X.toRepresentation B μ hμ q'
      (hq.comp e.surjective) α' hα' b
    have hi : B.subtype.range = B := range_subtype B
    let : B.subtype.range.Normal := hi.symm ▸ (inferInstance : B.Normal)
    refine ⟨image_rank_le_fixedCodim_of_nonStrong X.toRepresentation α' hk P
      (image_not_strong_of_marked_normal_range X.toRepresentation B.subtype μ q'
        (hq.comp e.surjective) b hn),?_⟩
    intro hp hff
    exact image_rank_lt_fixedCodim_of_nonFF X.toRepresentation α' hk P hp
      (not_isFFModule_image_of_marked_normal_range X.toRepresentation B.subtype μ q'
        (hq.comp e.surjective) b hff)
  constructor
  · have hh := section_cost_le_fixedCodim_of_degree B P (IsElementaryAbelian.isPGroup 2 P)
      (codisjoint_subgroupOf_sup N A).eq_top (rank (P.map α')) hpos
      (fun Y _ _ τ X hX => (hsec τ X hX).1) k σ ht' hd'
    rwa [hmap,hc] at hh
  · intro hp hff
    have hh := section_cost_le_fixedCodim_of_degree B P (IsElementaryAbelian.isPGroup 2 P)
      (codisjoint_subgroupOf_sup N A).eq_top (rank (P.map α')+1) hpos
      (fun Y _ _ τ X hX => (hsec τ X hX).2 (hmap.symm ▸ hp) hff) k σ ht' hd'
    rwa [hmap,hc] at hh
end Representation.BinaryOffender.Homogeneous
