module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.FaithfulSections
public import Theory.Representation.BinaryOffender.TwoSectionBudget

/-!
# A fixed actor excludes repeated faithful non-FF local types

If a semisimple isotypic normal-subgroup restriction is reducible, an
explicit elementary two-subgroup fixes two simple sections of the same type.
Faithfulness on the normal subgroup and injective conjugation make the actor
faithful on both. Their non-FF images each use more than the actor rank,
contradicting a fixed-codimension budget of twice that rank.

The actor is retained explicitly: in the original application it is chosen
from the starred family, where conjugation faithfulness is available.
Source: Aschbacher–Smith D.3.9(1), printed pp.199–200.
-/

public noncomputable section
open scoped MonoidAlgebra
open Subgroup Representation
namespace Representation.BinaryOffender.Homogeneous
universe u v
variable {G : Type u} [Group G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V] [Nontrivial V]

/-- A local-type certificate for both selected sections contradicts a
reducible restriction at the given actor's two-rank budget. -/
theorem irreducible_of_faithful_nonFF_sections
    (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]
    [IsSemisimpleModule (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))]
    (S : Subrepresentation (ρ.comp N.subtype))
    (htype : IsIsotypicOfType (ZMod 2)[N]
      (Representation.asModule (ρ.comp N.subtype)) S.asSubmodule)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A)
    (hconj : Function.Injective ((MulAut.conjNormal : G →* MulAut N).comp A.subtype))
    (hsection :
      let H := N ⊔ A
      let B := N.subgroupOf H
      let e := subgroupOfEquivOfLe (show N ≤ H from le_sup_left)
      ∀ (W : Type v) [AddCommGroup W] [Module (ZMod 2) W]
        (σ : Representation (ZMod 2) H W) (X : Subrepresentation σ),
        Nonempty ((X.compActors B.subtype).asSubmodule ≃ₗ[(ZMod 2)[B]]
          (S.compActors e.toMonoidHom).asSubmodule) →
        Function.Injective (X.toRepresentation.comp (inclusion (show N ≤ H from le_sup_left))) ∧
        ¬ IsFFModule (imageRepresentation X.toRepresentation)) :
    Representation.IsIrreducible (ρ.comp N.subtype) := by
  by_contra hred
  let H := N ⊔ A
  let : IsElementaryAbelian 2 A := hA.2
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨U,W,_hU,_hW,heU,heW⟩ :=
    exists_two_restricted_sections_of_isotypic ρ N S htype A
      (IsElementaryAbelian.isPGroup 2 A) hred
  obtain ⟨hfU,hnU⟩ := hsection V (ρ.comp H.subtype) U heU
  obtain ⟨hfW,hnW⟩ := hsection _ U.quotientRepresentation W heW
  have hfaU := faithful_on_actor_of_faithful_normal N A H le_sup_left le_sup_right
    U.toRepresentation hfU hconj
  have hfaW := faithful_on_actor_of_faithful_normal N A H le_sup_left le_sup_right
    W.toRepresentation hfW hconj
  exact (not_lt_of_ge hsmall)
    (twice_rank_lt_fixedCodim_of_restricted_nonFF_submodule_sections ρ
      hA le_sup_right U W hfaU hfaW hnU hnW)

end Representation.BinaryOffender.Homogeneous
