module
public import Theory.Representation.BinaryOffender.TwoSectionBudget
public import Theory.Representation.BinaryOffender.Embedding
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# The fixed-codimension budget for disjoint invariant subspaces

The sum of two disjoint invariant subspaces embeds their direct product into
the ambient module. Fixed codimensions add on the product and cannot increase
under that embedding. Thus two faithful non-FF subspaces each cost more than
the rank of the same elementary actor, exceeding a budget of twice that rank.

This is the direct-subspace version of the two-section inequality used in
Aschbacher--Smith D.3.9 and F.9.18, printed pp.199--200,325--326.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryOffender
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)

/-- Two disjoint invariant subspaces with faithful non-FF actions cost more
than twice the rank of the same elementary actor. -/
theorem twice_rank_lt_fixedCodim_of_disjoint_nonFF_subrepresentations
    (U W : Subrepresentation ρ) (hd : Disjoint U.toSubmodule W.toSubmodule)
    {A : Subgroup D} (hA : IsElementaryTwo A)
    (hU : ∀ a ∈ A, (∀ v, U.toRepresentation a v = v) → a = 1)
    (hW : ∀ a ∈ A, (∀ v, W.toRepresentation a v = v) → a = 1)
    (hnU : ¬ IsFFModule (imageRepresentation U.toRepresentation))
    (hnW : ¬ IsFFModule (imageRepresentation W.toRepresentation)) :
    2 * rank A < fixedCodim ρ A := by
  let f : U.toSubmodule × W.toSubmodule →ₗ[ZMod 2] V := U.toSubmodule.subtype.coprod W.toSubmodule.subtype
  have hi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    change LinearMap.ker (U.toSubmodule.subtype.coprod W.toSubmodule.subtype) = ⊥
    rw [LinearMap.ker_coprod_of_disjoint_range,Submodule.ker_subtype,
      Submodule.ker_subtype,Submodule.prod_bot]
    simpa only [Submodule.range_subtype] using hd
  have hact (g : D) (v : U.toSubmodule × W.toSubmodule) :
      ρ g (f v) = f ((U.toRepresentation.prod W.toRepresentation) g v) := map_add (ρ g) _ _
  have hb := fixedCodim_map_le_of_embedding ρ
    (U.toRepresentation.prod W.toRepresentation) (MonoidHom.id _) f hi hact A
  rw [Subgroup.map_id,fixedCodim_prod] at hb
  have hu := rank_lt_fixedCodim_of_nonFF_image U.toRepresentation hA hU hnU
  have hw := rank_lt_fixedCodim_of_nonFF_image W.toRepresentation hA hW hnW
  omega

end Representation.BinaryOffender
