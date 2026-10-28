module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveTripleSix
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveTripleSixFaithful
public import Theory.Representation.BinaryOffender.InvariantAction

/-!
# The common-offender test on original invariant constituents

For a normal component, faithfulness on the chosen invariant subspace survives
its actual translate. The two restricted fixed-codimension bounds give offenders
on the same component subgroup. Covered-A₆ recognition then supplies an
intertwiner with that component unchanged. This boundary keeps the literal
subspace actions while avoiding repeated unfolding in the Chapter12 consumer.

Source: Aschbacher--Smith D.3.5(5), printed p.196. The actual application is
`SeedAlternativesMovedSylowTripleSix`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) H W)

theorem invariant_equiv_of_common_budget_tripleSix
    (K : Subgroup H) [K.Normal] (I : Submodule (ZMod 2) W) (t : H)
    (hI : IsIrrPlus ρ K I)
    (hJ : IsIrrPlus ρ K (I.map (ρ t)))
    (hz : fixedSpace ρ K = ⊥)
    (e : K ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hi : Module.finrank (ZMod 2) I = 6)
    (hf : Function.Injective (invariantSubspace ρ K I hI.choose).toRepresentation)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hAK : A ≤ K)
    (hbi : fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) ≤ rank A)
    (hbj : fixedCodim (subspaceImageRepresentation ρ (I.map (ρ t)))
      (restrictedSubgroup ρ (I.map (ρ t)) A) ≤ rank A) :
    Nonempty (Representation.Equiv (invariantSubspace ρ K I hI.choose).toRepresentation
      (invariantSubspace ρ K (I.map (ρ t)) hJ.choose).toRepresentation) := by
  let J := I.map (ρ t)
  let τ := (invariantSubspace ρ K I hI.choose).toRepresentation
  let σ := (invariantSubspace ρ K J hJ.choose).toRepresentation
  have hit := invariant_irreducible_of_isIrrPlus ρ K I hI (by rw [hz,inf_bot_eq])
  have his := invariant_irreducible_of_isIrrPlus ρ K J hJ (by rw [hz,inf_bot_eq])
  have hj : Module.finrank (ZMod 2) J = 6 := (finrank_map_action ρ I t).trans hi
  have hfj := invariant_injective_conjugate ρ K I hI.choose t hJ.choose hf
  exact six_dimensional_equiv_of_marked_common_offender τ σ hf hfj hit his e hi hj
    (A.subgroupOf K)
    (component_offender_of_restricted_budget ρ K A I hI.choose hAK hA hbi)
    (component_offender_of_restricted_budget ρ K A J hJ.choose hAK hA hbj)

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
