module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.CycleSimplicity.Realization
public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.CycleSimplicity.Certificate
public import Theory.Representation.JacobsonDensity

/-!
# Absolute simplicity of the PSL₃(3) incidence-cycle quotient

The quotient of the 27-dimensional incidence kernel by its constant cycle
line is irreducible over every field of characteristic two. Checked cycle
coordinates identify two literal projected SL₃(3) actors with binary matrices.
A rank-one certificate proves those matrices generate the full matrix algebra,
and coefficient casting preserves density over arbitrary characteristic-two
fields. Conjugating back gives every endomorphism of the native quotient.

This supplies the degree-26 geometric witness required by the principal-model
construction for Guralnick--Malle, Classification of 2F-modules I, Proposition
4.2, manuscript pp.9--10. It assumes no irreducibility, character-table
completeness, block membership, or generation of the group by the two actors.
-/

@[expose] public section

namespace Representation.PSL3Three.AbsoluteDegrees.PrincipalModels
open CycleSimplicity
open scoped Matrix

variable (F : Type*) [Field F] [CharP F 2]

noncomputable def cycleEndEquiv :
    Module.End F (CycleQuotient F) ≃ₐ[F] Matrix (Fin 26) (Fin 26) F :=
  ((quotientEquiv F).symm.conjAlgEquiv F).trans LinearMap.toMatrixAlgEquiv'

private theorem cycleEndEquiv_actor (a : Fin 2) :
    cycleEndEquiv F ((constantLine F).quotientRepresentation (Coordinates.actor a)) =
      quotientMatrix F a := by
  change LinearMap.toMatrix'
    (((quotientEquiv F).symm.conjAlgEquiv F)
      ((constantLine F).quotientRepresentation (Coordinates.actor a))) = _
  rw [← LinearMap.toMatrix'_toLin' (quotientMatrix F a)]
  congr 1
  apply LinearMap.ext
  intro x
  change (quotientEquiv F).symm
    ((constantLine F).quotientRepresentation (Coordinates.actor a) (quotientEquiv F x)) =
      quotientMatrix F a *ᵥ x
  have he : (constantLine F).quotientRepresentation (Coordinates.actor a) (quotientEquiv F x) =
      quotientEquiv F (quotientMatrix F a *ᵥ x) := actor_quotientLift F a x
  rw [he, LinearEquiv.symm_apply_apply]

/-- The literal incidence-cycle quotient has full endomorphism algebra in characteristic two. -/
theorem cycleQuotient_density :
    Algebra.adjoin F (Set.range (constantLine F).quotientRepresentation) = ⊤ := by
  let P := Algebra.adjoin F (Set.range (constantLine F).quotientRepresentation)
  let e := cycleEndEquiv F
  let Q := P.map e.toAlgHom
  have hQ : Q = ⊤ := Certificate.algebra_eq_top_charTwo F Q (by
    intro a
    change quotientMatrix F a ∈ Q
    rw [← cycleEndEquiv_actor]
    exact ⟨(constantLine F).quotientRepresentation (Coordinates.actor a),
      Algebra.subset_adjoin (Set.mem_range_self _), rfl⟩)
  apply top_unique
  intro T _
  have hT : e T ∈ Q := by rw [hQ]; trivial
  obtain ⟨T', hT', he⟩ := hT
  exact e.injective he ▸ hT'

/-- Absolute simplicity of the 26-dimensional incidence-cycle quotient.
Algebraic closure is unnecessary: the checked density certificate survives
coefficient casting to every characteristic-two field. -/
theorem cycleQuotient_isIrreducible :
    IsIrreducible (constantLine F).quotientRepresentation := by
  let : Nontrivial (CycleQuotient F) := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank F (CycleQuotient F) by rw [finrank_cycleQuotient]; decide)
  exact irreducible_of_jacobson_density_surjective _ (cycleQuotient_density F)

end Representation.PSL3Three.AbsoluteDegrees.PrincipalModels
