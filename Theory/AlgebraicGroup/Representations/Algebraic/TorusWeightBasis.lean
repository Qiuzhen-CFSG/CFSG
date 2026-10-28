module

public import Theory.AlgebraicGroup.Representations.Algebraic.WeightSpaces
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Finite algebraic weight bases

The algebraic weight spaces of a rational torus representation form an
internal direct sum. Collecting bases of those spaces and reindexing gives an
actual basis indexed by the original module's finite rank. The coordinate
formula then transports the original action to diagonal scalar multiplication,
retaining the original closed-subgroup inclusion and algebraic characters.

This is the weight decomposition of Borel, Linear Algebraic Groups, §§8.5–8.6,
used by the cocharacter limits and projective torus-curve arguments in §13.
-/

public noncomputable section

namespace Theory.AlgebraicGroup
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {E : Type v} [AddCommGroup E] [Module k E] [FiniteDimensional k E]

/-- A rational torus action has an actual finite basis of algebraic weight
vectors, retaining the original subgroup inclusion and representation. -/
theorem exists_finite_torus_weight_basis
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (T : ClosedSubgroup G) (hT : IsTorus T.carrierVariety) :
    ∃ (b : Module.Basis (Fin (Module.finrank k E)) k E)
      (χ : Fin (Module.finrank k E) → TorusWeight T),
      ∀ (i : Fin (Module.finrank k E)) (t : Variety.Point T.carrierVariety),
        (ρ.action (T.includePoint t)).1 (b i) = (χ i).pointCharacter t • b i := by
  classical
  let W := fun χ : TorusWeight T => weightSpace ρ T χ
  have hW : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (weightSpace_iSupIndep ρ T) (closedSubtorusRepresentation_weightSpace_iSup_eq_top ρ hρ T hT)
  let c := fun χ : TorusWeight T => Module.finBasis k (W χ)
  let d := hW.collectedBasis c
  let e := d.indexEquiv (Module.finBasis k E)
  refine ⟨d.reindex e, fun i => (e.symm i).1, ?_⟩
  intro i t
  have hv := hW.collectedBasis_mem c (e.symm i)
  simpa only [Module.Basis.reindex_apply] using hv t


omit [IsAlgClosed k] [FiniteDimensional k E] in
/-- Coordinates in the actual weight basis intertwine the original torus
representation with its literal diagonal scalar action. -/
theorem torus_weight_basis_coordinates
    (ρ : RationalRepresentation G E) (T : ClosedSubgroup G)
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (χ : Fin (Module.finrank k E) → TorusWeight T)
    (hweight : ∀ i t, (ρ.action (T.includePoint t)).1 (b i) =
      (χ i).pointCharacter t • b i)
    (t : Variety.Point T.carrierVariety) (v : E) (i : Fin (Module.finrank k E)) :
    b.equivFun ((ρ.action (T.includePoint t)).1 v) i =
      (χ i).pointCharacter t * b.equivFun v i := by
  classical
  have hlin : (b.coord i).comp (ρ.action (T.includePoint t)).1 =
      (χ i).pointCharacter t • b.coord i := by
    apply b.ext
    intro j
    change b.coord i ((ρ.action (T.includePoint t)).1 (b j)) =
      (χ i).pointCharacter t * b.coord i (b j)
    rw [hweight]
    simp only [map_smul, smul_eq_mul, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    split_ifs with h
    · subst j; rfl
    · simp
  exact LinearMap.congr_fun hlin v

end Theory.AlgebraicGroup
