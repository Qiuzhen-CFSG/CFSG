/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianMonomialReduction.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneReductionSurjective
public import Theory.AtlasPort.Janko2.Codes.IcosianMatrixGlueStabilizer

/-!
# IcosianMonomialReduction

Unit monomial transformations reduce onto the finite monomial group. Taking the
preimage of the full glue stabilizer defines all its integral lifts.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianMonomialReduction.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes

abbrev IcosianUnitBlocks := Fin 3 → icosianNormOneGroup

def icosianUnitBlockPermutations : Equiv.Perm (Fin 3) →* MulAut IcosianUnitBlocks where
  toFun p :=
    { toFun := fun g i => g (p.symm i)
      invFun := fun g i => g (p i)
      left_inv := by intro g; funext i; simp
      right_inv := by intro g; funext i; simp
      map_mul' := by intros; rfl }
  map_one' := by apply MulEquiv.ext; intro g; funext i; rfl
  map_mul' p q := by apply MulEquiv.ext; intro g; funext i; rfl

abbrev IcosianUnitMonomial :=
  SemidirectProduct IcosianUnitBlocks (Equiv.Perm (Fin 3)) icosianUnitBlockPermutations

instance icosianUnitMonomial_finite : Finite IcosianUnitMonomial :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

def icosianUnitBlockReduction : IcosianUnitBlocks →* IcosianGlueBlocks GoldenFour where
  toFun u i := icosianNormOneReduction (u i)
  map_one' := by funext i; exact map_one icosianNormOneReduction
  map_mul' u v := by funext i; exact map_mul icosianNormOneReduction _ _

def icosianMonomialReduction : IcosianUnitMonomial →* IcosianGlueMonomialGroup GoldenFour :=
  SemidirectProduct.map icosianUnitBlockReduction (MonoidHom.id _)
    (by intro p; apply MonoidHom.ext; intro u; funext i; rfl)

theorem icosianMonomialReduction_surjective : Function.Surjective icosianMonomialReduction := by
  intro g
  choose u hu using fun i => icosianNormOneReduction_surjective (g.left i)
  refine ⟨⟨u,g.right⟩,?_⟩
  apply SemidirectProduct.ext
  · exact funext hu
  · rfl

/-- All lifts of the full finite gluing stabilizer, before identifying it with
an actual frame stabilizer. No splitting of this extension is asserted. -/
def icosianLiftedMonomial : Subgroup IcosianUnitMonomial :=
  (icosianGlueMonomialStabilizer GoldenFour).comap icosianMonomialReduction

def icosianLiftedMonomialProjection :
    icosianLiftedMonomial →* icosianGlueMonomialStabilizer GoldenFour where
  toFun g := ⟨icosianMonomialReduction g.val,g.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

theorem icosianLiftedMonomialProjection_surjective :
    Function.Surjective icosianLiftedMonomialProjection := by
  intro g
  obtain ⟨u,hu⟩ := icosianMonomialReduction_surjective g.val
  refine ⟨⟨u,?_⟩,?_⟩
  · change icosianMonomialReduction u ∈ icosianGlueMonomialStabilizer GoldenFour
    rw [hu]
    exact g.property
  · exact Subtype.ext hu

end Atlas.Conway
