module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.ComponentInputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.IndexTwo
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.SplitModels.Extension
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.SplitModels.Models
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.SplitModels.GraphTwist
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.SplitModels.OutsideAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Compatible models of a split restriction in the orthogonal quotient

The orthogonal constituent is excluded: its given marking identifies it with
an actual restriction of the natural S₈ module, so the extending-constituent
argument applies. In the natural or dual case, conjugation by the inverse
outside swapper is inverse transpose times inner, so the graph-twist argument
identifies the other constituent with the opposite model. The internal sum
then gives the required equivalence with the external natural-plus-dual model,
with the same specified GL₄(2) marking throughout.

The final theorem takes the constituent-model alternative explicitly. The
source assembly must obtain that premise by applying B.4 to a constituent;
no quadratic-actor or marked-plane hypothesis is needed for this step.

Source: Aschbacher–Smith B.4.2(9–10), B.4.5 and their use in 13.8.25,
printed pp.86–87,959–960 (combined manuscript of 1 March 2004).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction.SplitModels
open Representation FourStructure.ChiefFactors

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  {ρ : Representation (ZMod 2) H U} {K : Subgroup H}

/-- The actual six-dimensional permutation section already extends to H,
so it cannot occur as a constituent of this split irreducible module. -/
theorem not_componentOrthogonal [FiniteDimensional (ZMod 2) U]
    (d : RestrictionSplit ρ K) (hi : IsIrreducible ρ)
    (eH : H ≃* Equiv.Perm (Fin 8))
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) :
    ¬ IsComponentOrthogonal K d.left.toRepresentation eH := by
  rintro ⟨e, he⟩
  have hindex : K.index = 2 := by
    rw [← K.index_map_equiv eH]
    change (K.map eH.toMonoidHom).index = 2
    rw [hK]
    exact alternatingGroup.index_eq_two
  exact d.not_extends hindex hi
    ((BinaryPermutation.naturalRepresentation (Fin 8)).comp eH.toMonoidHom) e he

/-- After excluding the extending model, B.4's constituent premise supplies
one of the two actual four-dimensional models. -/
theorem naturalOrDual_of_constituent_alternatives [FiniteDimensional (ZMod 2) U]
    (d : RestrictionSplit ρ K) (hi : IsIrreducible ρ)
    (eH : H ≃* Equiv.Perm (Fin 8))
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (eK : K ≃* BinaryLinear.GL FourSpace)
    (hc : IsNaturalOrDual d.left.toRepresentation eK ∨
      IsComponentOrthogonal K d.left.toRepresentation eH) :
    IsNaturalOrDual d.left.toRepresentation eK :=
  hc.resolve_right (not_componentOrthogonal d hi eH hK)

/-- Complementary opposite models give the requested equivalence and
intertwining identity on the whole restricted module. -/
theorem naturalDualRestriction_of_oppositeModels
    (d : RestrictionSplit ρ K) (eK : K ≃* BinaryLinear.GL FourSpace)
    (hc : OppositeModels d eK) : IsNaturalDualRestriction ρ K eK := by
  rcases hc with ⟨⟨eL, hL⟩, ⟨eR, hR⟩⟩ | ⟨⟨eL, hL⟩, ⟨eR, hR⟩⟩
  · let e := d.sumEquiv.symm.trans (eL.prodCongr eR)
    refine ⟨e, fun k v => ?_⟩
    obtain ⟨x, rfl⟩ := d.sumEquiv.surjective v
    rw [← d.sumEquiv_intertwines]
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply]
    rw [hL, hR]
    ext x <;> simp [naturalDualAction, Representation.dual, naturalAction]
  · let e := d.sumEquiv.symm.trans ((eL.prodCongr eR).trans
      (LinearEquiv.prodComm (ZMod 2) _ _))
    refine ⟨e, fun k v => ?_⟩
    obtain ⟨x, rfl⟩ := d.sumEquiv.surjective v
    rw [← d.sumEquiv_intertwines]
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply, LinearEquiv.prodComm_apply]
    rw [hR, hL]
    ext x <;> simp [naturalDualAction, Representation.dual, naturalAction]

/-- An outside element exchanges natural and contragredient constituents for
the given GL₄(2) marking. Normality and the graph-action identity follow from
the specified alternating subgroup of S₈. -/
theorem oppositeModels_of_naturalOrDual
    (d : RestrictionSplit ρ K) (eH : H ≃* Equiv.Perm (Fin 8))
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (eK : K ≃* BinaryLinear.GL FourSpace)
    (hc : IsNaturalOrDual d.left.toRepresentation eK) : OppositeModels d eK := by
  have hindex : K.index = 2 := by
    rw [← K.index_map_equiv eH]
    change (K.map eH.toMonoidHom).index = 2
    rw [hK]
    exact alternatingGroup.index_eq_two
  let : K.Normal := K.normal_of_index_eq_two hindex
  obtain ⟨g, hg⟩ := outside_conjugation_eq_graph_mul_inner eH K hK eK
    d.swapper d.outside
  exact oppositeModels_of_graph d eK g hg hc

/-- The split branch of the constituent-model deduction in 13.8.25: either
B.4 constituent alternative yields the actual natural-plus-dual restriction,
with its linear equivalence and intertwining identity for the specified eK.
The orthogonal alternative is impossible because that constituent extends to H. -/
theorem naturalDualRestriction_of_constituent_alternatives
    [FiniteDimensional (ZMod 2) U]
    (d : RestrictionSplit ρ K) (hi : IsIrreducible ρ)
    (eH : H ≃* Equiv.Perm (Fin 8))
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (eK : K ≃* BinaryLinear.GL FourSpace)
    (hc : IsNaturalOrDual d.left.toRepresentation eK ∨
      IsComponentOrthogonal K d.left.toRepresentation eH) :
    IsNaturalDualRestriction ρ K eK := by
  apply naturalDualRestriction_of_oppositeModels d eK
  apply oppositeModels_of_naturalOrDual d eH hK eK
  exact naturalOrDual_of_constituent_alternatives d hi eH hK eK hc

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction.SplitModels
