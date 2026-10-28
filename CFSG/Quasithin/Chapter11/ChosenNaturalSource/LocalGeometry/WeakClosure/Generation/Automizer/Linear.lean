module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer.Index
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer.ModelTori
public import Theory.Representation.SL3OddNaturalNormalizer

/-!
# The full automizer bound for the original SL₃ module

The faithful quotient action identifies the literal layer with full SL₃.
The additive scalar commutant bounds its index in the ambient automizer by
(q-1)n. Cartan placement and the split Borel exponent then bound n′ by n.
The final theorem identifies the exact seed automizer used by 11.2.1.

Source: Aschbacher--Smith A.3.15 and 11.2.1, pp.50--51,766--767.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original full automizer has Cartan parameter at most n in the SL₃ row. -/
theorem sl3_full_automizer_nPrime_le
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    nPrime (Automizer V) ≤ S.field.degree := by
  let := D.elementary
  let c := Coordinates.sl3 m
  let := Parameters.FullAutomizer.layer_normal D S
  obtain ⟨ρ,hρ,_,hres⟩ := Parameters.FullAutomizer.exists_faithful_quotient_action D S c
  have hi := SL3OddNaturalNormalizer.index_dvd_field_units_mul_degree S.field.card_eq
    (inducedAutomizer V L) (Parameters.FullAutomizer.layerEquiv D S c) ρ hρ hres
  apply nPrime_le_of_layer_index (inducedAutomizer V L)
    (layer_solvable_sylow_control D S c) (k := 1) (by have := S.nonbinary; omega)
  · simpa only [pow_one, Nat.mul_comm] using hi
  · exact layer_sylow_normalizer_odd_exponent D S

include D S in
/-- The source seed automizer is the entire actual automizer of V. -/
theorem seed_automizer_eq_top :
    inducedAutomizer V (normalizer (L : Set G) ⊓ normalizer (V : Set G)) = ⊤ := by
  rw [inf_eq_right.mpr (seed_normalizer_le D S)]
  simp only [inducedAutomizer, subgroupOf_self,
    Subgroup.map_top_of_surjective _ V.normalizerMonoidHom.rangeRestrict_surjective]

/-- The SL₃ bound on the literal group in the first generation premise. -/
theorem sl3_seed_nPrime_le
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    nPrime (inducedAutomizer V
      (normalizer (L : Set G) ⊓ normalizer (V : Set G))) ≤ S.field.degree := by
  rw [seed_automizer_eq_top D S, nPrime_eq_of_mulEquiv topEquiv]
  exact sl3_full_automizer_nPrime_le D S m

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
