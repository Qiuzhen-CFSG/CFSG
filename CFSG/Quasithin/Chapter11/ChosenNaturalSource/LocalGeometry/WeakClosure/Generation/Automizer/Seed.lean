module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer.Linear
public import Theory.GroupTheory.NormalLayerOuterIndex
public import Theory.Representation.ScalarCentralizerOrder
public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer.Commutant
public import Theory.Representation.FirstCohomologyG2Natural.Commutant
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.TwoSylowSource
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.OuterOrder

/-!
# Cartan bounds for all original natural-module automizers

The original coordinate quotient is faithful for the full automizer, even
when the covering module has a central attachment. Its layer centralizer
embeds in the scalar field units. Conjugation therefore bounds the layer
index using the genuine outer automorphism group: order 2n for Sp₄ and a
divisor of n for G₂. The layer-index and Borel argument yields n′ ≤ n.
Together with the full SL₃ calculation, this discharges the first automizer
premise of 11.2.1 for every chosen nonbinary natural module.

Source: Aschbacher--Smith A.3.15 and 11.2.1, printed pp.50--51,766--767.
The doubled V_M bound and the source weak-closure assembly remain separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The relative layer centralizer acts by actual coefficient-field scalars. -/
theorem full_automizer_centralizer_card_dvd (c : Coordinates D S.field) :
    Nat.card (centralizer (inducedAutomizer V L : Set (Automizer V))) ∣
      2 ^ S.field.degree - 1 := by
  let := D.elementary
  obtain ⟨ρ,hρ,_,hres⟩ := Parameters.FullAutomizer.exists_faithful_quotient_action D S c
  have hnon : Nontrivial c.Space := by
    cases c with
    | sl3 m => exact inferInstanceAs (Nontrivial (Fin 3 → S.field.Carrier))
    | sp4 m => exact inferInstanceAs (Nontrivial ((Fin 2 ⊕ Fin 2) → S.field.Carrier))
    | g2 m =>
      exact (Atlas.G2.Restricted.NaturalCoordinates.equiv S.field.Carrier).symm.injective.nontrivial
  let := hnon
  rw [← S.field.card_eq]
  apply centralizer_card_dvd_of_scalar_commutant ρ hρ (inducedAutomizer V L)
    (F := S.field.Carrier)
  intro f hf
  have hmodel (g : c.ModelGroup) (v : c.Space) :
      f (c.modelAction g v) = c.modelAction g (f v) := by
    obtain ⟨a,rfl⟩ := (Parameters.FullAutomizer.layerEquiv D S c).surjective g
    rw [← hres, ← hres]
    exact hf a v
  cases c with
  | sl3 m => exact SL3OddNaturalNormalizer.centralizer_scalar f hmodel
  | sp4 m =>
    exact SymplecticConjugatePair.Ambient.Normalizer.Commutant.natural_centralizer_scalar f
      (fun g v => hmodel g.val v)
  | g2 m =>
    exact Atlas.G2.Natural.exists_scalar_of_additive_commutes_derived f
      (fun g v => hmodel g.val v)

/-- Inner-field coverage bounds the actual G₂ outer quotient by the degree. -/
theorem g2_outer_card_dvd_degree :
    Nat.card (MulAut.Outer (Atlas.G2.Model S.field.Carrier)) ∣ S.field.degree := by
  have hq : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact (show 2 ^ 1 < 2 ^ S.field.degree from Nat.pow_lt_pow_right (by decide) S.nonbinary)
  exact (Atlas.G2.LieAutomorphismExtensions.outer_card_dvd_fieldAut hq).trans
    (dvd_of_eq (SL3OddNaturalNormalizer.binaryFieldAut_card S.field.card_eq))

/-- The full symplectic automizer bound includes nonsplit covering modules. -/
theorem sp4_full_automizer_nPrime_le
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    nPrime (Automizer V) ≤ S.field.degree := by
  let c := Coordinates.sp4 m
  let := Parameters.FullAutomizer.layer_normal D S
  have houter : Nat.card (MulAut.Outer (inducedAutomizer V L)) = 2 * S.field.degree := by
    rw [Nat.card_congr (MulAut.outerCongr (Parameters.FullAutomizer.layerEquiv D S c)).toEquiv]
    exact Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.card_outer_eq_two_mul
      S.field.card_eq S.nonbinary
  have hi := (normal_index_dvd_centralizer_mul_outer (inducedAutomizer V L)).trans
    (Nat.mul_dvd_mul (full_automizer_centralizer_card_dvd D S c) (dvd_of_eq houter))
  apply nPrime_le_of_even_layer_index (inducedAutomizer V L)
    (layer_solvable_sylow_control D S c) (k := 1) (by have := S.nonbinary; omega)
  · simpa only [pow_one, mul_comm, mul_left_comm, mul_assoc] using hi
  · exact layer_sylow_normalizer_odd_exponent D S

/-- The full G₂ automizer bound retains the original central attachment. -/
theorem g2_full_automizer_nPrime_le
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) :
    nPrime (Automizer V) ≤ S.field.degree := by
  let c := Coordinates.g2 m
  let := Parameters.FullAutomizer.layer_normal D S
  have houter : Nat.card (MulAut.Outer (inducedAutomizer V L)) ∣ S.field.degree := by
    rw [Nat.card_congr (MulAut.outerCongr (Parameters.FullAutomizer.layerEquiv D S c)).toEquiv]
    exact g2_outer_card_dvd_degree D S
  have hi := (normal_index_dvd_centralizer_mul_outer (inducedAutomizer V L)).trans
    (Nat.mul_dvd_mul (full_automizer_centralizer_card_dvd D S c) houter)
  apply nPrime_le_of_layer_index (inducedAutomizer V L)
    (layer_solvable_sylow_control D S c) (k := 1) (by have := S.nonbinary; omega)
  · simpa only [pow_one, mul_comm] using hi
  · exact layer_sylow_normalizer_odd_exponent D S

/-- The uniform bound on the entire automizer of the original chosen module. -/
theorem full_automizer_nPrime_le : nPrime (Automizer V) ≤ S.field.degree := by
  cases coordinates D S with
  | sl3 m => exact sl3_full_automizer_nPrime_le D S m
  | sp4 m => exact sp4_full_automizer_nPrime_le D S m
  | g2 m => exact g2_full_automizer_nPrime_le D S m

/-- The exact first automizer bound consumed by source 11.2.1. -/
theorem seed_nPrime_le :
    nPrime (inducedAutomizer V
      (normalizer (L : Set G) ⊓ normalizer (V : Set G))) ≤ S.field.degree := by
  rw [seed_automizer_eq_top D S, nPrime_eq_of_mulEquiv topEquiv]
  exact full_automizer_nPrime_le D S

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
