module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.CharacteristicNormalizers
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.CharacteristicNormalizers.SeedMovement.Assembly
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete

/-!
# The strict normalizer and Thompson conclusions of 13.6.16

If a characteristic normalizer supplements the radical, its actual residual
is again a local component. The seed-action argument with the proved adequate
B.5 classification shows that this residual moves the original seed. The
first assertion of 13.6.16 then contradicts its normalization of the nontrivial
characteristic subgroup. The strict inequality feeds the Frattini--Thompson
argument on the same subgroup and the same ambient Thompson subgroup.

The universal two-core conclusion in assertion (1) remains explicit: its
producer uses the earlier replacement instance of 13.6.3(2). Neither a module
classification premise nor a radical-centralization premise remains here.
Source: Aschbacher--Smith, 13.6.16(2--3), printed p.930.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceTransferFields.HigherFieldParabolics
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual normalizer residual supplies strictness, using the complete B.5 theorem. -/
theorem characteristic_normalizer_obstruction_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (z v : G)
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hvT : v ∈ T) (hv : v ≠ 1) (hv2 : v ^ 2 = 1)
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v))
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hchar : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hcore : ∀ K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v),
      Tv (T : Subgroup G) v ≤ normalizer (K : Set G) →
      ¬ K ≤ centralizer ({z} : Set G) → (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥)
    (K : Subgroup G) (hK : K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hS : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (hm : ¬ K ≤ centralizer ({z} : Set G)) :
    CharacteristicNormalizerObstruction (Tv (T : Subgroup G) v) K := by
  intro C hCchar hC
  let := hCchar
  by_contra hnlt
  obtain ⟨_, _, _, hgen, hfix, _⟩ :=
    nonstrict_characteristicNormalizer_obstruction T z v hidx hcore K hK hS hm C hC hnlt
  exact SeedMovement.replacement_moves_of_characteristic_two hG
    ChapterB.SourceInduction.adequateClassification_knownSimple T z v hz hvT hv hv2
    hSylow hidx hchar hcore K
    (characteristicNormalizerReplacement K (Tv (T : Subgroup G) v) C)
    hK hS hm hgen hfix

/-- Both later assertions of 13.6.16 on the original component and Thompson subgroup. -/
theorem characteristic_normalizer_and_thompson_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (z v : G)
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hvT : v ∈ T) (hv : v ≠ 1) (hv2 : v ^ 2 = 1)
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v))
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hchar : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hcore : ∀ K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v),
      Tv (T : Subgroup G) v ≤ normalizer (K : Set G) →
      ¬ K ≤ centralizer ({z} : Set G) → (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥)
    (K : Subgroup G) (hK : K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hS : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (hm : ¬ K ≤ centralizer ({z} : Set G)) :
    CharacteristicNormalizerObstruction (Tv (T : Subgroup G) v) K ∧
      K = ⁅K, elementaryAbelianMaxJ (Tv (T : Subgroup G) v)⁆ := by
  have hstrict := characteristic_normalizer_obstruction_source hG T z v hz hvT hv hv2
    hSylow hidx hchar hcore K hK hS hm
  exact ⟨hstrict, eq_commutator_thompson_of_characteristic_normalizers T z v hvT hv
    hSylow hidx K hK hS hm hstrict⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
