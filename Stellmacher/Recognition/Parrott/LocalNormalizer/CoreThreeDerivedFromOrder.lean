module

public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeDerivedFromOrder
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.NormalizerCoreSolvable
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreAbelianization
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreOmega
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreThreeCenters
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreThreeOmega

/-!
# The actual second normalizer from local inputs

These calculations retain the supplied second elementary subgroup and Sylow.
The original derived-core normalizer identity and solvability of the actual
second normalizer replace the ambient N₂ assumption. All subgroup images,
centers, omega subgroups and conjugators are the original literal ones.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678. This is the local-input extension of `NormalizerCoreThreeDerivedFromOrder`.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- A derived core of order 64 contains the core centralizer of every supplied
Sylow three-subgroup of the second normalizer. -/
public theorem normalizer_three_centralizer_le_derived_of_card_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    Nat.card D = 64 → X ⊓ centralizer (A : Set G) ≤ D := by
  intro N X D A hDcard
  let K := pCore 2 N
  obtain ⟨action, haction, hfixed⟩ :=
    d.exists_normalizer_three_core_action_fixed_le_omega_of_local_inputs h hlocal hproper Q
  let : MulDistribMulAction Q K := MulDistribMulAction.compHom K action
  have hderived : FixedPoints.subgroup Q K ≤ commutator K :=
    Theory.GroupAction.fixedPoints_le_commutator_of_card_omega
      (d.normalizer_three_card_of_local_inputs h hlocal hproper Q)
      (d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper).2.1
      (d.normalizer_core_abelianization_card_of_derived_card_of_local_inputs h hlocal hproper hDcard).1
      (d.normalizer_core_omega_structure_of_local_inputs h hlocal hproper).1
      (d.normalizer_core_exists_square_not_mem_native_derived_of_local_inputs h hlocal hproper)
      hfixed
  rintro x ⟨hxX, hxC⟩
  obtain ⟨k, hk, rfl⟩ := hxX
  have hkfixed : (⟨k, hk⟩ : K) ∈ FixedPoints.subgroup Q K := by
    intro q
    apply N.subtype_injective.comp K.subtype_injective
    change (((action q ⟨k, hk⟩ : K) : N) : G) = (k : G)
    rw [haction]
    exact mul_inv_eq_iff_eq_mul.mpr
      (hxC ((q : N) : G) (mem_map_of_mem N.subtype q.property))
  change (k : G) ∈ (commutator X).map X.subtype
  rw [← d.normalizer_core_native_derived_image]
  exact mem_map_of_mem (N.subtype.comp K.subtype) (hderived hkfixed)

end Stellmacher.Recognition.ParrottSecondElementaryData
