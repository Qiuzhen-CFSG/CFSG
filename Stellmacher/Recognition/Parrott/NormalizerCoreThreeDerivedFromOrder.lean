module

public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeFixed
public import Stellmacher.Recognition.Parrott.NormalizerCoreOmegaQuotient
public import Stellmacher.Recognition.Parrott.NormalizerCoreDerivedOmega
public import Stellmacher.Recognition.Parrott.NormalizerCoreAbelianization
public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeOmega
public import Theory.GroupAction.OmegaFixedDerivedSixteen

/-!
# Sylow-three fixed containment from the derived core order

Let X be the ambient image of O₂(N_G(F)), and let D be its derived
subgroup in G. Assuming |D| = 64, every element of X centralizing the
supplied Sylow three-subgroup lies in D.

The actual conjugation action has its fixed points in omega. The core,
derived subgroup and omega have orders 1024, 64 and 256, respectively,
and the abelianization has a nontrivial square. The generic coprime-action
argument therefore places the fixed points in the intrinsic derived
subgroup. The literal subtype maps transport this containment to G.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.677, following N/U ≃ S₄ and the calculation of K′.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- A derived core of order 64 contains the core centralizer of every supplied
Sylow three-subgroup of the second normalizer. -/
public theorem normalizer_three_centralizer_le_derived_of_card
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
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
    d.exists_normalizer_three_core_action_fixed_le_omega h hN hproper Q
  let : MulDistribMulAction Q K := MulDistribMulAction.compHom K action
  have hderived : FixedPoints.subgroup Q K ≤ commutator K :=
    Theory.GroupAction.fixedPoints_le_commutator_of_card_omega
      (d.normalizer_three_card h hN hproper Q)
      (d.normalizer_core_order h hN hproper).2.1
      (d.normalizer_core_abelianization_card_of_derived_card h hN hproper hDcard).1
      (d.normalizer_core_omega_structure h hN hproper).1
      (d.normalizer_core_exists_square_not_mem_native_derived h hN hproper)
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
