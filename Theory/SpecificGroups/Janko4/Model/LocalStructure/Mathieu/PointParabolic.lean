module
public import Theory.GroupTheory.PCoreSectionCard
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.HallActors
public import Theory.Mathieu.M24.LocalGeometry.TrioNormalizerControl

/-!
# The original parabolic in the native Mathieu local

Actual containment in max1 puts its normal elementary kernel inside the
original full Sylow, hence inside the parabolic. The literal M24 quotient
therefore preserves the relative index 63. A core-free quotient image
would embed as a section of the original order-1008 core quotient, which
is incompatible with a full Mathieu Sylow. Native trio recognition then
identifies the parabolic as the full inverse image of a conjugate trio.

The quotient conjugator and actual projection remain explicit. This does
not compare the resulting subgroup with a max4 point parabolic. Its
literal exterior-source application is in JankoNativeParabolic.
Source: Aschbacher–Smith, 12.5.3, printed p.818/PDF p.835.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.MathieuParabolic
open Janko4.Cardinality MathieuHallActors
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local notation "M" => max1Subgroup matrixA_mul_self matrixB_pow_four
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups

/-- A small-core parabolic is the full preimage under the actual Mathieu map. -/
theorem eq_trio_preimage
    {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 M) (J : Subgroup M) (hSJ : (S : Subgroup M) ≤ J)
    (hi : (S : Subgroup M).relIndex J = 63)
    (j : J →* A) (hj : Function.Injective j)
    (hA : Nat.card (A ⧸ pCore 2 A) = 1008) :
    ∃ g : Sporadic.Mathieu.M24,
      J = (trioStabilizer standardTrio).comap
        ((MulAut.conj g).toMonoidHom.comp projection) := by
  have hkernel : IsPGroup 2 projection.ker := by
    rw [projection_ker, localKernel_eq_twoCore]
    exact pCore_isPGroup
  have hkS : projection.ker ≤ (S : Subgroup M) := hkernel.le_sylow_of_normal S
  let R := S.mapSurjective projection_surjective
  let X := J.map projection
  have hRX : (R : Subgroup Sporadic.Mathieu.M24) ≤ X := map_mono hSJ
  have hrel : (R : Subgroup Sporadic.Mathieu.M24).relIndex X = 63 := by
    change ((S : Subgroup M).map projection).relIndex (J.map projection) = 63
    rw [relIndex_map_map, sup_eq_left.mpr hkS, sup_eq_left.mpr (hkS.trans hSJ)]
    exact hi
  have hcore : pCore 2 X ≠ ⊥ := by
    intro hz
    have hd := MonoidHom.card_corefree_quotient_dvd_of_embedding j hj
      (projection.subgroupMap J) (projection.subgroupMap_surjective J) hz
    rw [hA] at hd
    have h32 : 32 ∣ Nat.card R := R.pow_dvd_card_of_pow_dvd_card (n := 5)
      (by rw [Sporadic.Mathieu.m24_order]; decide)
    have bad := (h32.trans (card_dvd_of_le hRX)).trans hd
    norm_num at bad
  obtain ⟨g, hg⟩ := Sporadic.Mathieu.M24LocalGeometry.TrioRecognition.exists_conjugate_trio
    R X hRX hcore hrel
  refine ⟨g, ?_⟩
  rw [← hg, ← comap_comap, comap_map_eq_self_of_injective (MulAut.conj g).injective]
  exact (comap_map_eq_self (hkS.trans hSJ)).symm

end Janko4.LocalStructure.MathieuParabolic
