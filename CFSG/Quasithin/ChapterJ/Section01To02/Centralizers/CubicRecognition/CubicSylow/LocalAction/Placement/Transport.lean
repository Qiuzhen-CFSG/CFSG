module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.LocalAction.Actions
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.Canonical
public import Theory.GroupTheory.SemidihedralStandardModel
public import Theory.GroupTheory.SemidihedralCenter
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Transport of the marked cubic complement in J.2.7

A literal quotient lift identifies T_R with the multiplier-one-or-three
subgroup of the cyclic-eight holomorph and preserves its actual marked map
into Aut(A₆). Transport gives its two generators, their presentation, a genuine
standard semidihedral equivalence, and the two specific transposition images.
Aligning the image of the original z with the image of (02)(13) then proves
r⁴ = z and identifies the whole embedded center with ⟨z⟩.

`Lift` records only the placement and quotient compatibility still to be
constructed. The theorems here do not assert that a lift or an alignment exists.
The source inputs already show that the marked z is an involution of the
specified M₁₀; its conjugacy to the canonical center is a separate model fact.

Source: Aschbacher–Smith, J.2.7, printed p.437 (PDF p.448).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction.Placement
open Subgroup
open AlternatingSix.ShadowLocal
open AlternatingSix.M10.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The original z, regarded as an element of N_G(B). -/
def zInNB : c.NB := ⟨c.z, c.GB_le_NB c.z_mem_GB⟩

theorem zInNB_order (hz : orderOf c.z = 2) : orderOf (zInNB c) = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact hz

theorem marked_z_order (hB : Nat.card c.B = 3) (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* AutA6) : orderOf (markedMap c e (zInNB c)) = 2 := by
  have hk : IsPGroup 3 (markedMap c e).ker := IsPGroup.of_card (n := 1) (by
    rw [markedMap_ker, normalizerKernel_card c hB, pow_one])
  rw [(markedMap c e).orderOf_map_eq_of_coprime_of_isPGroup_ker hk _
    (by rw [zInNB_order c hz]; decide), zInNB_order c hz]

theorem marked_z_mem_extension (e : c.NormalizerQuotient ≃* AutA6)
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension) :
    markedMap c e (zInNB c) ∈ AlternatingSix.M10.extension := by
  rw [← hM]
  exact mem_map_of_mem _ (mem_map_of_mem _ c.z_mem_GB)

/-- The primitive placement interface. The map is the published quotient marking,
and the Sylow images and actor are the original subgroups of G. The image of R
is retained for the normalizer product argument. Existence is not asserted here. -/
structure Lift (e : c.NormalizerQuotient ≃* AutA6) (σ : Equiv.Perm (Fin 6)) where
  R : Sylow 3 c.NB
  Tplus : Sylow 2 c.NB
  equiv : TR c R Tplus ≃* Coordinates.complement
  marked_eq (t : TR c R Tplus) :
    markedMap c e ⟨t, TR_le_NB c R Tplus t.property⟩ =
      (MulAut.conj (permutationAction σ)) (Identification.embedding (equiv t))
  image_R : (R : Subgroup c.NB).map (markedMap c e) =
    (AlternatingSix.M10.nine standardNine).map (MulAut.conj (permutationAction σ)).toMonoidHom
  z_mem : c.z ∈ TR c R Tplus

namespace Lift
variable {c} {e : c.NormalizerQuotient ≃* AutA6} {σ : Equiv.Perm (Fin 6)}
variable (l : Lift c e σ)

def rotation : TR c l.R l.Tplus := l.equiv.symm Coordinates.rotationIn
def flip : TR c l.R l.Tplus := l.equiv.symm Coordinates.flipIn

theorem rotation_order : orderOf l.rotation = 8 :=
  (l.equiv.symm.orderOf_eq _).trans Coordinates.rotationIn_order

theorem flip_order : orderOf l.flip = 2 :=
  (l.equiv.symm.orderOf_eq _).trans Coordinates.flipIn_order

theorem flip_ambient_order : orderOf (l.flip : G) = 2 := by
  rw [Subgroup.orderOf_coe]
  exact l.flip_order

theorem flip_rotation : l.flip * l.rotation * l.flip⁻¹ = l.rotation ^ 3 := by
  simpa only [map_mul, map_inv, map_pow, flip, rotation] using
    congrArg l.equiv.symm Coordinates.flipIn_rotationIn

theorem generated : closure ({l.rotation, l.flip} : Set (TR c l.R l.Tplus)) = ⊤ := by
  have he := congrArg (Subgroup.map l.equiv.symm.toMonoidHom) Coordinates.complement_generated
  simp only [Subgroup.map_sup, MonoidHom.map_zpowers,
    map_top_of_surjective l.equiv.symm.toMonoidHom l.equiv.symm.surjective,
    MulEquiv.coe_toMonoidHom] at he
  simpa only [rotation, flip, zpowers_eq_closure, ← Subgroup.closure_union,
    Set.singleton_union] using he

theorem card : Nat.card (TR c l.R l.Tplus) = 16 :=
  (Nat.card_congr l.equiv.toEquiv).trans Coordinates.card_complement

/-- A genuine equivalence to the standard order-sixteen semidihedral group. -/
def semidihedralEquiv : TR c l.R l.Tplus ≃* Semidihedral.StandardModel 4 (by decide) :=
  Classical.choice (Semidihedral.standardModel_equiv_of_presentation (by decide : 4 ≤ 4)
    l.rotation l.flip l.rotation_order l.flip_order l.flip_rotation l.generated l.card)

/-- The first actual permutation retained by the marking. -/
def firstSwap : Equiv.Perm (Fin 6) := σ * standardZ * σ⁻¹
/-- The second actual permutation retained by the marking. -/
def secondSwap : Equiv.Perm (Fin 6) := σ * standardU * σ⁻¹

theorem firstSwap_isSwap : (firstSwap (σ := σ)).IsSwap := by
  change (σ * Equiv.swap 0 2 * σ⁻¹).IsSwap
  rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right]
  exact Equiv.Perm.swap_isSwap_iff.mpr (σ.injective.ne (by decide))

theorem secondSwap_isSwap : (secondSwap (σ := σ)).IsSwap := by
  change (σ * Equiv.swap 1 3 * σ⁻¹).IsSwap
  rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right]
  exact Equiv.Perm.swap_isSwap_iff.mpr (σ.injective.ne (by decide))

theorem marked_flip :
    markedMap c e ⟨l.flip, TR_le_NB c l.R l.Tplus l.flip.property⟩ =
      permutationAction (firstSwap (σ := σ)) := by
  rw [l.marked_eq]
  change (MulAut.conj (permutationAction σ))
    (Identification.embedding (l.equiv (l.equiv.symm Coordinates.flipIn))) = _
  rw [l.equiv.apply_symm_apply]
  change (MulAut.conj (permutationAction σ)) (Identification.embedding Coordinates.flip) = _
  rw [embedding_flip]
  simp only [firstSwap, MulAut.conj_apply, map_mul, map_inv]

/-- The actual lift of the first transposition is fused to z by the explicit source premise. -/
theorem flip_fused (h7 : TranspositionFusion c e) :
    ∃ g : G, g * (l.flip : G) * g⁻¹ = c.z := by
  apply h7 ⟨l.flip, TR_le_NB c l.R l.Tplus l.flip.property⟩
  · rw [← Subgroup.orderOf_coe]
    exact l.flip_ambient_order
  · exact ⟨firstSwap, firstSwap_isSwap, l.marked_flip⟩

variable (hσ : markedMap c e (zInNB c) =
  (MulAut.conj (permutationAction σ)) (permutationAction (standardU * standardZ)))

include hσ in
theorem rotation_four : (l.rotation : G) ^ 4 = c.z := by
  have he : Identification.embedding (l.equiv (l.rotation ^ 4)) =
      Identification.embedding (l.equiv ⟨c.z, l.z_mem⟩) := by
    apply (MulAut.conj (permutationAction σ)).injective
    rw [← l.marked_eq ⟨c.z, l.z_mem⟩]
    change _ = markedMap c e (zInNB c)
    rw [hσ, map_pow]
    change (MulAut.conj (permutationAction σ))
      (Identification.embedding ((l.equiv (l.equiv.symm Coordinates.rotationIn)) ^ 4)) = _
    rw [l.equiv.apply_symm_apply]
    exact congrArg (MulAut.conj (permutationAction σ)) embedding_central
  exact congrArg Subtype.val (l.equiv.injective (Subtype.ext
    (Identification.embedding_injective he)))

include hσ in
theorem embedded_center :
    (center (TR c l.R l.Tplus)).map (TR c l.R l.Tplus).subtype = zpowers c.z := by
  have hc := Semidihedral.center_eq (by decide : 4 ≤ 4)
    l.rotation l.flip l.rotation_order l.flip_order l.flip_rotation l.generated
  rw [hc, MonoidHom.map_zpowers]
  change zpowers ((l.rotation : G) ^ 4) = zpowers c.z
  rw [l.rotation_four hσ]

include hσ in
theorem flip_z_order : orderOf ((l.flip : G) * c.z) = 2 := by
  rw [← l.rotation_four hσ]
  change orderOf (((l.flip * l.rotation ^ 4 : TR c l.R l.Tplus) : G)) = 2
  rw [Subgroup.orderOf_coe, ← l.equiv.orderOf_eq]
  simp only [map_mul, map_pow, flip, rotation, l.equiv.apply_symm_apply]
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

include hσ in
theorem marked_flip_z :
    markedMap c e ⟨(l.flip : G) * c.z,
      c.NB.mul_mem (TR_le_NB c l.R l.Tplus l.flip.property) (zInNB c).property⟩ =
      permutationAction (secondSwap (σ := σ)) := by
  change markedMap c e ((⟨l.flip, TR_le_NB c l.R l.Tplus l.flip.property⟩ : c.NB) * zInNB c) = _
  rw [map_mul, l.marked_flip, hσ]
  simp only [firstSwap, secondSwap, MulAut.conj_apply, map_mul, map_inv]
  have he : permutationAction standardZ *
      (permutationAction standardU * permutationAction standardZ) = permutationAction standardU := by
    rw [← map_mul, ← map_mul]
    exact congrArg permutationAction (by decide +kernel)
  calc
    _ = permutationAction σ *
        (permutationAction standardZ * (permutationAction standardU * permutationAction standardZ)) *
          (permutationAction σ)⁻¹ := by group
    _ = _ := by rw [he]

include hσ in
/-- The second marked involution also satisfies the literal source fusion premise. -/
theorem flip_z_fused (h7 : TranspositionFusion c e) :
    ∃ g : G, g * ((l.flip : G) * c.z) * g⁻¹ = c.z := by
  apply h7 ⟨(l.flip : G) * c.z,
    c.NB.mul_mem (TR_le_NB c l.R l.Tplus l.flip.property) (zInNB c).property⟩
  · rw [← Subgroup.orderOf_coe]
    exact l.flip_z_order hσ
  · exact ⟨secondSwap, secondSwap_isSwap, l.marked_flip_z hσ⟩

end Lift
end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction.Placement
