module
public import Theory.Representation.BinaryConjugationSection.ImageDimensions

/-!
# Displacement bounds on literal binary sections

If the section denominator contains Z, the image of C has at most |C:C∩Z|
elements, even when C is not contained in the upper endpoint. A commutator
bound into C therefore bounds the displacement of each specified actor on
that same section. This does not assume that a larger containing group is
elementary abelian or that its action is faithful.

When the displacement attains the index bound, both index towers saturate:
C lies in the upper endpoint and its intersection with the kernel is Z.

Source application: Aschbacher--Smith 15.2.27(2), printed p.1119, passing
the bound on (V∩Qc)/Z to the actual binary chief action.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] [Finite G] {H U B : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W}

/-- A subgroup image cannot grow when the section kernel contains Z. -/
theorem imageSpace_card_le_relative_index
    (d : BinaryConjugationSection H U B ρ) (C Z : Subgroup G) (hZB : Z ≤ B) :
    Nat.card (d.imageSpace C) ≤ Z.relIndex C := by
  have he : d.imageSpace C = d.imageSpace (C ⊓ U) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := (d.mem_imageSpace_iff C v).mp hv
      exact (d.mem_imageSpace_iff (C ⊓ U) _).mpr ⟨u, ⟨hu,u.property⟩,rfl⟩
    · exact d.imageSpace_mono inf_le_left
  rw [he,d.imageSpace_card_eq_relIndex _ inf_le_right]
  exact (relIndex_le_of_le_left hZB
    ((Z.subgroupOf (C ⊓ U)).index_ne_zero_of_finite)).trans
    (relIndex_le_of_le_right inf_le_left ((Z.subgroupOf C).index_ne_zero_of_finite))

/-- An actual commutator bound gives the same displacement bound on every actor. -/
theorem displacement_rank_le_of_commutator_bound
    (d : BinaryConjugationSection H U B ρ) (A C Z : Subgroup G)
    (hZB : Z ≤ B) (hc : ⁅A,U⁆ ≤ C) (n : ℕ) (hn : Z.relIndex C ≤ 2^n)
    (a : H) (ha : (a : G) ∈ A) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≤ n := by
  let : Finite W := Finite.of_surjective (fun u : U => (d.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp d.onto)
  have hcard := (d.imageSpace_card_le_relative_index C Z hZB).trans hn
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hcard
  exact (Submodule.finrank_mono
    (d.displacement_range_le_imageSpace_of_commutator_le A C hc a ha)).trans
    ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard)

/-- Saturation of the displacement bound retains the whole controlling
subgroup in the upper endpoint and its exact intersection with the kernel. -/
theorem endpoints_of_displacement_saturation
    (d : BinaryConjugationSection H U B ρ) (A C Z : Subgroup G)
    (hZC : Z ≤ C) (hZB : Z ≤ B) (hc : ⁅A,U⁆ ≤ C)
    (n : ℕ) (hn : Z.relIndex C ≤ 2^n)
    (a : H) (ha : (a : G) ∈ A)
    (hr : n ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1))) :
    C ≤ U ∧ C ⊓ B = Z ∧ Z.relIndex C = 2^n := by
  let : Finite W := Finite.of_surjective (fun u : U => (d.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp d.onto)
  have hrI : n ≤ Module.finrank (ZMod 2) (d.imageSpace C) := hr.trans
    (Submodule.finrank_mono
      (d.displacement_range_le_imageSpace_of_commutator_le A C hc a ha))
  have hcard : 2^n ≤ Nat.card (d.imageSpace C) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hrI
  have he : Z.relIndex C = 2^n :=
    le_antisymm hn (hcard.trans (d.imageSpace_card_le_relative_index C Z hZB))
  have hZI : Z ≤ C ⊓ U := le_inf hZC (hZB.trans d.kernel_le)
  have hIC : d.imageSpace C = d.imageSpace (C ⊓ U) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨u,hu,rfl⟩ := (d.mem_imageSpace_iff C v).mp hv
      exact (d.mem_imageSpace_iff (C ⊓ U) _).mpr ⟨u,⟨hu,u.property⟩,rfl⟩
    · exact d.imageSpace_mono inf_le_left
  have hI : 2^n ≤ Z.relIndex (C ⊓ U) := by
    rw [hIC] at hcard
    exact hcard.trans (d.imageSpace_card_le_relative_index (C ⊓ U) Z hZB)
  have ht := relIndex_mul_relIndex Z (C ⊓ U) C hZI inf_le_left
  rw [he] at ht
  have hip : 0 < (C ⊓ U).relIndex C :=
    Nat.pos_of_ne_zero ((C ⊓ U).subgroupOf C).index_ne_zero_of_finite
  have hnp : 0 < 2^n := pow_pos (by decide) _
  have hi : (C ⊓ U).relIndex C = 1 := by nlinarith
  have hCU : C ≤ U := (relIndex_eq_one.mp hi).trans inf_le_right
  have hB : 2^n ≤ B.relIndex C := by
    rw [d.imageSpace_card_eq_relIndex C hCU] at hcard
    exact hcard
  have htB := relIndex_inf_mul_relIndex Z B C
  rw [inf_eq_left.mpr hZB,he] at htB
  have hBp : 0 < Z.relIndex (B ⊓ C) :=
    Nat.pos_of_ne_zero (Z.subgroupOf (B ⊓ C)).index_ne_zero_of_finite
  have heB : Z.relIndex (B ⊓ C) = 1 := by nlinarith
  exact ⟨hCU,le_antisymm (by rw [inf_comm]; exact relIndex_eq_one.mp heB)
    (le_inf hZC hZB),he⟩

end Representation.BinaryConjugationSection
