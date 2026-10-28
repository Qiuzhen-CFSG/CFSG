module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.PairImages
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.KernelCentralizer

/-!
# Native kernel centralizers with the marked pair retained

The literal quotient image includes the Figure 1 pair permutation. Its kernel
centralizer has order sixteen in all four rows. The equalities concern the
original Mathieu kernel embedded in J4, not only a finite coordinate model.
Source: Kleidman--Wilson (1988), Figures 1(b,c), 2(b,d), and 2.3.4--2.3.5.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Cardinality Cardinality.QuotientCount.Image SylowCore SylowCore.Transport
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup
local notation "L" => SylowCore.Local
local notation "E" => localKernel matrixA_mul_self matrixB_pow_four
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four
local notation "e" => maskEquiv matrixA_mul_self matrixB_pow_four

/-- The whole pair-row fixed space is the corresponding unprimed fixed space. -/
theorem fixedTest_iff_pairRow (r : Fin 4) (m : Fin 2048) :
    fixedTest (unprimedRow r) m ↔
      ∀ g ∈ pairRowImage r, starMask g m.val = m.val := by
  rw [pairRowImage, starMask_closure_fixed_iff, ← pair_fixedTest]
  constructor
  · rintro ⟨hrow,hpair⟩ j
    unfold pairRowGenerator
    split_ifs with hj
    · rw [rowGenerator_mask]
      exact hrow ⟨j.val,hj⟩
    · rwa [pairPermutation_mask]
  · intro h
    refine ⟨?_, ?_⟩
    · intro j
      have hj := h (j.castLE (by decide))
      simpa only [pairRowGenerator, Fin.val_castLE, dif_pos j.isLt,
        rowGenerator_mask] using hj
    · exact (pairPermutation_mask m.val) ▸ h 3

/-- An exact equation for every native subgroup with the specified whole image. -/
theorem mask_mem_pairRow_centralizer_iff (A : Subgroup L) (r : Fin 4)
    (hrow : A.map π = pairRowImage r) (m : Fin 2048) :
    (e m : L) ∈ centralizer (A : Set L) ↔ fixedTest (unprimedRow r) m := by
  rw [mask_mem_centralizer_iff_image, hrow, ← fixedTest_iff_pairRow]

/-- Every centralizing kernel element occurs, and its bounded mask is unique. -/
def pairFixedMasksEquiv (A : Subgroup L) (r : Fin 4)
    (hrow : A.map π = pairRowImage r) :
    fixedMasks (unprimedRow r) ≃ (centralizer (A : Set L)).subgroupOf E where
  toFun m := ⟨e m.val, (mask_mem_pairRow_centralizer_iff A r hrow m.val).mpr m.property⟩
  invFun x := ⟨(e).symm x.val, (mask_mem_pairRow_centralizer_iff A r hrow ((e).symm x.val)).mp
    (by simpa only [(e).apply_symm_apply] using
      (show (x.val : L) ∈ centralizer (A : Set L) from x.property))⟩
  left_inv m := Subtype.ext ((e).symm_apply_apply m.val)
  right_inv x := Subtype.ext ((e).apply_symm_apply x.val)

theorem pairRow_kernel_centralizer_card (A : Subgroup L) (r : Fin 4)
    (hrow : A.map π = pairRowImage r) :
    Nat.card ((centralizer (A : Set L)).subgroupOf E) = 16 := by
  rw [← Nat.card_congr (pairFixedMasksEquiv A r hrow)]
  fin_cases r
  · exact fixedMasks0_card
  · exact fixedMasks1_card
  · exact fixedMasks0_card
  · exact fixedMasks1_card

/-- The comparison retains the original ambient inclusion on every element. -/
theorem kernelCentralizer_map (A : Subgroup L) :
    ((centralizer (A : Set L)).subgroupOf E).map ((L).subtype.comp (E).subtype) =
      centralizer (A.map (L).subtype : Set Model) ⊓ (E).map (L).subtype := by
  ext z
  constructor
  · rintro ⟨k,hk,rfl⟩
    refine ⟨?_, mem_map_of_mem (L).subtype k.property⟩
    rintro _ ⟨a,ha,rfl⟩
    exact congrArg (fun w : L => (w : Model)) (hk a ha)
  · rintro ⟨hc,k,hk,rfl⟩
    refine mem_map.mpr ⟨⟨k,hk⟩, ?_, rfl⟩
    intro a ha
    apply Subtype.ext
    exact hc a (mem_map_of_mem (L).subtype ha)

/-- The ambient kernel intersection has order sixteen in every selected pair row. -/
theorem pairRow_ambient_kernel_centralizer_card
    (X : Subgroup Model) (hXL : X ≤ L) (r : Fin 4)
    (hrow : (X.subgroupOf L).map π = pairRowImage r) :
    Nat.card (centralizer (X : Set Model) ⊓ (E).map (L).subtype : Subgroup Model) = 16 := by
  rw [← map_subgroupOf_eq_of_le hXL, ← kernelCentralizer_map]
  rw [card_map_of_injective (f := (L).subtype.comp (E).subtype)
    (fun a b h => Subtype.ext (Subtype.ext h))]
  exact pairRow_kernel_centralizer_card _ r hrow

end Janko4.LocalStructure.ElementaryEightGeometry


