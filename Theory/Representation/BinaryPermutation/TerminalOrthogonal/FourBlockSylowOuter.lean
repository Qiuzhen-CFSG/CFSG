module
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockPoint
public import Theory.GroupTheory.PGroup.CyclicInvolution
/-!
# Noncyclic Sylow images in the even four-block stabilizer

The simultaneous transposition in the two blocks and the interchange of
those blocks generate a four-group. They remain distinct involutions
modulo the literal Klein-four product, which is the intrinsic two-core.
Sylow conjugacy then rules out a cyclic Sylow image in this quotient.
Only the displayed permutations are computed; S₈ is not enumerated.

Source: Aschbacher--Smith 12.6.31, printed p.836, refs/quasithin.pdf.
The original point-group application is in NaturalSource.PointSylowOuter.
-/
public section
open Subgroup
namespace BinaryPermutation.TerminalOrthogonal.FourBlockResidual
open Theory.SpecificGroups.SymmetricEight
private def a : S8 := Equiv.swap 0 1 * Equiv.swap 4 5
private def b : S8 := Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7
private theorem a_mem : a ∈ P := by
  constructor
  · change Equiv.Perm.sign a = 1
    decide +kernel
  · change ∀ i j : Fin 8, (a i).val / 4 = (a j).val / 4 ↔ i.val / 4 = j.val / 4
    decide +kernel
private theorem b_mem : b ∈ P := by
  constructor
  · change Equiv.Perm.sign b = 1
    decide +kernel
  · change ∀ i j : Fin 8, (b i).val / 4 = (b j).val / 4 ↔ i.val / 4 = j.val / 4
    decide +kernel
private def W : Subgroup S8 where
  carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a*b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> decide +kernel
  inv_mem' := by
    rintro x (rfl | rfl | rfl | rfl) <;> decide +kernel
private theorem W_le : W ≤ P := by
  rintro x (rfl | rfl | rfl | rfl)
  · exact P.one_mem
  · exact a_mem
  · exact b_mem
  · exact P.mul_mem a_mem b_mem
private theorem W_two : IsPGroup 2 W := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  rintro ⟨x,hx⟩
  refine ⟨1,Subtype.ext ?_⟩
  rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Every Sylow two-subgroup of the even four-block group has noncyclic image
modulo its intrinsic two-core. -/
theorem sylow_core_image_not_cyclic (S : Sylow 2 P) :
    ¬ IsCyclic ((S : Subgroup P).map (QuotientGroup.mk' (pCore 2 P))) := by
  intro hc
  let q := QuotientGroup.mk' (pCore 2 P)
  let Sbar := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let Wp := W.subgroupOf P
  have hWp : IsPGroup 2 Wp := W_two.comap_subtype
  obtain ⟨Q,hQ⟩ := (hWp.map q).exists_le_sylow
  let : IsCyclic Sbar := hc
  let : IsCyclic Q := (Sbar.equiv Q).isCyclic.mp inferInstance
  let : IsCyclic (Wp.map q) := isCyclic_of_le hQ
  let x : Wp.map q := ⟨q ⟨a,a_mem⟩,mem_map_of_mem q (show (⟨a,a_mem⟩ : P) ∈ Wp from Or.inr (Or.inl rfl))⟩
  let y : Wp.map q := ⟨q ⟨b,b_mem⟩,mem_map_of_mem q (show (⟨b,b_mem⟩ : P) ∈ Wp from Or.inr (Or.inr (Or.inl rfl)))⟩
  have hk (g : P) (hg : q g = 1) : (g : S8) ∈ FourBlockCoreAction.kleinGroup := by
    have hm := mem_map_of_mem P.subtype ((QuotientGroup.eq_one_iff _).mp hg)
    change (g : S8) ∈ P.pCoreIn 2 at hm
    rwa [FourBlockPoint.intermediate_core P R_le_P inf_le_right] at hm
  have hx : orderOf x = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      change (q ⟨a,a_mem⟩)^2 = 1
      rw [←map_pow,show (⟨a,a_mem⟩ : P)^2=1 by apply Subtype.ext; decide +kernel,map_one]
    · intro he
      have hh := hk ⟨a,a_mem⟩ (congrArg Subtype.val he)
      exact (by decide +kernel : ¬ ∃ i j : Fin 4, a = FourBlockCoreAction.kleinPerm i j) hh
  have hy : orderOf y = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      change (q ⟨b,b_mem⟩)^2 = 1
      rw [←map_pow,show (⟨b,b_mem⟩ : P)^2=1 by apply Subtype.ext; decide +kernel,map_one]
    · intro he
      have hh := hk ⟨b,b_mem⟩ (congrArg Subtype.val he)
      exact (by decide +kernel : ¬ ∃ i j : Fin 4, b = FourBlockCoreAction.kleinPerm i j) hh
  have he : q ⟨a,a_mem⟩ = q ⟨b,b_mem⟩ := congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two hx hy)
  have hh := hk (⟨a,a_mem⟩ * ⟨b,b_mem⟩⁻¹) (by rw [map_mul,map_inv,he,mul_inv_cancel])
  exact (by decide +kernel : ¬ ∃ i j : Fin 4, a*b⁻¹ = FourBlockCoreAction.kleinPerm i j) hh
end BinaryPermutation.TerminalOrthogonal.FourBlockResidual
