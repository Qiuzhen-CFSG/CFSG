module

public import Theory.Mathieu.SchurMultipliers.M23TwoKernelSource.HeptadSection
public import Theory.Mathieu.SchurMultipliers.Models
public import Theory.GroupTheory.PerfectCentralCoverLocalSplitting
public import Theory.GroupTheory.PGroup.MaximalIndex

/-!
# Triviality of the native M₂₃ perfect central kernel

The proved odd-prime exclusions leave a two-group kernel. A nontrivial
kernel has a subgroup of index two; quotienting by its central image
gives a perfect double cover of the same native model. The marked
heptad section and odd-index transfer exclude that cover.
-/

public section
noncomputable section
open Subgroup PerfectCentralCovering
namespace Sporadic.Mathieu.SchurMultipliers.M23TwoKernelSource

/-- Every finite perfect central cover of the actual M₂₃ has trivial kernel. -/
theorem kernel_eq_bot {E : Type*} [Group E] [Finite E]
    (f : Cover E M23) : f.toMonoidHom.ker = ⊥ := by
  classical
  by_contra hne
  let : Nontrivial f.toMonoidHom.ker := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hp := PartialInversionSource.m23_cover_kernel_isTwoGroup f
  obtain ⟨K, hK⟩ := IsCoatomic.exists_coatom (α := Subgroup f.toMonoidHom.ker)
  have hi : K.index = 2 := hp.index_of_isCoatom K hK
  let D : Subgroup E := K.map f.toMonoidHom.ker.subtype
  have hD : D ≤ f.toMonoidHom.ker := map_subtype_le _
  let : D.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (f.ker_le_center (hD hx)) g, mul_inv_cancel_right]
    exact hx⟩
  let g := f.quotientKernelSubgroup D hD
  have hDcard : Nat.card D = Nat.card K :=
    card_map_of_injective f.toMonoidHom.ker.subtype_injective
  have hcount := f.card_kernel_quotientKernelSubgroup D hD
  have hKcount := K.card_mul_index
  rw [hi] at hKcount
  have hg : Nat.card g.toMonoidHom.ker = 2 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := D))
    calc
      Nat.card D * Nat.card g.toMonoidHom.ker = Nat.card f.toMonoidHom.ker := hcount.symm
      _ = Nat.card K * 2 := hKcount.symm
      _ = Nat.card D * 2 := by rw [hDcard]
  exact double_cover_false g hg

/-- The same result for the literal constructed universal projection. -/
theorem universal_kernel_eq_bot : (universalProjection M23).ker = ⊥ :=
  kernel_eq_bot (universalCover M23)

end Sporadic.Mathieu.SchurMultipliers.M23TwoKernelSource
