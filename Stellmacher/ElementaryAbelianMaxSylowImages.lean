module

public import Stellmacher.ElementaryAbelianMaxFamilyMap
public import Theory.GroupTheory.SylowImageLocalization

/-!
# Maximal elementary images in a chosen Sylow subgroup

Sylow conjugacy identifies the maximal-order elementary families locally and
globally. Kernel conjugacy then localizes every global maximal elementary
image contained in the chosen Sylow image, preserving its literal image.

Source application: Aschbacher–Smith B.2.7–9, printed pp.76–77, in the
ordinary alternating-block argument of 13.6.22, printed p.932.
-/

public section
open Subgroup
open scoped Pointwise

namespace Stellmacher
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

theorem maxFamily_sylow_iff (R : Sylow 2 G) (A : Subgroup G) :
    A ∈ elementaryAbelianMaxSubgroups (R : Subgroup G) ↔
      A ≤ R ∧ A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G) := by
  constructor
  · intro hA
    refine ⟨hA.1, le_top, hA.2.1, ?_⟩
    intro B _ hB
    obtain ⟨S, hBS⟩ := hB.isPGroup.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S R
    have hSR : (S : Subgroup G).map (MulAut.conj g).toMonoidHom = R := by
      change ((g • S : Sylow 2 G) : Subgroup G) = _
      rw [hg]
    have hc := hA.2.2 _ ((map_mono hBS).trans hSR.le)
      (hB.map (MulAut.conj g).toMonoidHom)
    rwa [card_map_of_injective (MulAut.conj g).injective] at hc
  · rintro ⟨hAR, _, he, hmax⟩
    exact ⟨hAR, he, fun B _ hB => hmax B le_top hB⟩

theorem exists_maxFamily_sylow_same_image (R : Sylow 2 G) (q : G →* Q)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G))
    (hAR : A.map q ≤ (R : Subgroup G).map q) :
    ∃ B ∈ elementaryAbelianMaxSubgroups (R : Subgroup G), B.map q = A.map q := by
  obtain ⟨g, hg, hBR⟩ := R.exists_kernel_conjugate_le q A hA.2.1.isPGroup hAR
  refine ⟨A.map (MulAut.conj g).toMonoidHom, ?_, ?_⟩
  · apply (maxFamily_sylow_iff R _).mpr
    refine ⟨hBR, ?_⟩
    have hm := (maxFamily_map_injective_iff (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective ⊤ A).mpr hA
    rwa [map_top_of_surjective _ (MulAut.conj g).surjective] at hm
  · rw [map_map]
    congr 1
    ext a
    simp [MonoidHom.comp_apply, MulAut.conj_apply, hg]
end Stellmacher
