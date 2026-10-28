module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Simplicity of the actual chi-zero core quotients

The quotient by the block's intrinsic two-core is simple for every chi-zero
block. Its defining model is an actual PSL₂ over a field of order at least
four, A₃ of prime order, or A₅. Apply the proved simplicity results to those
models and transport through the supplied group isomorphisms.

Source: Aschbacher–Smith, C.1.12, printed p.124. The PSL₂ argument also
appears privately in Chapter E's `BlockSelection.Residual.Generation`;
this extension makes the intrinsic block fact available at its defining layer.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {K : Type*} [Group K]

/-- Every chi-zero block has simple quotient by its own two-core. -/
theorem IsChiZeroBlock.simple_quotient (h : IsChiZeroBlock K) :
    IsSimpleGroup (K ⧸ pCore 2 K) := by
  rcases h with ⟨n, hn, _, F, _, _, _, hm, _⟩ | h | h
  · obtain ⟨F', _, _, hcard, ⟨e⟩⟩ := hm
    have hfour : 4 ≤ Nat.card F' := by
      rw [hcard]
      exact show 2 ^ 2 ≤ 2 ^ n from Nat.pow_le_pow_right (by decide) hn
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F') :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
    exact e.isSimpleGroup
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    apply isSimpleGroup_of_prime_card (p := 3)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    exact e.isSimpleGroup

end CFSG.Quasithin.ChapterC

end
