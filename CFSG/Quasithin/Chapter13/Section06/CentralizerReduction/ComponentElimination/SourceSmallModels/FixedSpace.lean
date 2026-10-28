module

public import Theory.GroupAction.FixedQuotientCentralizer
public import Theory.GroupTheory.PResidual.PerfectCover
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceFixedSpace

/-!
# Transport of the small-model fixed-space calculation

The first result works with the actual C.1 block quotient U/C_U(K) and
its chosen equivariant identification. The second passes an ambient
centralizer equality to the literal checked quotient C_G(v)/⟨v⟩.
Here two-perfection of Lᵥ is derived from its definition as O²(C_L(v));
it kills the displacement into the central two-group kernel.

These results are transport steps in 13.6.22, not its case classification.
The family producers must construct the marked module and actor from the
source geometry. The final assembly must also construct the B.2.14
supplement used by `SourceFixedSpace`.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, pp.932–933.
-/

public section
open Subgroup
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.Source

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels

/-- A concrete action on the actual block quotient detects its intrinsic centralizer. -/
theorem block_centralizer_eq_of_model {K A W : Type*} [Group K] [Group A] [Group W]
    (ρ : A →* MulAut W) (model : BlockModuleModel K ρ) (D : Subgroup K)
    (hfree : ∀ w : W, (∀ d : D,
      ρ (model.quotientIso (QuotientGroup.mk' (pCore 2 K) d)) w = w) → w = 1) :
    blockU K ⊓ centralizer (D : Set K) = blockU K ⊓ center K := by
  apply le_antisymm _ (inf_le_inf_left _ (center_le_centralizer (D : Set K)))
  rintro u ⟨hu, hc⟩
  refine ⟨hu, ?_⟩
  have hz : model.moduleIso (QuotientGroup.mk' (blockFixed K) ⟨u, hu⟩) = 1 := by
    apply hfree
    intro d
    have hf : blockConjugate K d ⟨u, hu⟩ = ⟨u, hu⟩ := by
      apply Subtype.ext
      change (d : K) * u * (d : K)⁻¹ = u
      rw [hc d d.property, mul_inv_cancel_right]
    rw [← model.intertwining, hf]
  have hm : QuotientGroup.mk' (blockFixed K) ⟨u, hu⟩ = 1 :=
    model.moduleIso.injective (hz.trans (map_one model.moduleIso).symm)
  have hmem : (⟨u, hu⟩ : blockU K) ∈ blockFixed K :=
    (QuotientGroup.eq_one_iff _).mp hm
  exact hmem

/-- Centralizer comparison survives the specified checked quotient. -/
theorem checked_centralizer_eq_of_ambient {G : Type*} [Group G] [Finite G]
    (L K U : Subgroup G) (v : G) (hLK : Lv L v ≤ K)
    (hv : v ^ 2 = 1)
    (hfix : U ⊓ centralizer (Lv L v : Set G) = U ⊓ centralizer (K : Set G)) :
    checkedImage v U ⊓ centralizer (checkedImage v (Lv L v) : Set (Gcheck v)) =
      checkedImage v U ⊓ centralizer (checkedImage v K : Set (Gcheck v)) := by
  apply le_antisymm _ (inf_le_inf_left _
    (centralizer_le (map_mono (comap_mono hLK))))
  rintro x ⟨hxU, hxD⟩
  obtain ⟨u, hu, rfl⟩ := hxU
  refine ⟨mem_map.mpr ⟨u, hu, rfl⟩, ?_⟩
  have hDu := centralizes_of_checked_centralizes (Lv L v) v u (Lv_le_Gv L v)
    (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v)) hv hxD
  have huD : (u : G) ∈ centralizer (Lv L v : Set G) := by
    intro d hd
    exact mem_centralizer_singleton_iff.mp (hDu hd)
  have huK := (hfix.le ⟨hu, huD⟩).2
  rintro _ ⟨k, hk, rfl⟩
  exact congrArg (checkedQuotientMap v) (Subtype.ext (huK k hk))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
