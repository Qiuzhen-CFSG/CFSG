module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.SourceInputs
public import Theory.GroupTheory.Commutator.NilpotentSaturation

/-!
# Full generation of the source seed

The actual marked natural action gives V₃=[V₃,L₁]V₁. The earlier source
identity 13.7.3(6) is V₁=[V₃,Q_H]. Since Q_H lies in the source Sylow T,
it normalizes both V₃ and L₁ and hence their commutator. Both V₃ and Q_H
are two-groups. Nilpotent commutator saturation removes [V₃,Q_H] from
the generating product, proving V₃=[V₃,L₁]. This supplies the seed
hypothesis of the existing centralizing contradiction without assuming
its fixedness, spanning, or faithfulness conclusions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.7.3(6), printed p.936; the last paragraph of 13.8.5, printed p.948.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter13.Section08
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable
variable {G : Type*} [Group G] [Finite G]

/-- Recover full seed generation from the literal earlier core commutator. -/
theorem seed_generation_of_core_displacement
    {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
    (s : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hmodels : Nonempty (TransvectionParabolic.EarlierCore.ComponentSetup T L V V₁ V₂ V₃) ∨
      Nonempty (NaturalSetup L (T : Subgroup G) V V₁ V₃))
    (hfactor : ∀ (W₁ W₃ : Subgroup G), NaturalSetup L (T : Subgroup G) V W₁ W₃ →
      one L T W₁ = plus L T W₁ ⊔ zero L)
    (hcore : V₁ = ⁅V₃, Source.QH H⁆) : V₃ = ⁅V₃, sourceOne L T V₁⁆ := by
  have hlocal : sourceOne L T V₁ ≤ normalizer (V₃ : Set G) ∧
      V₃ ≤ ⁅V₃, sourceOne L T V₁⁆ ⊔ V₁ := by
    rcases hmodels with hs | hs
    · obtain ⟨d⟩ := hs
      have he : sourceOne L T V₁ = TransvectionParabolic.EarlierCore.localResidual L V₁ :=
        d.extend.line_residual_eq
      rw [he]
      exact ⟨d.extend.one_normalizes_seed, d.extend.seed_eq_commutator_sup_line.le⟩
    · obtain ⟨d⟩ := hs
      refine ⟨?_, ?_⟩
      · change one L T V₁ ≤ _
        rw [hfactor V₁ V₃ d]
        exact sup_le d.plus_normalizes_seed
          ((d.zero_centralizes.trans (centralizer_le d.seed_le)).trans (centralizer_le_normalizer _))
      · have hc := d.seed_le_plus_commutator_sup (hfactor V₁ V₃ d)
        rw [commutator_comm] at hc
        exact hc.trans (sup_le_sup (commutator_mono le_rfl
          (plus_le_one L T V₁ s.line_stable)) le_rfl)
  have hQT : Source.QH H ≤ T := OneFactor.core_le_sourceSylow H T (le_sup_right.trans hH.1.2)
  have hn : Source.QH H ≤ normalizer ((⁅V₃, sourceOne L T V₁⁆ : Subgroup G) : Set G) := by
    intro q hq
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (s.seed_stable (hQT hq)),
      mem_normalizer_iff_map_conj_eq.mp (T_normalizes_one L T V₁ s.line_stable (hQT hq))]
  have hV3 : IsPGroup 2 V₃ := by
    let := s.uh_elementary hH
    exact (IsElementaryAbelian.isPGroup (p := 2) (G := Source.UH H V₃)).to_le
      (le_conjugateSpanBy V₃ H)
  have hle := le_normalizer_iff_commutator_le_left.mp hlocal.1
  apply le_antisymm _ hle
  apply le_of_le_sup_commutator_of_isPGroup V₃ ⁅V₃, sourceOne L T V₁⁆ (Source.QH H)
    hV3 (isPGroup_pCoreIn 2 H) hle (hQT.trans s.seed_stable) hn
  rw [← hcore]
  exact hlocal.2
end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable

end
