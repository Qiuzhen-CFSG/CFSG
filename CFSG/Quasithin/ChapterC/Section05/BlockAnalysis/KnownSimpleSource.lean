module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.RankOneSetup
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple
/-!
# The original C.5 block producer with the full known-simple catalogue

The proved original C.1.28 outside-block theorem discharges the final
independent source input. The resulting producer constructs the actual
C.5.3 orbit, its original rank-one markings and the noncommuting conjugate
from C.5.1–2, with SQTK required only for the local subgroup H.

Source: Aschbacher–Smith C.5.1–5, printed pp.154–155, using C.1.28–29,
printed pp.133–134.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
universe u
variable {G : Type u} [Group G] [Finite G] {H M K R T : Subgroup G}

theorem c128Outside_knownSimple : C128Outside KnownSimple.IsKnownSimple := by
  intro A _ _ hA hf S N hc hn
  exact RankOne.ChiProduct.SelectedRankOne.outside_moved_chi_knownSimple hA hf S N hc hn

/-- Original C.5.3, with every earlier source premise discharged. -/
theorem OriginalHypotheses.block_decomposition_knownSimple
    (d : OriginalHypotheses H M K R T) (hH : IsSQTK KnownSimple.IsKnownSimple H) :
    Nonempty (OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H)
      (pResidual 2 H)) :=
  d.block_decomposition_of_local c128Outside_knownSimple hH

/-- The complete original block, rank-one marking and escaping-conjugate
producer used by C.5.6 and the original C.5.8 application. -/
theorem OriginalHypotheses.blocks_setups_and_noncommuting_conjugate_knownSimple
    (d : OriginalHypotheses H M K R T) (hH : IsSQTK KnownSimple.IsKnownSimple H) :
    ∃ b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H),
      (∀ i, (∃ (F : Type) (_ : Field F),
        Nonempty (ConjugateSource.RankOne.Setup R ((b.block i).map H.subtype) F)) ∨
        IsAlternatingBlock ((b.block i).map H.subtype) 5) ∧
      ∃ i₀ : Fin b.size, ∃ x ∈ M,
        ⁅moduleLayer ((b.block i₀).map H.subtype),
          (moduleLayer ((b.block i₀).map H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom⁆ ≠ ⊥ :=
  d.blocks_setups_and_noncommuting_conjugate c128Outside_knownSimple hH

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
