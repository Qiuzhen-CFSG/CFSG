module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.F9Application
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SeedNormalizer

/-!
# Original 13.5.7 and its closure consumers

The common-normal source argument discharges global seed-normalizer
control. The same marked Context now supplies every clause of F.9.1
for each original member of H_z. The universal earlier13.5.7 input and
the two conjugate-span equivalences use the literal Chapter13 subgroups.
Only the independent full A.3.12 embedding theorem remains explicit.
Source: Aschbacher–Smith 13.2.3 and13.5.7–10, pp.879,917–918.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
include d hA312

theorem source13_5_7
    (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
      (centralizer (V₁ : Set G)) (normalizer (L : Set G))) : SourceF91 T L V V₃ V₁ H :=
  sourceF91_of_earlier_geometry d (inf_le_right.trans (d.seed_normalizer hA312)) hH

/-- The exact universal input used by the later Chapter13 source consumers. -/
theorem earlier1357 : Earlier1357 T L V V₃ V₁
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)) :=
  fun _ hH => source13_5_7 d hA312 hH

/-- Original13.5.10 and the literal quotient-action kernel, with their
F.9.1 setup now constructed from the original marked source context. -/
theorem source13_5_10
    (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
      (centralizer (V₁ : Set G)) (normalizer (L : Set G))) :
    ((IsMulCommutative (conjugateSpanBy V₃ H) ↔ IsMulCommutative (conjugateSpanBy V H)) ∧
      (IsMulCommutative (conjugateSpanBy V₃ H) ↔ V ≤ H.pCoreIn 2)) ∧
      commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H :=
  span_and_kernel_of_earlier_geometry d (inf_le_right.trans (d.seed_normalizer hA312)) hH

end CFSG.Quasithin.Chapter13.Section05.A5Source
