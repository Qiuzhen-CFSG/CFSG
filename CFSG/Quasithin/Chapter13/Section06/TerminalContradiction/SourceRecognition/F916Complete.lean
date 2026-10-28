module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.F916Source

/-!
# The marked A₅ terminal argument with F.9.16 proved

The original marked context supplies the abelian centralizer closure. The
proved F.9.16 construction then produces its quadratic witness on the actual
quotient U_H/V₁. Thus the terminal contradiction has no F.9 callback; the
remaining component, embedding and small-ratio classification inputs retain
their original scope.

Source: Aschbacher–Smith F.9.16(3) and the final argument of 13.6,
printed pp.323–324 and 935.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Ratio Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original marked A₅ terminal argument with closure and F.9 setup supplied. -/
theorem terminal_contradiction_of_marked_A5_F916
    (d : Context T L V V₁ V₂ V₃)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (coordinates : FiveCoordinates V) (v z : V)
    (hv : BinaryPermutation.FiveGeometry.form (coordinates.equiv v).toAdd ≠ 0)
    (hz : z ≠ 1) (hzline : zpowers z.val = V₁)
    (hqz : BinaryPermutation.FiveGeometry.form (coordinates.equiv z).toAdd = 0)
    (hAlt : alternatingGroup (Fin 5) ≤ coordinates.actor.range)
    (hfusion : ∀ x : V, x ≠ 1 → ∀ a : G, MulAut.conj a x.val ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n x.val = MulAut.conj a x.val)
    (hCv : centralizer ({v.val} : Set G) ≤ normalizer (V : Set G))
    (hmark : ∀ x : V, x.val ∈ V₃ ↔ (coordinates.equiv x).toAdd.val 4 = 0)
    (houtside : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hcounter : CentralizerReduction.IsA5Counterexample G)
    (hcomponents : Components.Conclusion
      ((T : Subgroup G).subgroupOf (centralizer ({z.val} : Set G))))
    (hB45 : Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.FullB45.{u,u}
      KnownSimple.IsKnownSimple) : False := by
  let := SourceAbelian.source_closure_abelian d hA312 z.val hzline houtside hcounter
  exact terminal_contradiction_of_marked_A5_source d hA312 coordinates v z hv hz hzline
    hqz hAlt hfusion hCv hmark houtside hcounter hcomponents
    (earlierF9163_of_five coordinates v z hv hz hqz hAlt hfusion hCv hmark
      (d.seed_normalizer hA312)) hB45

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
