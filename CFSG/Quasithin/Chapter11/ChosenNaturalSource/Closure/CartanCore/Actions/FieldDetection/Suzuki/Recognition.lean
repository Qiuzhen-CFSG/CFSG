module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Components
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Recognition of the even-degree component quotient

The original point normalizer is an SQTK-group for the full known-simple
catalogue. Apply the proved A.3.6 classification to its actual component
image modulo the two-core. The three-prime exclusion eliminates every
non-Suzuki row, including the nonsimple rows. Transport back through the
intrinsic component quotient and the relative subgroup equivalence.

This proves the recognition step in Aschbacher--Smith 11.5.6(3), printed
pp.780--781. The invariant Borel and its normalizer action are separate
steps; the quotient below is literally I/O₂(I).
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Three-prime order identifies the actual relative component quotient.
All full K-group classification inputs are discharged. -/
theorem component_suzuki_of_three_free (hp : E.point ≠ ⊥)
    (hthree : ¬ 3 ∣ Nat.card E.Y) {I : Subgroup G}
    (hI : Source.ComponentIn E.Y I) :
    ∃ m : ℕ, 0 < m ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  have hH : IsSQTK KnownSimple.IsKnownSimple E.G₁ :=
    E.input.source.simpleQTKE.twoLocal_sqtk (D.centralQuotientPreimage_twoLocal E.point hp)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (E.G₁ ⧸ pCore 2 E.G₁) := by
    refine ⟨?_, hH.isKGroup.quotient (pCore 2 E.G₁)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp ho)
  let eI : I.subgroupOf E.G₁ ≃* I := subgroupOfEquivOfLe (hI.1.trans E.Y_le_G₁)
  have hi : Nat.Coprime 3 (Nat.card (I.subgroupOf E.G₁)) := by
    rw [Nat.card_congr eI.toEquiv]
    exact Nat.prime_three.coprime_iff_not_dvd.mpr
      (fun hd => hthree (hd.trans (card_dvd_of_le hI.1)))
  obtain ⟨m, hm, ⟨e⟩⟩ :=
    Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue.component_suzuki_quotient
      (ChapterA.SQTKStructure.a36Input_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
      hQ (E.component_in_point_normalizer hI) hi
  exact ⟨m, hm, ⟨(QuotientGroup.congr _ _ eI (pCore_map_iso 2 eI)).symm.trans e⟩⟩

/-- The even-degree source branch supplies its genuine Suzuki marking,
using the previously proved numerical conclusion 11.5.6(1). -/
theorem component_suzuki_of_even (hp : E.point ≠ ⊥)
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    (he : Even E.input.field.degree) {I : Subgroup G}
    (hI : Source.ComponentIn E.Y I) :
    ∃ m : ℕ, 0 < m ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
  E.component_suzuki_of_three_free hp (E.three_not_dvd_Y_of_even hc he) hI

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
