module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedJankoExcluded.CoverAssembly
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.JankoLargeCenterRadical.NativeQuotients
/-!
# The original binary doubled J₄ exclusion

The proved native cover discharges the final extra premise in the same
chosen-module placement. Maximality is among two-locals, and the original
normal residual and full-core quotient markings are preserved. The actual
source obstruction consequently retains the Rudvalis and maximal-pushing-up
alternatives.

Source: Aschbacher--Smith 4.4.3 and its original 12.2 application;
Kleidman--Wilson (1988), Section 2, pp.488--493.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory ChapterB.QuasisimpleSource
open Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Representation Representation.BinaryOffender BinaryLinearThree
open Janko4.LocalStructure.LargeCenterRadicals.LinearFiveLocal
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)


/-- Exclude the J₄ geometry with its original placed maps and witnesses. -/
theorem native_janko_geometry_false
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (hg : D.BinaryPlacedNativeGeometry A K hr e) : False := by
  obtain ⟨m,_,hP,hN,hlarge,hq⟩ := D.native_janko_geometry_quotients_excluded A K hr e hg
  have hh := Janko4.LocalStructure.LargeCenterRadicals.radical_quotient _ hP hlarge
  rw [hN] at hh
  exact hq hh

/-- Apply the exclusion to the same original binary doubled component. -/
theorem sourceOrbit_binary_oddNormalizer_janko_false
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) (hcore : pCore 2 K = ⊥)
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Janko4.Model) : False := by
  exact sourceOrbit_binary_oddNormalizer_janko_false_of_cover
    D Janko4.LocalStructure.PureFirstNormalizers.CompleteCover.maximalTwoLocalCover h hd F hF hmodel A hAC ho hu K hK hcore hr e

/-- Remove precisely J₄ from the actual native placed case. -/
theorem binaryPlacedNativeCase_rudvalis
    (A : Subgroup G) (hc : D.BinaryPlacedNativeCase A) :
    D.BinaryPlacedNativeRudvalisCase A := by
  exact binaryPlacedNativeCase_rudvalis_of_janko_cover
    D Janko4.LocalStructure.PureFirstNormalizers.CompleteCover.maximalTwoLocalCover A hc

/-- The original obstruction retains its maximal-pushing-up and Rudvalis
alternatives, with the J₄ branch excluded. -/
theorem sourceOrbit_binary_rudvalis_oddLocal_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : D.SourceOrbitNonFF)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ A : Subgroup G,
        A ≤ H ∧ A ≤ centralizer (D.sourceOrbit : Set G) ∧ Nat.card A = p ∧
        ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
        ((∃ J P : Subgroup G,
          J ∈ muStar (normalizer (L : Set G)) L
            (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
          PushLE L (oddActorResidual L A) J ∧
          IsMaximalTwoLocal P ∧ J ≤ P ∧ ¬ P ≤ normalizer (L : Set G) ∧
          IsSQTK KnownSimple.IsKnownSimple P ∧ D.sourceOrbit ≤ J.pCoreIn 2 ∧
          J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
        D.BinaryPlacedNativeRudvalisCase A) := by
  exact sourceOrbit_binary_rudvalis_oddLocal_obstruction_of_janko_cover
    D Janko4.LocalStructure.PureFirstNormalizers.CompleteCover.maximalTwoLocalCover h hd hmany hnon F hF hmodel

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
