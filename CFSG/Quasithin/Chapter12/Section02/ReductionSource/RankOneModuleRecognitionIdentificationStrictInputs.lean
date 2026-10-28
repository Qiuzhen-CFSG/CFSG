module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationStrictRank
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictInputs

/-!
# G.11 inputs on the whole reduced Chapter12 layer

The moving residual cubic selects the literal crossing groups. The
source strict analysis then supplies the complete G.10 hypothesis,
the original Sylow relative normality, SQTK quotient presentation and
the type-a₂ involution, all for the same quotient and commutator form.

Source: Aschbacher--Smith, 6.2.18 and 12.2.2(3d). The remaining G.11.2
classification and alternative elimination belong to
qt-d-1222-recognition-strict-elimination. The existing final owner
qt-d-1222-rankone-recognition-identification discharges LocalAnalysis.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The G.10 and low-rank G.11 hypotheses on the actual whole reduced
layer, including the original Sylow image and SQTK covering map. -/
theorem strict_reduced_g11_inputs
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L (wholeReduced T L) <
      sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L) :
    ∃ d ∈ strictCrossingResidual (T : Subgroup G) L (wholeReduced T L),
      d ∈ L ∧ orderOf d = 3 ∧ d ∉ centralizer ({z} : Set G) ∧
    ∃ he : IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z),
      letI := he
      ∃ hX : IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d),
        letI := hX
        ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)))
          (v : Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)),
          let ρ := strictRepresentation (T : Subgroup G) L (wholeReduced T L) z
          let X := strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d
          let X₀ := (strictCrossingCenterImage (T : Subgroup G) L (wholeReduced T L) z d).subgroupOf X
          let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L (wholeReduced T L) z).ker
          let S := (T.subtype hTH).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
          ChapterG.Section10.Hypothesis ρ B v
            (strictHatSpace (T : Subgroup G) L (wholeReduced T L) z (strictCrossingIntersection (T : Subgroup G) L (wholeReduced T L) z d)) X X₀ ∧
          v ∈ strictSourceLine (T : Subgroup G) L (wholeReduced T L) z ∧
          (∀ u w : sourceClosure (T : Subgroup G) L (wholeReduced T L) z,
            B (strictHatElement (T : Subgroup G) L (wholeReduced T L) z u)
              (strictHatElement (T : Subgroup G) L (wholeReduced T L) z w) = 0 ↔ Commute u w) ∧
          4 ≤ Module.finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)) ∧
          Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple (StrictActor (T : Subgroup G) L (wholeReduced T L) z)) ∧
          (S : Subgroup (StrictActor (T : Subgroup G) L (wholeReduced T L) z)) ≤ ChapterG.Section10.pointCentralizer ρ v ∧
          X ≤ (S : Subgroup (StrictActor (T : Subgroup G) L (wholeReduced T L) z)) ∧
          (X.subgroupOf (S : Subgroup (StrictActor (T : Subgroup G) L (wholeReduced T L) z))).Normal ∧
          ∃ a ∈ X, a ≠ 1 ∧ a ^ 2 = 1 ∧
            Representation.RankTwo.movedSpace ρ a = strictCentralPlane (T : Subgroup G) L (wholeReduced T L) z ∧
            Module.finrank (ZMod 2) (Representation.RankTwo.movedSpace ρ a) = 2 ∧
            v ∈ Representation.RankTwo.movedSpace ρ a ∧
            (∀ w, B w (ρ a w) = 0) ∧
            ¬ Representation.RankTwo.StabilizerTransitive ρ (Representation.RankTwo.movedSpace ρ a) := by
  obtain ⟨d, hdres, hdL, hdS, _, hd3, hdH⟩ := strict_exists_crossing_cubic h611 hnatural hz horder
  exact ⟨d, hdres, hdL, hd3, hdH,
    A.strict_g11_inputs h611 hnatural hz horder hTH hstrict hdres hdH hdS hd3⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
