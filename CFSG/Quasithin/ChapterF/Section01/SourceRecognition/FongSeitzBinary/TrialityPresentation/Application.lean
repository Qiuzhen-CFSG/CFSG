module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialityPresentation.Markings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.CartanTransport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GenericApplication
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue

/-!
# Original and carrier-general triality comparisons for Chapter 12

Compose the proved full marking with any original/geometric amalgam marking.
Both inclusion squares and all three representative formulas use the same
ambient equivalence, including every element of the original overlap. The
literal generated-group specialization retains its original quotient map.
Both endpoint orientations give the genuine triality catalogue constructor.

For the selected generic factor, Preparation.hypothesisF11 supplies the original
F.1.1 hypothesis from Input and T≤H. It identifies the original Sylow image and
retains both original odd Cartans inside the complete native Borel. The output
is the exact sourceParabolicAmalgam comparison consumed in Chapter12, with no
stronger assumption that a geometric quotient descends to the generated group.
Source: DGS Theorem D, printed p.224; Aschbacher–Smith F.1.1–12 and 12.2.2.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation
open Chapter6.Source.RankOneGeneric
variable {G X F : Type*} [Group G] [Group X] [Field F]
variable {Psrc : Fin 2 → Subgroup X} {Q : MarkedQuotient Psrc} {split : SplitData Q.tits}
variable {m : ℕ} {hm : 0 < m} {σ : F ≃+* F} {armIndex : Fin 2}
local notation "P" => binaryParameters m hm

namespace RootData
variable (d : RootData Q split m hm σ armIndex)
variable {A C Z : Type*} [Group A] [Group C] [Group Z] {α : RankTwoAmalgam A C Z}
  (e0 : RankTwoAmalgam.Iso α Q.standardAmalgam)

/-- Carrier-general composition, including independently marked geometric quotients. -/
def comparison : RankTwoAmalgam.Iso α (flagAmalgam m hm armIndex) := e0.trans d.markedIso

@[simp] theorem comparison_left_apply (a : A) :
    ((d.comparison e0).left a : BinaryCarrier m hm) =
      d.bruhat.quotientEquiv (e0.left a : X ⧸ Q.D) := rfl
@[simp] theorem comparison_middle_apply (a : C) :
    ((d.comparison e0).middle a : BinaryCarrier m hm) =
      d.bruhat.quotientEquiv (e0.middle a : X ⧸ Q.D) := rfl
@[simp] theorem comparison_right_apply (a : Z) :
    ((d.comparison e0).right a : BinaryCarrier m hm) =
      d.bruhat.quotientEquiv (e0.right a : X ⧸ Q.D) := rfl

theorem comparison_left_square (a : C) :
    (d.comparison e0).left (α.left a) = (flagAmalgam m hm armIndex).left ((d.comparison e0).middle a) :=
  (d.comparison e0).left_commutes a

theorem comparison_right_square (a : C) :
    (d.comparison e0).right (α.right a) = (flagAmalgam m hm armIndex).right ((d.comparison e0).middle a) :=
  (d.comparison e0).right_commutes a

include d e0 in
/-- The complete genuine triality row, in either orientation. -/
theorem concreteComparison : Global.ConcreteAmalgamComparison α := by
  fin_cases armIndex
  · exact .triality m hm (Or.inl ⟨d.comparison e0⟩)
  · exact .triality m hm (Or.inr ⟨d.comparison e0⟩)
end RootData

section Original
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q₀ : SourceQuotient L S) {split₀ : SplitData Q₀.tits}
  (d : RootData Q₀ split₀ m hm σ armIndex)

/-- The generated original quotient uses its original endpoint inclusions. -/
def originalComparison := d.comparison (originalMarkedIso Q₀)

@[simp] theorem originalComparison_left_apply (a : parabolic L S 0) :
    ((originalComparison Q₀ d).left a : BinaryCarrier m hm) =
      d.bruhat.quotientEquiv (Q₀.q ⟨a,parabolic_le_generated 0 a.property⟩) := by
  rw [originalComparison, RootData.comparison_left_apply, originalMarkedIso_left_apply]
@[simp] theorem originalComparison_middle_apply (a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((originalComparison Q₀ d).middle a : BinaryCarrier m hm) =
      d.bruhat.quotientEquiv (Q₀.q ⟨a,parabolic_le_generated 0 a.property.1⟩) := by
  rw [originalComparison, RootData.comparison_middle_apply, originalMarkedIso_middle_apply]
@[simp] theorem originalComparison_right_apply (a : parabolic L S 1) :
    ((originalComparison Q₀ d).right a : BinaryCarrier m hm) =
      d.bruhat.quotientEquiv (Q₀.q ⟨a,parabolic_le_generated 1 a.property⟩) := by
  rw [originalComparison, RootData.comparison_right_apply, originalMarkedIso_right_apply]
end Original

section Local
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (e0 : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0) (parabolic L S 0 ⊓ parabolic L S 1)
      (parabolic L S 1) inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (d : RootData Q split m hm σ armIndex)

/-- The entire original common Borel follows the same middle map. -/
theorem comparison_commonBorel_apply (b : commonBorel L S) :
    ((d.comparison e0).middle ((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm) b) : BinaryCarrier m hm) =
      d.bruhat.quotientEquiv (MarkedLocal.borelMap Q e0 h b) := rfl

/-- The original Sylow image is the actual native positive subgroup. -/
theorem source_sylow_image :
    (MarkedLocal.sylowMap Q e0 h).range.map d.bruhat.quotientEquiv.toMonoidHom =
      Parabolics.unipotent P := by
  rw [MarkedLocal.sylow_range Q e0 h split]
  exact d.bruhat.quotientEquiv_unipotent

include h in
/-- Both original odd Cartans lie in the complete model Borel under this same equivalence. -/
theorem source_cartans (i : Fin 2) :
    Nat.Coprime 2 (Nat.card (MarkedLocal.localCartan Q e0 i)) ∧
      (MarkedLocal.localCartan Q e0 i).map
        (d.bruhat.quotientEquiv.toMonoidHom.comp (MarkedLocal.factorMap Q e0 i)) ≤ Parabolics.borel P := by
  refine ⟨(MarkedLocal.localCartan_complement Q e0 h split i).2.1,?_⟩
  rw [← Subgroup.map_map, MarkedLocal.localCartan_image, ← d.bruhat.quotientEquiv_borel]
  exact map_mono (inf_le_right.trans inf_le_left)
end Local

section Selected
variable [Finite G] {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (prep : Global.Preparation T L H A B R) (h : Input κ T L W n) (hTH : (T : Subgroup G) ≤ H)
  (d : RootData Q split m hm σ armIndex)
  (e0 : RankTwoAmalgam.Iso (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)

/-- The literal Chapter12 comparison type, with the original F.1.1 supplied by preparation.
The quotient carrier may be geometric; no universal-to-generated-group descent is assumed. -/
theorem selectedFactorComparison :
    Global.ConcreteAmalgamComparison (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
    (MarkedLocal.sylowMap Q e0 (prep.hypothesisF11 h hTH)).range.map d.bruhat.quotientEquiv.toMonoidHom =
      Parabolics.unipotent P ∧
    ∀ i : Fin 2, Nat.Coprime 2 (Nat.card (MarkedLocal.localCartan Q e0 i)) ∧
      (MarkedLocal.localCartan Q e0 i).map
        (d.bruhat.quotientEquiv.toMonoidHom.comp (MarkedLocal.factorMap Q e0 i)) ≤ Parabolics.borel P :=
  ⟨d.concreteComparison e0,source_sylow_image e0 (prep.hypothesisF11 h hTH) d,
    source_cartans e0 (prep.hypothesisF11 h hTH) d⟩
end Selected
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation
