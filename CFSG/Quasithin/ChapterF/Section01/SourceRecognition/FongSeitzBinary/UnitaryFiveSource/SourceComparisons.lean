module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.ProfileComparisons

/-!
# Source U₅ comparisons with the complete scalar kernel

The earlier mixed-factor profile constructs FiveData and hence the exact
projective map, both endpoint maps and the whole Borel. In the generated
source specialization the three squares use the literal original quotient Q.q.
Source: Fong--Seitz II (8C), pp.202–210; DGS Theorem D, p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
open UnitaryPresentation UnitarySource.Combined Theory.SpecificGroups.UnitaryFive
variable {G X K E : Type*} [Group G] [Group X]
  [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (hm : rotationOrder Q = 4)
  (n : ℕ) (hn : 0 < n) (i j : Fin 2) (hij : i ≠ j)
  (p : FiveProfile L S Q split K E n i j)

include mark h hm hn hij in
/-- The original profile discharges every presentation equation and generation
premise before the scalar quotient and three marked squares are formed. -/
theorem profile_projective_comparison :
    ∃ (d : FiveData Q split j (fiveForm p.form)) (κ : E) (hκ : κ + (fiveForm p.form).conj κ = 1)
      (f : ProjectiveSpecialUnitaryMatrixGroup (fiveForm p.form) ≃* (X ⧸ Q.D))
      (c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (MarkedAmalgam.flag (lineParabolic (fiveForm p.form)) (planeParabolic (fiveForm p.form)) j)),
      (d.modelHom (fiveForm p.form) κ hκ rfl).ker = (project (fiveForm p.form)).ker ∧
      (∀ a, f (project (fiveForm p.form) a) = d.modelHom (fiveForm p.form) κ hκ rfl a) ∧
      (lineParabolic (fiveForm p.form) ⊓ planeParabolic (fiveForm p.form)).map f.toMonoidHom = Q.tits.B ∧
      (lineParabolic (fiveForm p.form)).map f.toMonoidHom = Q.tits.standardParabolic {Q.simple j} ∧
      (planeParabolic (fiveForm p.form)).map f.toMonoidHom = Q.tits.standardParabolic {Q.simple (1-j)} ∧
      (∀ a : parabolic L S 0, (c.left a : ProjectiveSpecialUnitaryMatrixGroup (fiveForm p.form)) =
        f.symm (mark.left a : X ⧸ Q.D)) ∧
      (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
        (c.middle a : ProjectiveSpecialUnitaryMatrixGroup (fiveForm p.form)) =
          f.symm (mark.middle a : X ⧸ Q.D)) ∧
      (∀ a : parabolic L S 1, (c.right a : ProjectiveSpecialUnitaryMatrixGroup (fiveForm p.form)) =
        f.symm (mark.right a : X ⧸ Q.D)) := by
  obtain ⟨d⟩ := profile_native_data Q split mark h hm n hn i j hij p
  exact ⟨d,marked_fiveData_comparison p.form n p.unitary_card Q split mark h hm p.fixed_card d⟩

include h hn hij in
/-- The source-profile comparison preserves literal quotient representatives
on both original endpoints and their entire intersection. -/
theorem profile_original_comparison (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm₀ : rotationOrder Q₀ = 4) (p : FiveProfile L S Q₀ split₀ K E n i j) :
    ∃ (d : FiveData Q₀ split₀ j (fiveForm p.form)) (κ : E) (hκ : κ + (fiveForm p.form).conj κ = 1)
      (f : ProjectiveSpecialUnitaryMatrixGroup (fiveForm p.form) ≃* ((generated L S) ⧸ Q₀.D))
      (c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (MarkedAmalgam.flag (lineParabolic (fiveForm p.form)) (planeParabolic (fiveForm p.form)) j)),
      (d.modelHom (fiveForm p.form) κ hκ rfl).ker = (project (fiveForm p.form)).ker ∧
      (∀ a, f (project (fiveForm p.form) a) = d.modelHom (fiveForm p.form) κ hκ rfl a) ∧
      (lineParabolic (fiveForm p.form) ⊓ planeParabolic (fiveForm p.form)).map f.toMonoidHom = Q₀.tits.B ∧
      (lineParabolic (fiveForm p.form)).map f.toMonoidHom = Q₀.tits.standardParabolic {Q₀.simple j} ∧
      (planeParabolic (fiveForm p.form)).map f.toMonoidHom = Q₀.tits.standardParabolic {Q₀.simple (1-j)} ∧
      (∀ a : parabolic L S 0, (c.left a : ProjectiveSpecialUnitaryMatrixGroup (fiveForm p.form)) =
        f.symm (Q₀.q ⟨a,parabolic_le_generated 0 a.property⟩)) ∧
      (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
        (c.middle a : ProjectiveSpecialUnitaryMatrixGroup (fiveForm p.form)) =
          f.symm (Q₀.q ⟨a,parabolic_le_generated 0 a.property.1⟩)) ∧
      (∀ a : parabolic L S 1, (c.right a : ProjectiveSpecialUnitaryMatrixGroup (fiveForm p.form)) =
        f.symm (Q₀.q ⟨a,parabolic_le_generated 1 a.property⟩)) := by
  simpa only [originalMarkedIso_left_apply,originalMarkedIso_middle_apply,
    originalMarkedIso_right_apply] using
    profile_projective_comparison Q₀ split₀ (originalMarkedIso Q₀) h hm₀ n hn i j hij p

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
