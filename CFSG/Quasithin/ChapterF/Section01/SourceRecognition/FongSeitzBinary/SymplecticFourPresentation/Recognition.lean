module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2Presentation.Markings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticFourPresentation.Weyl
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.SymplecticFour

/-!
# Original F.1.1 symplectic recognition from the eight-root presentation

The root presentation constructs an ambient equivalence on the same finite
marked quotient. Genuine F.1.1 transports local characteristic two through
the supplied endpoint maps, discharging both parabolic-recognition premises.
Restricting the one ambient equivalence and composing the original marking
gives the concrete point/Borel/plane amalgam with both inclusion squares.
The generated-source specialization retains its literal numerator and quotient
map. Field and mixed-root reconstruction remain explicit source inputs;
no ambient completion recognition or universal-to-source descent is asserted.

Source: DGS Theorem D, pp.224–226; Aschbacher–Smith F.1.1 and F.1.12,
pp.259–264; Steinberg §6, Theorems 8–9, pp.68–74.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticFourPresentation
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (d : C2Presentation.RootData (F := F) Q split)

include e h in
/-- The same ambient equivalence maps U, the whole Borel, and both correctly
oriented original quotient parabolics. F.1.1 supplies local characteristic two. -/
theorem subgroup_images :
    split.U.map d.equiv.toMonoidHom = unipotent (F := F) ∧
    Q.tits.B.map d.equiv.toMonoidHom = Theory.SpecificGroups.SymplecticFour.borel (F := F) ∧
    (Q.tits.standardParabolic {Q.simple 0}).map d.equiv.toMonoidHom = pointParabolic (F := F) ∧
    (Q.tits.standardParabolic {Q.simple 1}).map d.equiv.toMonoidHom = planeParabolic (F := F) :=
  ⟨d.map_unipotent,d.map_borel,
    d.map_point (MarkedLocal.parabolic_core_selfCentralizing Q e h),
    d.map_plane (MarkedLocal.parabolic_core_selfCentralizing Q e h)⟩

/-- The literal original/geometric amalgam comparison constructed from eight
root relations. No model map, faithfulness, or extra Cartan match is an input. -/
def comparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F) :=
  e.trans (d.markedIso (MarkedLocal.parabolic_core_selfCentralizing Q e h))

@[simp] theorem comparison_left_apply (a : parabolic L S 0) :
    ((comparison Q e h split d).left a : Sp F) =
      d.equiv ((e.left a : Q.tits.standardParabolic {Q.simple 0}) : X ⧸ Q.D) := rfl

@[simp] theorem comparison_middle_apply (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison Q e h split d).middle b : Sp F) = d.equiv (e.middle b : X ⧸ Q.D) := rfl

@[simp] theorem comparison_right_apply (a : parabolic L S 1) :
    ((comparison Q e h split d).right a : Sp F) =
      d.equiv ((e.right a : Q.tits.standardParabolic {Q.simple 1}) : X ⧸ Q.D) := rfl

/-- Left inclusion square on the entire original overlap. -/
theorem comparison_left_square (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    (comparison Q e h split d).left ⟨b,b.property.1⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).left
        ((comparison Q e h split d).middle b) := (comparison Q e h split d).left_commutes b

/-- Right inclusion square, using the same common-Borel map. -/
theorem comparison_right_square (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    (comparison Q e h split d).right ⟨b,b.property.2⟩ =
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).right
        ((comparison Q e h split d).middle b) := (comparison Q e h split d).right_commutes b

theorem comparison_commonBorel_apply (b : commonBorel L S) :
    ((comparison Q e h split d).middle
      ((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm) b) : Sp F) =
      d.equiv (MarkedLocal.borelMap Q e h b) := rfl

theorem source_sylow_image :
    (MarkedLocal.sylowMap Q e h).range.map d.equiv.toMonoidHom = unipotent (F := F) := by
  rw [MarkedLocal.sylow_range Q e h split]
  exact d.map_unipotent

section GeneratedSource
variable (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
  (d₀ : C2Presentation.RootData (F := F) Q₀ split₀)

/-- Application to the actual generated-source quotient, retaining its map. -/
def originalComparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F) :=
  comparison Q₀ (originalMarkedIso Q₀) h split₀ d₀

@[simp] theorem originalComparison_left_apply (a : parabolic L S 0) :
    ((originalComparison h Q₀ split₀ d₀).left a : Sp F) =
      d₀.equiv (Q₀.q ⟨a,parabolic_le_generated 0 a.property⟩) := by
  rw [originalComparison,comparison_left_apply,originalMarkedIso_left_apply]

@[simp] theorem originalComparison_middle_apply (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((originalComparison h Q₀ split₀ d₀).middle b : Sp F) =
      d₀.equiv (Q₀.q ⟨b,parabolic_le_generated 0 b.property.1⟩) := by
  rw [originalComparison,comparison_middle_apply,originalMarkedIso_middle_apply]

@[simp] theorem originalComparison_right_apply (a : parabolic L S 1) :
    ((originalComparison h Q₀ split₀ d₀).right a : Sp F) =
      d₀.equiv (Q₀.q ⟨a,parabolic_le_generated 1 a.property⟩) := by
  rw [originalComparison,comparison_right_apply,originalMarkedIso_right_apply]
end GeneratedSource
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticFourPresentation
