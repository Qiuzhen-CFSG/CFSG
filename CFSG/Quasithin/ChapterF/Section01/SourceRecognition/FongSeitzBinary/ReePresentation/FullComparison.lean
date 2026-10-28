module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition
public import Theory.GroupTheory.Amalgam.Reversal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReePresentation.SignedComparison
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.ReeFour

/-!
# Full original and geometric Ree amalgam comparison from finite equations

The constructed ambient equivalence restricts to the entire Borel and both
oriented parabolics. Composing with the supplied marking retains the same
original or universal/geometric quotient maps and both endpoint squares.
Every m is allowed, and m = 0 uses the full Ree group. Source field/root/Cartan
construction and verification of the displayed equations remain independent
source obligations, as do the binary type alternatives.
Source: DGS Groups and Graphs, Theorem D, p.224; Aschbacher--Smith F.1.1--3;
GLS3 2.3.5--8 and Steinberg section 11.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReePresentation

/-- The source orientation chooses which literal endpoint is linear. -/
def sideAt (o : Bool) : Fin 2 → ReeF4.LargeLocalSeeds.Side :=
  if o then ![.suzuki,.linear] else ![.linear,.suzuki]

def orientedAmalgam (m : ℕ) (o : Bool) :=
  RankTwoAmalgam.ofSubgroups (ReeF4.Parabolics.parabolic m (sideAt o 0)) (ReeF4.Parabolics.borel m)
    (ReeF4.Parabolics.parabolic m (sideAt o 1))
    (ReeF4.Parabolics.borel_le_parabolic m _) (ReeF4.Parabolics.borel_le_parabolic m _)

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) {m : ℕ} (d : SourcePositive.Charts Q split m)
  (T : SourceBorel.TorusData Q split d) (W : SourceNormalizer.WeylData Q split d T)
  (E : SourceAngular.Equations Q split d) (R : SourceSigned.Equations Q split d T W)
  (A : ReeF4.RootPresentationRecognition.Global.SourceGauss Q split d T W)

abbrev quotientEquiv := ReeF4.RootPresentationRecognition.Global.comparison Q split d T W E R A

theorem subgroup_images :
    split.U.map (quotientEquiv Q split d T W E R A).toMonoidHom = ReeF4.Parabolics.unipotent m ∧
    Q.tits.B.map (quotientEquiv Q split d T W E R A).toMonoidHom = ReeF4.Parabolics.borel m ∧
    ∀ i : Fin 2, (Q.tits.standardParabolic {Q.simple i}).map
      (quotientEquiv Q split d T W E R A).toMonoidHom = ReeF4.Parabolics.parabolic m (sideAt d.orientation i) := by
  refine ⟨Global.comparison_unipotent Q split d T W E R A,Global.comparison_borel Q split d T W E R A,?_⟩
  intro i
  cases ho : d.orientation <;> fin_cases i
  · simpa [quotientEquiv,ho,SourceNormalizer.index,sideAt,NormalizerPresentation.side] using Global.comparison_parabolic Q split d T W E R A false
  · simpa [quotientEquiv,ho,SourceNormalizer.index,sideAt,NormalizerPresentation.side] using Global.comparison_parabolic Q split d T W E R A true
  · simpa [quotientEquiv,ho,SourceNormalizer.index,sideAt,NormalizerPresentation.side] using Global.comparison_parabolic Q split d T W E R A true
  · simpa [quotientEquiv,ho,SourceNormalizer.index,sideAt,NormalizerPresentation.side] using Global.comparison_parabolic Q split d T W E R A false

private theorem standard_left_apply (b : Q.tits.B) :
    (Q.standardAmalgam.left b : X ⧸ Q.D) = b := by
  obtain ⟨x,rfl⟩ := Q.markedIso.middle.surjective b
  rw [← Q.markedIso.left_commutes, Q.markedIso_left_apply, Q.markedIso_middle_apply]
  rfl

private theorem standard_right_apply (b : Q.tits.B) :
    (Q.standardAmalgam.right b : X ⧸ Q.D) = b := by
  obtain ⟨x,rfl⟩ := Q.markedIso.middle.surjective b
  rw [← Q.markedIso.right_commutes, Q.markedIso_right_apply, Q.markedIso_middle_apply]
  rfl

/-- Restrict the same full quotient equivalence on all three marked subgroups. -/
def markedIso : RankTwoAmalgam.Iso Q.standardAmalgam (orientedAmalgam m d.orientation) where
  left := ((Q.tits.standardParabolic {Q.simple 0}).equivMapOfInjective
    (quotientEquiv Q split d T W E R A).toMonoidHom (quotientEquiv Q split d T W E R A).injective).trans
      (MulEquiv.subgroupCongr ((subgroup_images Q split d T W E R A).2.2 0))
  middle := (Q.tits.B.equivMapOfInjective
    (quotientEquiv Q split d T W E R A).toMonoidHom (quotientEquiv Q split d T W E R A).injective).trans
      (MulEquiv.subgroupCongr (subgroup_images Q split d T W E R A).2.1)
  right := ((Q.tits.standardParabolic {Q.simple 1}).equivMapOfInjective
    (quotientEquiv Q split d T W E R A).toMonoidHom (quotientEquiv Q split d T W E R A).injective).trans
      (MulEquiv.subgroupCongr ((subgroup_images Q split d T W E R A).2.2 1))
  left_commutes b := by
    apply Subtype.ext
    exact congrArg (quotientEquiv Q split d T W E R A) (standard_left_apply Q b)
  right_commutes b := by
    apply Subtype.ext
    exact congrArg (quotientEquiv Q split d T W E R A) (standard_right_apply Q b)

/-- The original or geometric inclusion amalgam, with its entire overlap. -/
def comparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (orientedAmalgam m d.orientation) := e.trans (markedIso Q split d T W E R A)

@[simp] theorem comparison_left_apply (a : parabolic L S 0) :
    ((comparison Q e split d T W E R A).left a : ReeF4.Model m) =
      quotientEquiv Q split d T W E R A (e.left a : X ⧸ Q.D) := rfl
@[simp] theorem comparison_middle_apply (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison Q e split d T W E R A).middle b : ReeF4.Model m) =
      quotientEquiv Q split d T W E R A (e.middle b : X ⧸ Q.D) := rfl
@[simp] theorem comparison_right_apply (a : parabolic L S 1) :
    ((comparison Q e split d T W E R A).right a : ReeF4.Model m) =
      quotientEquiv Q split d T W E R A (e.right a : X ⧸ Q.D) := rfl

theorem comparison_left_square (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    (comparison Q e split d T W E R A).left ⟨b,b.property.1⟩ =
      (orientedAmalgam m d.orientation).left ((comparison Q e split d T W E R A).middle b) :=
  (comparison Q e split d T W E R A).left_commutes b

theorem comparison_right_square (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    (comparison Q e split d T W E R A).right ⟨b,b.property.2⟩ =
      (orientedAmalgam m d.orientation).right ((comparison Q e split d T W E R A).middle b) :=
  (comparison Q e split d T W E R A).right_commutes b

theorem comparison_commonBorel_apply (h : HypothesisF11 L S) (b : commonBorel L S) :
    ((comparison Q e split d T W E R A).middle
      ((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm) b) : ReeF4.Model m) =
        quotientEquiv Q split d T W E R A (MarkedLocal.borelMap Q e h b) := rfl

include Q e split d T W E R A in
/-- Either actual orientation supplies the existing concrete Ree amalgam. -/
theorem concrete_comparison :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (GreenBook.LieModels.ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (GreenBook.LieModels.ReeFour.amalgam m).reverse) := by
  let α := RankTwoAmalgam.ofSubgroups (parabolic L S 0)
    (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right
  have finish : ∀ o : Bool, Nonempty (RankTwoAmalgam.Iso α (orientedAmalgam m o)) →
      Nonempty (RankTwoAmalgam.Iso α (GreenBook.LieModels.ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso α (GreenBook.LieModels.ReeFour.amalgam m).reverse) := by
    intro o ⟨f⟩
    cases o
    · exact Or.inr ⟨f⟩
    · exact Or.inl ⟨f⟩
  exact finish d.orientation ⟨comparison Q e split d T W E R A⟩

section Original
variable (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
  {m₀ : ℕ} (d₀ : SourcePositive.Charts Q₀ split₀ m₀)
  (T₀ : SourceBorel.TorusData Q₀ split₀ d₀) (W₀ : SourceNormalizer.WeylData Q₀ split₀ d₀ T₀)
  (E₀ : SourceAngular.Equations Q₀ split₀ d₀) (R₀ : SourceSigned.Equations Q₀ split₀ d₀ T₀ W₀)
  (A₀ : Global.SourceGauss Q₀ split₀ d₀ T₀ W₀)

def originalComparison := comparison Q₀ (originalMarkedIso Q₀) split₀ d₀ T₀ W₀ E₀ R₀ A₀

@[simp] theorem originalComparison_left_apply (a : parabolic L S 0) :
    ((originalComparison Q₀ split₀ d₀ T₀ W₀ E₀ R₀ A₀).left a : ReeF4.Model m₀) =
      quotientEquiv Q₀ split₀ d₀ T₀ W₀ E₀ R₀ A₀ (Q₀.q ⟨a,parabolic_le_generated 0 a.property⟩) := by
  rw [originalComparison,comparison_left_apply,originalMarkedIso_left_apply]
@[simp] theorem originalComparison_middle_apply (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((originalComparison Q₀ split₀ d₀ T₀ W₀ E₀ R₀ A₀).middle b : ReeF4.Model m₀) =
      quotientEquiv Q₀ split₀ d₀ T₀ W₀ E₀ R₀ A₀ (Q₀.q ⟨b,parabolic_le_generated 0 b.property.1⟩) := by
  rw [originalComparison,comparison_middle_apply,originalMarkedIso_middle_apply]
@[simp] theorem originalComparison_right_apply (a : parabolic L S 1) :
    ((originalComparison Q₀ split₀ d₀ T₀ W₀ E₀ R₀ A₀).right a : ReeF4.Model m₀) =
      quotientEquiv Q₀ split₀ d₀ T₀ W₀ E₀ R₀ A₀ (Q₀.q ⟨a,parabolic_le_generated 1 a.property⟩) := by
  rw [originalComparison,comparison_right_apply,originalMarkedIso_right_apply]
end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReePresentation
