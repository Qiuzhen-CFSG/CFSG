module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.InitialReduction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SylowGeneratedReduction
public import Theory.GroupTheory.Fitting.Equiv
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.EndpointIndices

/-!
# The source minimal-configuration reduction on the same marked quotient

The original rank-one Sylows normally generate the finite quotient.
Characteristic two at the actual marked parabolics kills the Borel core,
hence the ambient center, and gives F(B) = O₂(B) = U. It also excludes the
reducible rank-two diagram. These prove the initial hypotheses used in
Fong–Seitz I §§2–3, with saturation already supplied by SplitData. No
replacement of the quotient by its perfect residual is made or needed.

The Fitting equality transports through the full original Borel marking,
so the source's replacement of U by F(B) leaves the original Sylow image
unchanged. InitialReduction constructs the literal G₀/Z equivalence and
both original endpoint squares. The reduced Borel is proved to be the full
intersection, and the original-carrier specialization retains Q.q on all
three groups, rather than choosing unrelated endpoint isomorphisms.

Source: Fong–Seitz I, Theorem A, (1A)–(1D), opening §2 (p.7) and §3
(p.12), Invent. Math. 21 (1973), pp.1–57; DGS, Groups and Graphs,
minimal-configuration caveat on pp.80–81 and invocation on p.224.
The genuine quotient, splitness and original amalgam marking remain inputs
of qt-dgs85-apartment-exchange. This completes the initial reduction at
that boundary, not exhaustive profile selection or the seven marked Lie
comparisons. Binary and nonperfect endpoints require no extra hypothesis.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h split

/-- The original full Borel's Fitting subgroup is its specified Sylow, through the actual middle marking. -/
theorem original_borel_fitting_eq_sylow :
    fittingSubgroup (commonBorel L S) = S.subgroupOf (commonBorel L S) := by
  let b : commonBorel L S ≃* Q.tits.B :=
    (MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm).trans e.middle
  apply map_injective (f := b.toMonoidHom) b.injective
  apply map_injective Q.tits.B.subtype_injective
  rw [map_fitting_equiv, borel_fitting_eq_unipotent_of_source Q e h split,
    map_subgroupOf_eq_of_le split.U_le]
  rw [← sylow_range Q e h split, sylowMap, MonoidHom.range_comp, inclusion_range, map_map]
  rfl

/-- Replacing U by F(B) leaves its original marked image unchanged. -/
theorem original_borel_fitting_image :
    (fittingSubgroup (commonBorel L S)).map (borelMap Q e h) = split.U := by
  rw [original_borel_fitting_eq_sylow Q e h split, ← sylow_range Q e h split,
    sylowMap, MonoidHom.range_comp, inclusion_range]

/-- The initial assumptions of Fong–Seitz I §§2–3 hold on this SAME saturated split quotient. -/
theorem source_minimal_configuration :
    split.unipotentClosure = ⊤ ∧
      Q.tits.B.normalCore = ⊥ ∧ center (X ⧸ Q.D) = ⊥ ∧
      fittingSubgroup Q.tits.B = pCore 2 Q.tits.B ∧
      pCore 2 Q.tits.B = split.U.subgroupOf Q.tits.B ∧
      ¬ Commute (Q.simple 0) (Q.simple 1) := by
  have hc := parabolic_core_selfCentralizing Q e h
  have hcore : Q.tits.B.normalCore = ⊥ := by
    apply eq_bot_iff.mpr
    calc
      Q.tits.B.normalCore ≤ (Q.tits.standardParabolic {Q.simple 0}).normalCore :=
        normal_le_normalCore.mpr
          (Q.tits.B.normalCore_le.trans (Q.tits.B_le_standardParabolic _))
      _ = ⊥ := Q.parabolic_normalCore_eq_bot split 0 (hc 0)
  exact ⟨unipotentClosure_eq_top_of_source Q e h split, hcore,
    split.center_eq_bot_of_borel_core hcore,
    (borel_fitting_eq_unipotent_of_source Q e h split).trans split.borel_twoCore.symm,
    split.borel_twoCore, Q.simple_not_commute split hc⟩

/-- The actual source hypotheses discharge both premises of the canonical G₀/Z equivalence. -/
@[expose] def sourceInitialEquiv : split.InitialQuotient ≃* (X ⧸ Q.D) :=
  split.initialEquiv (source_minimal_configuration Q e h split).1
    (source_minimal_configuration Q e h split).2.1

/-- Both standard parabolics and the full Borel after the literal source reduction. -/
@[expose] def sourceInitialAmalgam :=
  split.initialAmalgam (Q.tits.standardParabolic {Q.simple 0}) Q.tits.B
    (Q.tits.standardParabolic {Q.simple 1}) (Q.tits.B_le_standardParabolic _)
    (Q.tits.B_le_standardParabolic _)

private def standardInclusionIso : RankTwoAmalgam.Iso Q.standardAmalgam
    (RankTwoAmalgam.ofSubgroups (Q.tits.standardParabolic {Q.simple 0}) Q.tits.B
      (Q.tits.standardParabolic {Q.simple 1}) (Q.tits.B_le_standardParabolic _)
      (Q.tits.B_le_standardParabolic _)) where
  left := MulEquiv.refl _
  middle := MulEquiv.refl _
  right := MulEquiv.refl _
  left_commutes b := by
    apply Subtype.ext
    change (Q.standardAmalgam.left b : X ⧸ Q.D) = b
    rw [RootCoordinates.standardAmalgam_left_eq_inclusion]
    rfl
  right_commutes b := by
    apply Subtype.ext
    change (Q.standardAmalgam.right b : X ⧸ Q.D) = b
    rw [RootCoordinates.standardAmalgam_right_eq_inclusion]
    rfl

/-- The full original amalgam survives the initial Fong–Seitz reduction, including both endpoint squares. -/
def sourceInitialMarkedIso : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (sourceInitialAmalgam Q split) :=
  e.trans ((standardInclusionIso Q).trans
    (split.initialAmalgamIso (source_minimal_configuration Q e h split).1
      (source_minimal_configuration Q e h split).2.1 _ _ _
      (Q.tits.B_le_standardParabolic _) (Q.tits.B_le_standardParabolic _)))

/-- The left endpoint keeps its prescribed marking. -/
theorem sourceInitialMarkedIso_left_apply (x : parabolic L S 0) :
    sourceInitialEquiv Q e h split ((sourceInitialMarkedIso Q e h split).left x) =
      endpointMap Q e 0 x := by
  exact (sourceInitialEquiv Q e h split).apply_symm_apply _

/-- The entire original overlap keeps its prescribed marking. -/
theorem sourceInitialMarkedIso_middle_apply
    (x : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    sourceInitialEquiv Q e h split ((sourceInitialMarkedIso Q e h split).middle x) =
      (e.middle x : X ⧸ Q.D) := by
  exact (sourceInitialEquiv Q e h split).apply_symm_apply _

/-- The right endpoint keeps its prescribed marking. -/
theorem sourceInitialMarkedIso_right_apply (x : parabolic L S 1) :
    sourceInitialEquiv Q e h split ((sourceInitialMarkedIso Q e h split).right x) =
      endpointMap Q e 1 x := by
  exact (sourceInitialEquiv Q e h split).apply_symm_apply _

/-- The reduced full Borel is exactly the intersection of both reduced parabolics. -/
theorem source_initial_intersection :
    split.initialSubgroup (Q.tits.standardParabolic {Q.simple 0}) ⊓
      split.initialSubgroup (Q.tits.standardParabolic {Q.simple 1}) =
        split.initialSubgroup Q.tits.B := by
  apply map_injective (f := (sourceInitialEquiv Q e h split).toMonoidHom)
    (sourceInitialEquiv Q e h split).injective
  rw [map_inf _ _ _ (sourceInitialEquiv Q e h split).injective]
  change (split.initialSubgroup _).map (split.initialEquiv _ _).toMonoidHom ⊓
    (split.initialSubgroup _).map (split.initialEquiv _ _).toMonoidHom =
      (split.initialSubgroup _).map (split.initialEquiv _ _).toMonoidHom
  rw [split.initialEquiv_subgroup, split.initialEquiv_subgroup,
    split.initialEquiv_subgroup, Q.standard_intersection]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)

/-- In a quotient of the original generated carrier, all three reduced maps are the SAME Q.q on representatives. -/
theorem original_initial_reduction_maps :
    let η := MarkedLocal.sourceInitialEquiv Q (originalMarkedIso Q) h split
    let a := MarkedLocal.sourceInitialMarkedIso Q (originalMarkedIso Q) h split
    (∀ x : parabolic L S 0, η (a.left x) =
      Q.q ⟨x, parabolic_le_generated 0 x.property⟩) ∧
    (∀ x : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G), η (a.middle x) =
      Q.q ⟨x, parabolic_le_generated 0 x.property.1⟩) ∧
    (∀ x : parabolic L S 1, η (a.right x) =
      Q.q ⟨x, parabolic_le_generated 1 x.property⟩) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact (MarkedLocal.sourceInitialMarkedIso_left_apply Q (originalMarkedIso Q) h split x).trans
      (originalMarkedIso_left_apply Q x)
  · intro x
    exact (MarkedLocal.sourceInitialMarkedIso_middle_apply Q (originalMarkedIso Q) h split x).trans
      (originalMarkedIso_middle_apply Q x)
  · intro x
    exact (MarkedLocal.sourceInitialMarkedIso_right_apply Q (originalMarkedIso Q) h split x).trans
      (originalMarkedIso_right_apply Q x)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
