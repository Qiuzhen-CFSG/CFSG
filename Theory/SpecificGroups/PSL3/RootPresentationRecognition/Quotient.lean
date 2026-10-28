module
public import Theory.SpecificGroups.PSL3.RootPresentationRecognition.Markings
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.Irreducibility

/-!
# Root-marked recognition of a finite split rank-two quotient

Six literal root maps satisfying the elementary relations determine an
ambient PSL₃ equivalence. Positive generation and normalizers identify the
whole Borel; maximality and the negative simple roots identify both vertices.
The point index records either orientation. All three amalgam maps restrict
this same ambient equivalence, so both inclusion squares commute.

Source: Steinberg §6, pp.71–74; DGS, Groups and Graphs, Theorem D, p.224.
The construction of the six compatible source root maps is a separate input.
-/

@[expose] public noncomputable section
open scoped MatrixGroups
open Theory.SpecificGroups.LinearHigher
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.GroupTheory Subgroup Matrix.PSL3.LinearThree
namespace Matrix.PSL3.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] {P : Fin 2 → Subgroup X}

/-- The source premises, retaining all roots, parameters and actual subgroup markings.
`pointIndex = 0` is the usual orientation and `pointIndex = 1` the reverse. -/
structure RootData (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (F : Type*) [Field F] (pointIndex : Fin 2) where
  x : Root 3 → F → X ⧸ Q.D
  relations : Relations x
  generate : closure {g | ∃ r a, g = x r a} = ⊤
  positive : positiveClosure x = split.U
  negative_point : x (root (2 : Fin 3) 1 (by decide)) 1 ∈
    Q.tits.standardParabolic {Q.simple pointIndex}
  negative_line : x (root (1 : Fin 3) 0 (by decide)) 1 ∈
    Q.tits.standardParabolic {Q.simple (1 - pointIndex)}

/-- A proper marked parabolic ensures that the quotient is nontrivial. -/
theorem quotient_nontrivial (Q : MarkedQuotient P) : Nontrivial (X ⧸ Q.D) := by
  by_contra hn
  let := not_nontrivial_iff_subsingleton.mp hn
  exact (Q.parabolic_isCoatom 0).ne_top (Subsingleton.elim _ _)

variable (Q : MarkedQuotient P)

theorem standard_left_apply (b : Q.tits.B) :
    (Q.standardAmalgam.left b : X ⧸ Q.D) = b := by
  obtain ⟨x, rfl⟩ := Q.markedIso.middle.surjective b
  rw [← Q.markedIso.left_commutes]
  rw [Q.markedIso_left_apply, Q.markedIso_middle_apply]
  rfl

theorem standard_right_apply (b : Q.tits.B) :
    (Q.standardAmalgam.right b : X ⧸ Q.D) = b := by
  obtain ⟨x, rfl⟩ := Q.markedIso.middle.surjective b
  rw [← Q.markedIso.right_commutes]
  rw [Q.markedIso_right_apply, Q.markedIso_middle_apply]
  rfl

/-- The two marked singleton parabolics generate the whole quotient. -/
theorem marked_parabolics_generate :
    Q.tits.standardParabolic {Q.simple 0} ⊔
      Q.tits.standardParabolic {Q.simple 1} = ⊤ := by
  apply top_unique
  rw [← Q.tits.standardParabolic_S]
  apply Q.tits.standardParabolic_le
  · exact (Q.tits.B_le_standardParabolic {Q.simple 0}).trans le_sup_left
  · intro s hs
    obtain ⟨i, rfl⟩ := Q.simple_range ▸ hs
    have hi : Q.tits.standardParabolic {Q.simple i} ≤
        Q.tits.standardParabolic {Q.simple 0} ⊔ Q.tits.standardParabolic {Q.simple 1} := by
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    exact (Q.tits.bruhatCell_subset_standardParabolic_of_mem (by simp)).trans hi

/-- The quotient itself faithfully completes its marked standard amalgam. -/
def standardCompletion : RankTwoAmalgam.FaithfulCompletion Q.standardAmalgam
    (G := X ⧸ Q.D) where
  left := (Q.tits.standardParabolic {Q.simple 0}).subtype
  right := (Q.tits.standardParabolic {Q.simple 1}).subtype
  compatible := by
    ext b
    exact (standard_left_apply Q b).trans (standard_right_apply Q b).symm
  left_injective := Subtype.val_injective
  right_injective := Subtype.val_injective
  middle_injective := by
    intro a b hab
    apply Subtype.ext
    exact (standard_left_apply Q a).symm.trans (hab.trans (standard_left_apply Q b))
  generated := by
    rw [range_subtype, range_subtype]
    exact marked_parabolics_generate Q

/-- Its entire marked middle image is the actual Borel. -/
theorem standardCompletion_middle_range : (standardCompletion Q).middle.range = Q.tits.B := by
  have he : (standardCompletion Q).middle = Q.tits.B.subtype := by
    ext b
    exact standard_left_apply Q b
  rw [he, range_subtype]

variable [Finite F] (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {pointIndex : Fin 2} (d : RootData Q split F pointIndex)
  (hcore : Q.tits.B.normalCore = ⊥)

/-- The equivalence is constructed from the root relations, with no recognition
or simplicity hypothesis on the unknown quotient. -/
def rootEquiv : (X ⧸ Q.D) ≃* PSL(3,F) := by
  letI := quotient_nontrivial Q
  exact equiv d.relations d.generate (split.center_eq_bot_of_borel_core hcore)

@[simp] theorem rootEquiv_root (r : Root 3) (a : F) :
    rootEquiv Q split d hcore (d.x r a) = projectiveRoot r a := by
  let := quotient_nontrivial Q
  exact equiv_root d.relations d.generate _ r a

/-- The actual specified unipotent group is preserved. -/
theorem rootEquiv_unipotent : split.U.map (rootEquiv Q split d hcore).toMonoidHom =
    unipotent F := by
  rw [← d.positive]
  exact map_positiveClosure _ (rootEquiv_root Q split d hcore)

variable [CharP F 2]

/-- Normalizers recover the whole Borel, including its odd torus. -/
theorem rootEquiv_borel : Q.tits.B.map (rootEquiv Q split d hcore).toMonoidHom =
    borel F :=
  map_borel _ (rootEquiv_root Q split d hcore) _ _ d.positive split.normalizer_eq

/-- The marked point vertex, in either orientation. -/
theorem rootEquiv_point :
    (Q.tits.standardParabolic {Q.simple pointIndex}).map
      (rootEquiv Q split d hcore).toMonoidHom = pointParabolic F :=
  map_pointParabolic _ (rootEquiv_root Q split d hcore) _ _
    (rootEquiv_borel Q split d hcore) (Q.tits.B_le_standardParabolic _)
    (Q.parabolic_isCoatom _) d.negative_point

/-- The marked line vertex, in the opposite orientation. -/
theorem rootEquiv_line :
    (Q.tits.standardParabolic {Q.simple (1 - pointIndex)}).map
      (rootEquiv Q split d hcore).toMonoidHom = lineParabolic F :=
  map_lineParabolic _ (rootEquiv_root Q split d hcore) _ _
    (rootEquiv_borel Q split d hcore) (Q.tits.B_le_standardParabolic _)
    (Q.parabolic_isCoatom _) d.negative_line

omit [Finite F] [CharP F 2] in
/-- The endpoint subgroup with the chosen orientation. -/
def flagVertex (F : Type*) [Field F] (pointIndex i : Fin 2) : Subgroup PSL(3,F) :=
  if i = pointIndex then pointParabolic F else lineParabolic F

omit [Finite F] [CharP F 2] in
/-- The whole model Borel lies in both oriented vertices. -/
theorem borel_le_flagVertex (F : Type*) [Field F] (pointIndex i : Fin 2) :
    borel F ≤ flagVertex F pointIndex i := by
  unfold flagVertex
  split
  · exact map_mono inf_le_left
  · exact map_mono inf_le_right

omit [Finite F] [CharP F 2] in
/-- The actual flag inclusion amalgam, with either ordering of its vertices. -/
def flagAmalgam (F : Type*) [Field F] (pointIndex : Fin 2) :
    RankTwoAmalgam (flagVertex F pointIndex 0) (borel F) (flagVertex F pointIndex 1) :=
  RankTwoAmalgam.ofSubgroups _ _ _ (borel_le_flagVertex F pointIndex 0)
    (borel_le_flagVertex F pointIndex 1)

/-- All endpoint images use the same orientation and ambient map. -/
theorem rootEquiv_vertex (i : Fin 2) :
    (Q.tits.standardParabolic {Q.simple i}).map
      (rootEquiv Q split d hcore).toMonoidHom = flagVertex F pointIndex i := by
  by_cases h : i = pointIndex
  · subst i
    simpa [flagVertex] using rootEquiv_point Q split d hcore
  · have hi : i = 1 - pointIndex := by
      fin_cases i <;> fin_cases pointIndex <;> simp_all
    rw [flagVertex, if_neg h, hi]
    exact rootEquiv_line Q split d hcore

/-- Restrict an ambient equivalence to an exactly identified subgroup. -/
def restrictEquiv {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z)
    (A : Subgroup Y) (C : Subgroup Z) (h : A.map e.toMonoidHom = C) : A ≃* C :=
  (A.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr h)

@[simp] theorem restrictEquiv_apply {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z)
    (A : Subgroup Y) (C : Subgroup Z) (h : A.map e.toMonoidHom = C) (a : A) :
    (restrictEquiv e A C h a : Z) = e a := rfl

/-- One ambient equivalence on the two endpoints and whole Borel, including
both commuting squares. -/
def markedIso : RankTwoAmalgam.Iso Q.standardAmalgam (flagAmalgam F pointIndex) where
  left := restrictEquiv (rootEquiv Q split d hcore) _ _ (rootEquiv_vertex Q split d hcore 0)
  middle := restrictEquiv (rootEquiv Q split d hcore) _ _ (rootEquiv_borel Q split d hcore)
  right := restrictEquiv (rootEquiv Q split d hcore) _ _ (rootEquiv_vertex Q split d hcore 1)
  left_commutes b := by
    apply Subtype.ext
    exact congrArg (rootEquiv Q split d hcore) (standard_left_apply Q b)
  right_commutes b := by
    apply Subtype.ext
    exact congrArg (rootEquiv Q split d hcore) (standard_right_apply Q b)

@[simp] theorem markedIso_left_apply (a : Q.tits.standardParabolic {Q.simple 0}) :
    ((markedIso Q split d hcore).left a : PSL(3,F)) = rootEquiv Q split d hcore a := rfl

@[simp] theorem markedIso_middle_apply (b : Q.tits.B) :
    ((markedIso Q split d hcore).middle b : PSL(3,F)) = rootEquiv Q split d hcore b := rfl

@[simp] theorem markedIso_right_apply (a : Q.tits.standardParabolic {Q.simple 1}) :
    ((markedIso Q split d hcore).right a : PSL(3,F)) = rootEquiv Q split d hcore a := rfl

/-- Compose with the literal original quotient marking, for either orientation. -/
def quotientMarkedIso : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
    (flagAmalgam F pointIndex) := Q.markedIso.trans (markedIso Q split d hcore)

@[simp] theorem quotientMarkedIso_left_apply (a : P 0) :
    ((quotientMarkedIso Q split d hcore).left a : PSL(3,F)) =
      rootEquiv Q split d hcore (Q.q a) := by
  change rootEquiv Q split d hcore (Q.markedIso.left a : X ⧸ Q.D) = _
  rw [Q.markedIso_left_apply]

@[simp] theorem quotientMarkedIso_middle_apply (b : (P 0 ⊓ P 1 : Subgroup X)) :
    ((quotientMarkedIso Q split d hcore).middle b : PSL(3,F)) =
      rootEquiv Q split d hcore (Q.q b) := by
  change rootEquiv Q split d hcore (Q.markedIso.middle b : X ⧸ Q.D) = _
  rw [Q.markedIso_middle_apply]

@[simp] theorem quotientMarkedIso_right_apply (a : P 1) :
    ((quotientMarkedIso Q split d hcore).right a : PSL(3,F)) =
      rootEquiv Q split d hcore (Q.q a) := by
  change rootEquiv Q split d hcore (Q.markedIso.right a : X ⧸ Q.D) = _
  rw [Q.markedIso_right_apply]

end Matrix.PSL3.RootPresentationRecognition
