module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointResidual
public import Theory.GroupTheory.Amalgam.LocalStructure
public import Theory.Frattini.OmegaProducts

/-!
# The complete first local factor of the unitary-four model

For q = 2^n, n ≥ 1, the first local factor is the faithful projective image of
matrices fixing the first isotropic vector. We assemble the middle-block
quotient, special radical, and residual calculations for this same subgroup.
The radical is identified with the actual two-core before transporting its
coordinates, center, derived subgroup, and Frattini subgroup. Its quotient is
PSL₂ over the actual quadratic-Frobenius fixed field, whose order is q.

`source_I_6_point` supplies the first-factor clauses of Aschbacher--Smith
F.1.12(I)(6), using the complete meaning of q^(1+4) from F.1.11.
`source_II_point` applies the residual and core results to any ambient Sylow
two-subgroup lying in this point parabolic; `source_II_point_two` supplies the
separate solvable binary case. The full two-parabolic amalgam, its chosen
Sylow configuration, second factor, and outer extension belong to the
unitary-four amalgam assembly, rather than to these first-factor assertions.

Source: `refs/quasithin.pdf`, printed pp. 262--264 (PDF pp. 273--275).
-/

open Theory.SpecificGroups.ClassicalUnitary Theory.GroupTheory
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal
variable (n : ℕ) (hn : 1 ≤ n)

/-- The entire matrix radical maps isomorphically onto the projective two-core. -/
def radicalEquivProjectiveTwoCore : Radical n hn ≃* pCore 2 (ProjectiveLocal n hn) :=
  ((localEquiv n hn).subgroupMap (Radical n hn)).trans
    (MulEquiv.subgroupCongr (projectiveLocal_twoCore n hn).symm)

/-- The core equivalence is the restriction of the original projective map. -/
@[simp] theorem radicalEquivProjectiveTwoCore_apply (a : Radical n hn) :
    (radicalEquivProjectiveTwoCore n hn a).val = localEquiv n hn a.val := rfl

/-- Hermitian Heisenberg coordinates for the actual projective two-core. -/
def projectiveTwoCoreCoordinatesEquiv :
    UnitaryFourPointLocal.RadicalCoordinates (MatrixField n) (fieldConj n) ≃
      pCore 2 (ProjectiveLocal n hn) :=
  (UnitaryFourPointLocal.radicalCoordinatesEquiv (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn)).trans (radicalEquivProjectiveTwoCore n hn).toEquiv

/-- Coordinates retain the literal matrix-to-projective embedding. -/
@[simp] theorem projectiveTwoCoreCoordinatesEquiv_apply
    (c : UnitaryFourPointLocal.RadicalCoordinates (MatrixField n) (fieldConj n)) :
    (projectiveTwoCoreCoordinatesEquiv n hn c).val.val = projection n hn
      (UnitaryFourPointLocal.radicalElement (MatrixField n) (fieldConj n)
        (fieldConj_involutive n hn) c) := rfl

/-- The center of the actual two-core is the additive fixed field. -/
def projectiveTwoCoreCenterEquiv :
    Subgroup.center (pCore 2 (ProjectiveLocal n hn)) ≃* Multiplicative (FixedField n) :=
  (Subgroup.centerCongr (radicalEquivProjectiveTwoCore n hn).symm).trans
    (UnitaryFourPointLocal.centerEquivFixedField (MatrixField n) (fieldConj n)
      (fieldConj_involutive n hn) (fieldConj_nontrivial n hn))

/-- The matrix two-core has the special structure and orders required in F.1.11. -/
theorem twoCore_special :
    IsPGroup 2 (pCore 2 (MatrixLocal n hn)) ∧
    Subgroup.center (pCore 2 (MatrixLocal n hn)) = commutator (pCore 2 (MatrixLocal n hn)) ∧
    Subgroup.center (pCore 2 (MatrixLocal n hn)) = frattini (pCore 2 (MatrixLocal n hn)) ∧
    Nat.card (pCore 2 (MatrixLocal n hn)) = (2 ^ n) ^ 5 ∧
    Nat.card (Subgroup.center (pCore 2 (MatrixLocal n hn))) = 2 ^ n := by
  rw [← radical_eq_twoCore n hn]
  exact radical_special n hn

/-- The projective two-core has center equal to its derived subgroup. -/
theorem projectiveTwoCore_center_eq_commutator :
    Subgroup.center (pCore 2 (ProjectiveLocal n hn)) =
      commutator (pCore 2 (ProjectiveLocal n hn)) := by
  let e := (radicalEquivProjectiveTwoCore n hn).symm
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.center_map_equiv, map_commutator_eq,
    MonoidHom.range_eq_top.mpr e.surjective, ← commutator_def]
  exact radical_center_eq_commutator n hn

/-- The projective two-core has center equal to its Frattini subgroup. -/
theorem projectiveTwoCore_center_eq_frattini :
    Subgroup.center (pCore 2 (ProjectiveLocal n hn)) =
      frattini (pCore 2 (ProjectiveLocal n hn)) := by
  let e := (radicalEquivProjectiveTwoCore n hn).symm
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.center_map_equiv, Subgroup.frattini_map_equiv]
  exact radical_center_eq_frattini n hn

/-- The first projective two-core has order q^5. -/
theorem projectiveTwoCore_card :
    Nat.card (pCore 2 (ProjectiveLocal n hn)) = (2 ^ n) ^ 5 :=
  (Nat.card_congr (radicalEquivProjectiveTwoCore n hn).symm.toEquiv).trans
    (radical_card n hn)

/-- Its center has order q, not the matrix-field order q². -/
theorem projectiveTwoCore_center_card :
    Nat.card (Subgroup.center (pCore 2 (ProjectiveLocal n hn))) = 2 ^ n :=
  (Nat.card_congr ((projectiveTwoCoreCenterEquiv n hn).toEquiv.trans
    Multiplicative.toAdd)).trans (fixedField_card n hn)

/-- The center is elementary abelian, through its additive fixed-field realization. -/
theorem projectiveTwoCore_center_elementary :
    IsElementaryAbelian 2 (Subgroup.center (pCore 2 (ProjectiveLocal n hn))) := by
  refine { exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro z
  apply (projectiveTwoCoreCenterEquiv n hn).injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  simp [pow_two, CharTwo.add_self_eq_zero]

/-- The first two-core is nonabelian, including at q = 2. -/
theorem projectiveTwoCore_commutator_ne_bot :
    commutator (pCore 2 (ProjectiveLocal n hn)) ≠ ⊥ := by
  intro h
  have hc := projectiveTwoCore_center_card n hn
  rw [projectiveTwoCore_center_eq_commutator, h, Subgroup.card_bot] at hc
  have hq : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by decide)
  omega

/-- All special-group assertions in the source notation q^(1+4). -/
theorem projectiveTwoCore_special :
    let Q := pCore 2 (ProjectiveLocal n hn)
    IsPGroup 2 Q ∧ commutator Q ≠ ⊥ ∧
    commutator Q = Subgroup.center Q ∧ frattini Q = Subgroup.center Q ∧
    IsElementaryAbelian 2 (Subgroup.center Q) ∧
    Nat.card Q = (2 ^ n) ^ 5 ∧ Nat.card (Subgroup.center Q) = 2 ^ n :=
  ⟨pCore_isPGroup, projectiveTwoCore_commutator_ne_bot n hn,
    (projectiveTwoCore_center_eq_commutator n hn).symm,
    (projectiveTwoCore_center_eq_frattini n hn).symm,
    projectiveTwoCore_center_elementary n hn, projectiveTwoCore_card n hn,
    projectiveTwoCore_center_card n hn⟩

/-- The quotient by the actual projective two-core is PSL₂ over the fixed field. -/
def projectiveQuotientByTwoCoreEquivPSL :
    (ProjectiveLocal n hn ⧸ pCore 2 (ProjectiveLocal n hn)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (FixedField n) :=
  (LocalCoreTransport.quotientEquiv 2 (localEquiv n hn).symm).trans
    (quotientByTwoCoreEquivPSL n hn)

/-- The quotient isomorphism commutes with the given faithful local projection. -/
@[simp] theorem projectiveQuotientByTwoCoreEquivPSL_mk_localEquiv (a : MatrixLocal n hn) :
    projectiveQuotientByTwoCoreEquivPSL n hn (QuotientGroup.mk (localEquiv n hn a)) =
      quotientByTwoCoreEquivPSL n hn (QuotientGroup.mk a) := by
  simp [projectiveQuotientByTwoCoreEquivPSL]

/-- The first-factor conclusions of F.1.12(I)(6), without radical or quotient premises. -/
theorem source_I_6_point :
    ProjectiveLocal n hn ≤ pointParabolic n hn ∧
    ((ProjectiveLocal n hn).subgroupOf (pointParabolic n hn)).Normal ∧
    Nat.card (FixedField n) = 2 ^ n ∧
    Nonempty ((ProjectiveLocal n hn ⧸ pCore 2 (ProjectiveLocal n hn)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (FixedField n)) ∧
    (let Q := pCore 2 (ProjectiveLocal n hn)
     IsPGroup 2 Q ∧ commutator Q ≠ ⊥ ∧
     commutator Q = Subgroup.center Q ∧ frattini Q = Subgroup.center Q ∧
     IsElementaryAbelian 2 (Subgroup.center Q) ∧
     Nat.card Q = (2 ^ n) ^ 5 ∧ Nat.card (Subgroup.center Q) = 2 ^ n) :=
  ⟨projectiveLocal_le_pointParabolic n hn, projectiveLocal_normal n hn,
    fixedField_card n hn, ⟨projectiveQuotientByTwoCoreEquivPSL n hn⟩,
    projectiveTwoCore_special n hn⟩

/-- The first-factor application of F.1.12(II)(i), including the literal embedded core.
The ambient Sylow and its placement are supplied by the amalgam assembly. -/
theorem source_II_point (hn2 : 1 < n) (S : Sylow 2 (ProjectiveGroup n hn))
    (hSP : (S : Subgroup (ProjectiveGroup n hn)) ≤ pointParabolic n hn) :
    Subgroup.solvableResidual (ProjectiveLocal n hn) = ⊤ ∧
    (S : Subgroup (ProjectiveGroup n hn)) ≤ ProjectiveLocal n hn ∧
    (pCore 2 (ProjectiveLocal n hn ⊔ (S : Subgroup (ProjectiveGroup n hn)) :
        Subgroup (ProjectiveGroup n hn))).map
        (ProjectiveLocal n hn ⊔ (S : Subgroup (ProjectiveGroup n hn))).subtype =
      (pCore 2 (ProjectiveLocal n hn)).map (ProjectiveLocal n hn).subtype := by
  refine ⟨projectiveLocal_solvableResidual_eq_top n hn hn2,
    twoSubgroup_le_projectiveLocal n hn S S.isPGroup' hSP, ?_⟩
  rw [projectiveLocal_sup_twoSubgroup n hn S S.isPGroup' hSP]

/-- The q = 2 exception in F.1.12(II): the actual first factor is solvable. -/
theorem source_II_point_two :
    Group.IsSolvable (ProjectiveLocal 1 (by decide)) ∧
    Subgroup.solvableResidual (ProjectiveLocal 1 (by decide)) = ⊥ ∧
    Nat.card (pCore 2 (ProjectiveLocal 1 (by decide))) = 32 ∧
    Nat.card (Subgroup.center (pCore 2 (ProjectiveLocal 1 (by decide)))) = 2 := by
  exact ⟨projectiveLocal_isSolvable_two, projectiveLocal_solvableResidual_two,
    projectiveTwoCore_card 1 (by decide), projectiveTwoCore_center_card 1 (by decide)⟩

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal
