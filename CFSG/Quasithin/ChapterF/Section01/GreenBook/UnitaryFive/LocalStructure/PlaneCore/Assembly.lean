module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.PlaneCore.Levi
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Residual

/-!
# The residual and canonical two-core of the U₅(4) plane parabolic

The geometric radical--SL₂ subgroup is perfect, while the determinant quotient
of the full plane parabolic is abelian. These facts identify the subgroup
with the solvable residual. Its projection to SL₂ has kernel exactly the
plane-unipotent subgroup; the trivial two-core of SL₂ identifies the canonical
two-core, and the parameter count gives its order. All equivalences use the
actual matrix embeddings and quotient maps of the marked model.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.12(7), printed pp.263--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model

open Matrix Theory.SpecificGroups.UnitaryFive

variable (M : Model 4)

/-- The concrete radical--SL₂ subgroup is the right solvable residual. -/
theorem rightLocal_eq_rightRadicalLevi : M.rightLocal = M.rightRadicalLevi :=
  PlaneCore.plane_solvableResidual_eq M.form M.local_field_card M.conjugation
    M.rightLeviTrace M.rightLeviTrace_spec M.matrix

/-- Every constructed unipotent matrix lies in the actual residual. -/
theorem rightUnipotent_le_rightLocal : M.rightUnipotent ≤ M.rightLocal := by
  rw [M.rightLocal_eq_rightRadicalLevi, M.rightRadicalLevi_eq]
  exact le_sup_left

/-- The concrete semidirect product is the residual, through its geometric
multiplication map. -/
noncomputable def rightLocalEquiv : PlaneCore.PlaneSemidirect M.form ≃* M.rightLocal :=
  M.rightRadicalLeviEquiv.trans (MulEquiv.subgroupCongr M.rightLocal_eq_rightRadicalLevi.symm)

@[simp] theorem rightLocalEquiv_val (p : PlaneCore.PlaneSemidirect M.form) :
    (M.rightLocalEquiv p).val =
      PlaneCore.Parameters.toParabolic M.matrix p.left * M.rightSLLevi p.right := rfl

/-- The canonical two-core of the generated radical is its relative
plane-unipotent subgroup. -/
theorem rightRadicalLevi_pCore_eq :
    pCore 2 M.rightRadicalLevi = M.rightUnipotent.subgroupOf M.rightRadicalLevi :=
  PlaneCore.planeRadicalLevi_twoCore_eq M.form M.rightLeviTrace M.rightLeviTrace_spec M.matrix

/-- The canonical two-core of the residual is precisely the constructed
plane-unipotent subgroup with its natural relative embedding. -/
theorem rightLocal_pCore_eq :
    pCore 2 M.rightLocal = M.rightUnipotent.subgroupOf M.rightLocal := by
  rw [M.rightLocal_eq_rightRadicalLevi]
  exact M.rightRadicalLevi_pCore_eq

/-- In the full plane parabolic, the residual's core is the constructed image. -/
theorem rightLocal_pCore_map :
    (pCore 2 M.rightLocal).map M.rightLocal.subtype = M.rightUnipotent := by
  rw [M.rightLocal_pCore_eq, Subgroup.map_subgroupOf_eq_of_le M.rightUnipotent_le_rightLocal]

/-- The canonical core is identified with the actual matrix parameter group. -/
noncomputable def rightLocalTwoCoreEquiv :
    pCore 2 M.rightLocal ≃* M.RightUnipotentParameters :=
  ((MulEquiv.subgroupCongr M.rightLocal_pCore_eq).trans
    (Subgroup.subgroupOfEquivOfLe M.rightUnipotent_le_rightLocal)).trans
      M.rightUnipotentEquiv.symm

/-- The plane-unipotent subgroup has the source order `2^16`. -/
theorem rightUnipotent_card : Nat.card M.rightUnipotent = 2 ^ 16 :=
  PlaneCore.projectiveUnipotent_card_four M.form M.local_field_card M.conjugation M.matrix

/-- The order concerns the canonical two-core of the actual residual. -/
theorem rightLocal_pCore_card : Nat.card (pCore 2 M.rightLocal) = 2 ^ 16 := by
  rw [M.rightLocal_pCore_eq,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe M.rightUnipotent_le_rightLocal).toEquiv]
  exact M.rightUnipotent_card

/-- The residual has the three cosets given by the determinant quotient. -/
theorem rightLocal_index : M.rightLocal.index = 3 := by
  rw [M.rightLocal_eq_rightRadicalLevi]
  exact M.rightRadicalLevi_index

/-- The special-linear projection on the actual residual. -/
noncomputable def rightLocalProjection :
    M.rightLocal →* SpecialLinearGroup (Fin 2) M.F :=
  M.rightRadicalLeviProjection.comp
    (MulEquiv.subgroupCongr M.rightLocal_eq_rightRadicalLevi).toMonoidHom

theorem rightLocalProjection_surjective : Function.Surjective M.rightLocalProjection :=
  M.rightRadicalLeviProjection_surjective.comp
    (MulEquiv.subgroupCongr M.rightLocal_eq_rightRadicalLevi).surjective

/-- In geometric coordinates, the projection forgets exactly the parameter factor. -/
@[simp] theorem rightLocalProjection_equiv (p : PlaneCore.PlaneSemidirect M.form) :
    M.rightLocalProjection (M.rightLocalEquiv p) = p.right := by
  change M.rightRadicalLeviProjection (M.rightRadicalLeviEquiv p) = p.right
  exact PlaneCore.planeRadicalLeviProjection_equiv M.form M.rightLeviTrace
    M.rightLeviTrace_spec M.matrix p

/-- The actual residual projection kills precisely its canonical two-core. -/
theorem rightLocalProjection_ker : M.rightLocalProjection.ker = pCore 2 M.rightLocal := by
  rw [M.rightLocal_pCore_eq]
  ext g
  change M.rightRadicalLeviProjection
    ((MulEquiv.subgroupCongr M.rightLocal_eq_rightRadicalLevi) g) = 1 ↔
      g.val ∈ M.rightUnipotent
  exact Iff.of_eq (congrArg
    (fun H : Subgroup M.rightRadicalLevi =>
      (MulEquiv.subgroupCongr M.rightLocal_eq_rightRadicalLevi) g ∈ H)
    M.rightRadicalLeviProjection_ker)

/-- The residual quotient is the actual PSL₂ matrix group over the same F₁₆. -/
noncomputable def rightLocalQuotientEquiv :
    (M.rightLocal ⧸ pCore 2 M.rightLocal) ≃* M.LocalLinearGroup :=
  ((QuotientGroup.quotientMulEquivOfEq M.rightLocalProjection_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective M.rightLocalProjection
      M.rightLocalProjection_surjective)).trans PlaneCore.ResidualAction.slEquivPSL

/-- The quotient equivalence uses the canonical SL₂-to-PSL₂ quotient. -/
@[simp] theorem rightLocalQuotientEquiv_mk (g : M.rightLocal) :
    M.rightLocalQuotientEquiv (QuotientGroup.mk g) =
      QuotientGroup.mk (M.rightLocalProjection g) := rfl

/-- On an actual product of unipotent and SL₂ matrices, the quotient keeps
exactly the SL₂ factor. -/
@[simp] theorem rightLocalQuotientEquiv_equiv (p : PlaneCore.PlaneSemidirect M.form) :
    M.rightLocalQuotientEquiv (QuotientGroup.mk (M.rightLocalEquiv p)) =
      QuotientGroup.mk p.right := by
  rw [M.rightLocalQuotientEquiv_mk, M.rightLocalProjection_equiv]

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
