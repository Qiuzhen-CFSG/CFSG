module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Star.LinearImage
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Star.PointNormalizer

/-!
# Matrix inputs for the higher-field root calculation

The actual starred U-image, transported through the specified SL₂ model,
is nontrivial, fixes the marked field line pointwise, and is normalized by
the full setwise line stabilizer. The original marked conjugator lies outside
that stabilizer. Thus the remaining Sylow and generation step is precisely
the geometry of a line root group in SL₂, with all source inputs discharged.

Containment of U* in L* also identifies the source product L*U* with its
actual SL₂ model and bounds I* above by L*. These conclusions use only the
earlier G.2.2 containment and Frattini premises.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.3(1–2), printed p.333, PDF p.344.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Hypothesis
open Setup
variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {F : Type*} [Field F] [Finite F] {n : ℕ} {g : G}
  (d : Hypothesis D F n g)
include d

/-- U* transported through the literal marked SL₂-model. -/
def matrixU : Subgroup SL(2,F) :=
  ((D.star D.U).subgroupOf (D.star D.L)).map d.model.toMonoidHom

theorem matrixU_ne_bot (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : d.matrixU ≠ ⊥ := by
  intro he
  apply d.star_U_ne_bot
  apply bot_unique
  intro u hu
  let q : D.star D.L := ⟨u, d.star_U_le_star_L hUT hf hu⟩
  have hm : d.model q ∈ d.matrixU := ⟨q, hu, rfl⟩
  rw [he, mem_bot] at hm
  have hq := d.model.injective (hm.trans d.model.map_one.symm)
  exact congrArg Subtype.val hq

theorem matrixU_le_fixingSubgroup :
    d.matrixU ≤ fixingSubgroup SL(2,F) (d.point : Set (Fin 2 → F)) := by
  rintro x ⟨q, hq, rfl⟩
  apply (mem_fixingSubgroup_iff SL(2,F)).mpr
  intro v hv
  change (d.model q).val *ᵥ v = v
  have he := congrArg Multiplicative.toAdd
    (d.coordinateAction_U_fixes_point ⟨q, hq⟩ v hv)
  rw [d.coordinateAction_on_L q] at he
  exact he

/-- Normalization descends under precisely the source quotient map. -/
theorem pointNormalizer_star_normalizes_U :
    D.star (D.L ⊓ D.G₁) ≤ normalizer (D.star D.U : Set D.Star) := by
  rintro _ ⟨x, hx, rfl⟩
  apply mem_normalizer_fintype
  rintro _ ⟨y, hy, rfl⟩
  have hn := d.pointNormalizer_normalizes_U hx
  have hc : ((x * y * x⁻¹ : D.LT) : G) ∈ D.U :=
    (mem_normalizer_iff.mp hn y).mp hy
  refine ⟨x * y * x⁻¹, hc, ?_⟩
  simp only [map_mul, map_inv]

/-- The full setwise line stabilizer normalizes the actual matrix U-image. -/
theorem matrixU_normalized :
    MulAction.stabilizer SL(2,F) (d.point : Set (Fin 2 → F)) ≤
      normalizer (d.matrixU : Set SL(2,F)) := by
  rw [← d.pointNormalizer_model]
  have hn : (D.star (D.L ⊓ D.G₁)).subgroupOf (D.star D.L) ≤
      normalizer ((D.star D.U).subgroupOf (D.star D.L) : Set (D.star D.L)) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp (d.pointNormalizer_star_normalizes_U hx) y
  exact (map_mono (f := d.model.toMonoidHom) hn).trans
    (le_normalizer_map d.model.toMonoidHom)

/-- The original marked conjugator has a matrix outside the full line Borel. -/
theorem marked_matrix_not_stabilizing :
    d.model (starProjection D ⟨g, d.g_mem⟩) ∉
      MulAction.stabilizer SL(2,F) (d.point : Set (Fin 2 → F)) :=
  fun he => d.g_not_normalizing ((d.model_mem_pointStabilizer_iff ⟨g, d.g_mem⟩).mp he)

/-- The source marked product has no extra field-automorphism factor. -/
theorem star_join_eq (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.star (D.L ⊔ D.U) = D.star D.L := by
  rw [binary_star_sup _ _ le_sup_left (hUT.trans le_sup_right)]
  exact sup_eq_left.mpr (d.star_U_le_star_L hUT hf)

/-- The actual L*U* is the marked copy of SL₂(F). -/
noncomputable def starJoinEquiv (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    (D.star D.L ⊔ D.star D.U : Subgroup D.Star) ≃* SL(2,F) :=
  (MulEquiv.subgroupCongr (sup_eq_left.mpr (d.star_U_le_star_L hUT hf))).trans d.model

theorem starJoin_product (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    (D.star D.L : Set D.Star) * (D.star D.U : Set D.Star) = D.star D.L := by
  rw [← coe_mul_of_right_le_normalizer_left _ _
    ((d.star_U_le_star_L hUT hf).trans (D.star D.L).le_normalizer),
    sup_eq_left.mpr (d.star_U_le_star_L hUT hf)]

theorem star_I_le_star_L (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : D.star (D.I g) ≤ D.star D.L := by
  rw [← d.star_join_eq hUT hf]
  exact binary_star_mono (binary_I_le_join d.g_mem)

end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Hypothesis
