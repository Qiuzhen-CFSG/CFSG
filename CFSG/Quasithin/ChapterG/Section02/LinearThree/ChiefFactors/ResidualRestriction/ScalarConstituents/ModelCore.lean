module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Irreducibility.Actions
public import Theory.SpecificGroups.PSL3.PointRadicalGeneration.ParabolicCore

/-!
# The full parabolic core as a scalar-twisted constituent

The literal block kernel maps to the geometric standard-point radical.
The full-parabolic core and minimality theorems therefore identify it with
O₂(P) and prove minimality among arbitrary invariant subgroups. In additive
coordinates its conjugation action is det(B)⁻¹ B⁻ᵀ. This is irreducible
among all binary submodules; on the concrete SL₂ section an alternating
form identifies it with the natural module. Surjective covers retain
irreducibility and noncentrality.

The source-core quotient and terminal quotient applications are assembled
in `ScalarConstituents.SourceCore` using the original local projection.
Source: Aschbacher–Smith, G.2.5(1),(8), printed pp.335–336.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
open Matrix.PSL3.LinearThree
open Irreducibility
variable (F : Type*) [Field F] [Finite F]

omit [Finite F] in
/-- The flag line is the geometric standard point used by the core theorem. -/
theorem naturalLine_eq_standardPoint : naturalLine F =
    Matrix.PSL3.PointRadicalGeneration.standardPoint (F := F) := by
  ext v
  rw [mem_naturalLine, Matrix.PSL3.PointRadicalGeneration.mem_standardPoint]

/-- The block kernel and the geometric transvection radical have the same literal matrices. -/
theorem block_kernel_map_eq_geometric_radical : ((block F).ker).map (pointParabolicSL F).subtype =
    Matrix.PSL3.PointRadicalGeneration.radical (Matrix.PSL3.PointRadicalGeneration.standardPoint (F := F)) := by
  rw [← radical_range, Matrix.PSL3.PointRadicalGeneration.radical_standardPoint]
  ext x
  rw [Subgroup.mem_map, Matrix.PSL3.RootPlaneGeometry.mem_rootPlaneSL_point]
  constructor
  · rintro ⟨_, ⟨w,rfl⟩,rfl⟩
    exact ⟨w.toAdd 0,w.toAdd 1,rfl⟩
  · rintro ⟨u,v,rfl⟩
    exact ⟨radicalHom F (Multiplicative.ofAdd ![u,v]), ⟨_,rfl⟩,rfl⟩

/-- The full setwise point-parabolic two-core is exactly the GL₂ block kernel. -/
theorem block_kernel_eq_twoCore [CharP F 2] :
    (block F).ker = pCore 2 (pointParabolicSL F) := by
  apply Subgroup.map_injective (pointParabolicSL F).subtype_injective
  rw [block_kernel_map_eq_geometric_radical]
  change _ = (pointParabolicSL F).pCoreIn 2
  rw [← Matrix.PSL3.PointRadicalGeneration.parabolic_standardPoint,
    Matrix.PSL3.PointRadicalGeneration.parabolic_twoCore_eq _
      (by rw [← naturalLine_eq_standardPoint]; exact naturalLine_dimension F)]

/-- Every nontrivial normal subgroup in the block kernel is the whole kernel. -/
theorem block_kernel_minimal (A : Subgroup (pointParabolicSL F))
    (hA : A ≤ (block F).ker) (hA0 : A ≠ ⊥) [A.Normal] : A = (block F).ker := by
  apply Subgroup.map_injective (pointParabolicSL F).subtype_injective
  rw [block_kernel_map_eq_geometric_radical]
  apply Matrix.PSL3.PointRadicalGeneration.radical_minimal _
    (by rw [← naturalLine_eq_standardPoint]; exact naturalLine_dimension F)
  · rw [← block_kernel_map_eq_geometric_radical]
    exact Subgroup.map_mono hA
  · exact (Subgroup.map_eq_bot_iff_of_injective _ (pointParabolicSL F).subtype_injective).not.mpr hA0
  · have hn := A.le_normalizer_map (pointParabolicSL F).subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hn
    simpa only [Matrix.PSL3.PointRadicalGeneration.parabolic_standardPoint] using hn

/-- Conjugation on row-unipotent coordinates, including the determinant-inverse twist. -/
def radicalAction (x : pointParabolicSL F) (w : Fin 2 → F) : Fin 2 → F :=
  (scalar F x : F) • dualBlockAction F x w

/-- Restriction to the actual SL₂ section removes precisely the scalar twist. -/
theorem radicalAction_restrict_SL (x : SL(2,F)) (w : Fin 2 → F) :
    radicalAction F (specialLinearSection F x) w = x⁻¹.val.transpose *ᵥ w := by
  change (scalar F (blockLift F (SpecialLinearGroup.toGL x)) : F) •
    dualBlockAction F (blockLift F (SpecialLinearGroup.toGL x)) w = _
  rw [scalar_restrict_SL]
  simp only [Units.val_one, one_smul]
  rw [dualBlockAction, map_inv, block_lift, ← map_inv]
  rfl

/-- The alternating form identifies the SL₂ restriction with its natural module. -/
theorem radicalAction_alternating (x : SL(2,F)) (w : Fin 2 → F) :
    alternatingEquiv F (radicalAction F (specialLinearSection F x) w) =
      x.val *ᵥ alternatingEquiv F w := by
  rw [radicalAction_restrict_SL, alternating_intertwines]

/-- The SL₂ section already acts transitively on nonzero radical vectors. -/
theorem radicalAction_transitive (v w : Fin 2 → F) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ x, radicalAction F x v = w := by
  obtain ⟨x,hx⟩ := Matrix.SL2.exists_mulVec_eq F v w hv hw
  refine ⟨specialLinearSection F x.transpose⁻¹, ?_⟩
  simpa only [radicalAction_restrict_SL, inv_inv, SpecialLinearGroup.coe_transpose,
    transpose_transpose] using hx

variable {A : Type*} [Group A] (p : A →* pointParabolicSL F)
/-- Geometric minimality gives irreducibility among all additive subgroups,
including those which are not F-linear. The actor may be any surjective cover. -/
theorem radicalAction_irreducible (hp : Function.Surjective p) :
    AdditivelyIrreducible (fun x => radicalAction F (p x)) := by
  intro K hK
  let B := K.toSubgroup.map (radicalHom F)
  have hB : B ≤ (block F).ker := by
    rw [← radical_range]
    exact Subgroup.map_le_range _ _
  let : B.Normal := ⟨by
    rintro _ ⟨v,hv,rfl⟩ x
    obtain ⟨y,rfl⟩ := hp x
    change p y * radicalHom F (Multiplicative.ofAdd v.toAdd) * (p y)⁻¹ ∈ B
    rw [radical_conjugation]
    exact ⟨Multiplicative.ofAdd (radicalAction F (p y) v.toAdd), hK y v.toAdd hv,rfl⟩⟩
  by_cases hB0 : B = ⊥
  · left
    have hK0 : K.toSubgroup = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (radicalHom_injective F)).mp hB0
    exact AddSubgroup.toSubgroup.injective (hK0.trans AddSubgroup.toSubgroup.map_bot.symm)
  · right
    have hb := block_kernel_minimal F B hB hB0
    rw [← radical_range, MonoidHom.range_eq_map] at hb
    have hKtop := Subgroup.map_injective (radicalHom_injective F) hb
    exact AddSubgroup.toSubgroup.injective (hKtop.trans AddSubgroup.toSubgroup.map_top.symm)

/-- The radical constituent is noncentral, including over the binary field. -/
theorem radicalAction_noncentral (hp : Function.Surjective p) :
    Noncentral (fun x => radicalAction F (p x)) := by
  have h0 : (![1,0] : Fin 2 → F) ≠ 0 := by
    intro he; have := congrFun he 0; simp at this
  have h1 : (![0,1] : Fin 2 → F) ≠ 0 := by
    intro he; have := congrFun he 1; simp at this
  obtain ⟨x,hx⟩ := radicalAction_transitive F _ _ h0 h1
  obtain ⟨y,rfl⟩ := hp x
  refine ⟨y, ![1,0], ?_⟩
  change radicalAction F (p y) ![1,0] ≠ ![1,0]
  rw [hx]
  intro he
  have := congrFun he 0
  simp at this
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
