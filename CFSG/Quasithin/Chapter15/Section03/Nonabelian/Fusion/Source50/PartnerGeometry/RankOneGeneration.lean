module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.RankOneImage
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The actual rank-one pair contains the selected residual

The two point stabilizers generate the full matrix image of Y₁U. Their
join is normalized by the original two-core, so the remaining quotient is
a two-group. The two-perfectness of Y₁ removes that quotient.
Source: Aschbacher–Smith 15.3.56(3), printed p.1147.
-/
@[expose] public noncomputable section
open Subgroup ClassicalOrthogonal.FourPlusMatrix
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : CFSG.Quasithin.ChapterG.Section02.Setup G}
  {g : G} (d : Hypothesis D g)

theorem residual_isPPerfect : IsPPerfect 2 (leftResidual d) :=
  isPPerfect_embedded_pResidual 2 _

theorem selected_pair_le_residual_join (y : D.I g) (hy : (y : G) ∈ leftResidual d) :
    D.I (y : G) ≤ leftResidual d ⊔ D.U := by
  apply sup_le le_sup_right
  rintro _ ⟨u, hu, rfl⟩
  exact (leftResidual d ⊔ D.U).mul_mem
    ((leftResidual d ⊔ D.U).mul_mem (mem_sup_left ((leftResidual d).inv_mem hy))
      (mem_sup_right hu)) (mem_sup_left ((leftResidual d).inv_mem ((leftResidual d).inv_mem hy)))

include d in
theorem original_core_normalizes_selected_pair (y : D.I g) :
    D.S g ≤ normalizer (D.I (y : G) : Set G) := by
  rw [d.S_eq_star_kernel]
  refine inf_le_right.trans ?_
  apply (le_inf (d.base.binary_core_le_T.trans d.base.binary_T_normalizes_U)
    (BaseHypothesis.binary_core_normalizes_conjugate d.base (d.I_le_LT y.property))).trans
  exact normalizer_inf_normalizer_le_normalizer_sup D.U (conjugate D.U (y : G))

theorem selected_pair_eq_residual_join (y : D.I g) (hy : (y : G) ∈ leftResidual d)
    (hyc : matrixSection d y = MatrixOrbit.leftCubic) :
    D.I (y : G) = leftResidual d ⊔ D.U := by
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  let K := leftResidual d ⊔ D.U
  have hK : K ≤ D.I g := sup_le (leftResidual_le_I d) le_sup_left
  have hJK : D.I (y : G) ≤ K := selected_pair_le_residual_join d y hy
  let q := (matrixSection d).comp (inclusion hK)
  let J := (D.I (y : G)).subgroupOf K
  have hqQ : q.ker.map K.subtype ≤ D.S g := by
    rintro x ⟨k,hk,rfl⟩
    refine ⟨inclusion hK k, ?_, rfl⟩
    rw [← matrixSection_ker d]
    exact hk
  have hQN : q.ker ≤ normalizer (J : Set K) := by
    apply (le_normalizer_comap K.subtype).trans'
    intro x hx
    exact original_core_normalizes_selected_pair d y (hqQ (mem_map_of_mem _ hx))
  have hmap : J.map q = matrixImage d (D.I (y : G)) := by
    ext a
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨inclusion hK u,hu,rfl⟩
    · rintro ⟨u,hu,rfl⟩
      exact ⟨⟨u,hJK hu⟩,hu,rfl⟩
  have hrange : q.range = matrixImage d K := by
    ext a
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨inclusion hK u,u.property,rfl⟩
    · rintro ⟨u,hu,rfl⟩
      exact ⟨⟨u,hu⟩,rfl⟩
  have himage : J.map q = q.range := by
    rw [hmap,hrange,selected_pair_image d z hz y hyc,residual_join_image d z hz y hy hyc]
  have hcover : J ⊔ q.ker = ⊤ := by
    have hc := congrArg (fun A => A.comap q) himage
    simpa only [comap_map_eq,MonoidHom.comap_range_self] using hc
  have hJn : J.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hcover]
    exact sup_le J.le_normalizer hQN
  let := hJn
  have hker : IsPGroup 2 q.ker := by
    have he : q.ker = (matrixSection d).ker.comap (inclusion hK) := rfl
    rw [he,matrixSection_ker d]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hp : IsPGroup 2 (K ⧸ J) := isPGroup_quotient_of_sup_eq_top J q.ker hker hcover
  let f : leftResidual d →* K ⧸ J := (QuotientGroup.mk' J).comp (inclusion le_sup_left)
  have hf : f = 1 := (residual_isPPerfect d).hom_eq_one_of_isPGroup hp f
  have hYJ : leftResidual d ≤ D.I (y : G) := by
    intro l hl
    apply (QuotientGroup.eq_one_iff (N := J)
      (inclusion (show leftResidual d ≤ K from le_sup_left) ⟨l,hl⟩)).mp
    exact DFunLike.congr_fun hf ⟨l,hl⟩
  exact le_antisymm hJK (sup_le hYJ le_sup_left)

theorem selected_y_mem_pair (y : D.I g) (hy : (y : G) ∈ leftResidual d)
    (hyc : matrixSection d y = MatrixOrbit.leftCubic) : (y : G) ∈ D.I (y : G) := by
  rw [selected_pair_eq_residual_join d y hy hyc]
  exact mem_sup_left hy

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
