module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EdgeStar
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# The star's core displacement is residual-fixed

The first star comparison makes [[Z-star-alpha,L-alpha],Q-alpha] trivial.
Consequently the commutator of the holomorph star with Q-alpha is normalized
by the residual; characteristic star generation normalizes it by the edge
supplement as well. It is centralized by the critical endpoint. The actual
critical conjugate-generation theorem and the two-group supplement therefore
make the residual centralize this commutator. Normal generation transfers
the result to the entire alpha star.

All normality is relative to the finite vertex stabilizer. The application
uses the replacement's actual quotient and retains the full fixed core.
This proves the intermediate [Z-star-alpha,Q-alpha] <= D-alpha in MS93
(3.4), printed p.869. The dual-module inclusion Z-star-beta <= U-alpha D-alpha
and Section 5 exclusion are still separate obligations.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

private theorem commutator_normalized_of_triple
    {G : Type*} [Group G] (B A Q L : Subgroup G) [Q.Normal]
    (hBA : B ≤ A) (htriple : ⁅⁅A,L⁆,Q⁆ = ⊥) :
    L ≤ normalizer ((⁅B,Q⁆ : Subgroup G) : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro l hl _ ⟨a, ha, y, hy, rfl⟩
  have hy' : l * y * l⁻¹ ∈ Q := (inferInstance : Q.Normal).conj_mem y hy l
  have hc : ⁅l,a⁆ ∈ ⁅A,L⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hl (hBA ha)
  have hcy : Commute ⁅l,a⁆ (l * y * l⁻¹) :=
    (commutator_eq_bot_iff_le_centralizer.mp htriple hc _ hy').symm
  have hck : Commute ⁅l,a⁆ ⁅a,l * y * l⁻¹⁆ :=
    (commutator_eq_bot_iff_le_centralizer.mp htriple hc _
      (commutator_le_right B Q (commutator_mem_commutator ha hy'))).symm
  rw [conjugate_commutatorElement, show l * a * l⁻¹ = ⁅l,a⁆ * a by
    simp [commutatorElement_def, mul_assoc]]
  rw [commutatorElement_mul_left_eq_conj_mul, hcy.commutator_eq,
    hck.eq, mul_inv_cancel_right, mul_one]
  exact commutator_mem_commutator ha hy'

private theorem seed_core_displacement
    {G : Type*} [Group G] [Finite G]
    (A B Q T J : Subgroup G) [Q.Normal]
    (hBA : B ≤ A) (hAc : A ≤ normalClosure (B : Set G))
    (hQT : Q ≤ T) (hT : IsPGroup 2 T)
    (hgen : pResidual 2 G ⊔ T = ⊤)
    (hBn : T ≤ normalizer (B : Set G))
    (htriple : ⁅⁅A,pResidual 2 G⁆,Q⁆ = ⊥)
    (hBJ : B ≤ centralizer (J : Set G))
    (hJgen : normalClosure (J : Set G) ⊔ T = ⊤) :
    ⁅A,Q⁆ ≤ Q ⊓ centralizer (pResidual 2 G : Set G) := by
  let N := ⁅B,Q⁆
  have hNL : pResidual 2 G ≤ normalizer (N : Set G) :=
    commutator_normalized_of_triple B A Q _ hBA htriple
  have hNT : T ≤ normalizer (N : Set G) := by
    intro t ht
    change t ∈ normalizer ((⁅B,Q⁆ : Subgroup G) : Set G)
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hBn ht),
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (H := Q) (mem_top t))]
  let : N.Normal := normalizer_eq_top_iff.mp (top_unique (hgen ▸ sup_le hNL hNT))
  have hNB : N ≤ B := le_normalizer_iff_commutator_le_left.mp (hQT.trans hBn)
  let C := centralizer (N : Set G)
  have hJC : J ≤ C := le_centralizer_iff.mp (hNB.trans hBJ)
  have hCT : C ⊔ T = ⊤ := top_unique (hJgen ▸
    sup_le_sup_right (normalClosure_le_normal hJC) T)
  have hLC : pResidual 2 G ≤ C := sInf_le
    ⟨inferInstance, isPGroup_quotient_of_sup_eq_top C T hT hCT⟩
  have hND : N ≤ Q ⊓ centralizer (pResidual 2 G : Set G) :=
    le_inf (commutator_le_right _ _) (le_centralizer_iff.mp hLC)
  apply (commutator_mono hAc le_rfl).trans
  rw [commutator_comm]
  exact commutator_normalClosure_le_of_normal Q B _ (by rwa [commutator_comm])

private theorem subgroupOf_commutator {G : Type*} [Group G]
    (S A B : Subgroup G) (hA : A ≤ S) (hB : B ≤ S) :
    ⁅A.subgroupOf S,B.subgroupOf S⁆ = (⁅A,B⁆).subgroupOf S := by
  apply map_injective S.subtype_injective
  rw [map_commutator,map_subgroupOf_eq_of_le hA,map_subgroupOf_eq_of_le hB,
    map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup _ _).trans (sup_le hA hB))]

private theorem conjugatesIn_le_mapped_normalClosure {G : Type*} [Group G]
    (S J : Subgroup G) (hJ : J ≤ S) :
    conjugatesIn J S ≤ (normalClosure (J.subgroupOf S : Set S)).map S.subtype := by
  apply iSup_le
  intro g
  rintro _ ⟨j,hj,rfl⟩
  exact mem_map_of_mem S.subtype
    ((inferInstance : (normalClosure (J.subgroupOf S : Set S)).Normal).conj_mem
      ⟨j,hJ hj⟩ (le_normalClosure hj) g⁻¹)

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full source star has core displacement in the literal residual-fixed
core. This is the intermediate assertion on printed p.869, before the second
star inclusion and before outer removal. -/
theorem Input.replacement_sourceStarAlpha_core_displacement
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    {z : Vertex d.radical} (path : CriticalPath d.radical geometry (alpha d.radical) z)
    (hfirst : path.walk.getVert 1 = beta d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical))) :
    ⁅sourceStarAlpha d.radical Y,Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical) := by
  let S := stabilizer d.radical (alpha d.radical)
  let A := sourceStarAlpha d.radical Y
  let B := (starSpan d.radical Y).map (embedS d.radical)
  let Q₀ := Q d.radical (alpha d.radical)
  let T := Q d.radical (beta d.radical)
  let J := Z d.radical z
  have hAS : A ≤ S := sourceStarAlpha_le_stabilizer _ _
  have hBA : B ≤ A := by
    have hh := (sourceStarAlpha_le_iff d.radical Y A).mp le_rfl (1 : Mbar d.radical)
    have he : (MulAut.conj (1 : FreeAmalgam d.radical)).toMonoidHom =
        MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change 1 * x * 1⁻¹ = x
      simp
    simpa only [OneMemClass.coe_one,he,Subgroup.map_id] using hh
  have hBS := hBA.trans hAS
  have hQS : Q₀ ≤ S := fun _ hx => hx.1
  have hTS : T ≤ S := fun _ hx => hx.2 _ (adjacent_symm _ (base_adjacent _))
  have hQT : Q₀ ≤ T := Q_le_adjacent_h d.radical rfl (base_adjacent _)
  have hJS : J ≤ S := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant _ rfl,
      geometry.distance_constant _ path.end_color]
  have hgen₀ : pResidual 2 d.overgroup ⊔ d.radical = ⊤ := by
    rw [h.replacement_residual d]
    apply top_unique
    intro x _
    obtain ⟨k,hk,r,hr,rfl⟩ := h.replacement_product d x
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hgen : Ltilde d.radical (alpha d.radical) ⊔ T = S :=
    local_residual_edge_generation _ hgen₀ rfl (base_adjacent _)
  have hBn : T ≤ normalizer (B : Set (FreeAmalgam d.radical)) := by
    rw [show T = d.radical.map (embedM d.radical) from Q_beta _]
    change d.radical.map (embedM d.radical) ≤ normalizer
      ((starSpan d.radical Y).map (embedS d.radical) : Set _)
    rw [←embedM_comp_subtype,←map_map]
    have hdn : d.radical ≤ normalizer
        ((starSpan d.radical Y).map d.radical.subtype : Set d.overgroup) := by
      have hh := le_normalizer_map (H := starSpan d.radical Y) d.radical.subtype
      rw [normalizer_eq_top_iff.mpr inferInstance,←MonoidHom.range_eq_map,range_subtype] at hh
      exact hh
    exact (map_mono hdn).trans (le_normalizer_map (embedM d.radical))
  have htriple : ⁅⁅A,Ltilde d.radical (alpha d.radical)⁆,Q₀⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (commutator_mono
      (h.replacement_sourceStarAlpha_commutator_le_U d geometry hb Y P hY hn) le_rfl).trans
      ((commutator_mono (U_le_Z _) le_rfl).trans (Z_centralizes_Q _ _ rfl).le)
  have hBJ : B ≤ centralizer (J : Set (FreeAmalgam d.radical)) :=
    h.replacement_starSpan_centralizes_endpoint d geometry hb path hfirst Y P hY hn
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  have hs := h.replacement_component_image_structure d
  let : ((pResidual 2 d.overgroup).map q).Normal := by rw [h.replacement_residual d]; exact hs.2.1
  let : IsSimpleGroup ((pResidual 2 d.overgroup).map q) := by rw [h.replacement_residual d]; exact hs.2.2.1
  let : IsQuasisimple ((pResidual 2 d.overgroup).map q) := by rw [h.replacement_residual d]; exact hs.2.2.2.1
  have hcent : centralizer ((pResidual 2 d.overgroup).map q : Set (d.overgroup ⧸ pCore 2 d.overgroup)) = ⊥ := by
    rw [h.replacement_residual d]
    exact hs.2.2.2.2
  have hnot : ¬ J ≤ Q₀ := by
    have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
    exact (critical_reverse d.radical geometry hedge _ rfl
      (by rwa [geometry.distance_constant _ rfl]) z path.end_color path.critical).2
  have hJgen := edge_conjugate_generation_of_centric_component d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) hgen₀ q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hcent rfl
    (base_adjacent _) J hJS hnot
  change conjugatesIn J S ⊔ T = S at hJgen
  let : Finite S := finite_stabilizer _ _
  let : (Q₀.subgroupOf S).Normal := Q_normal _ _
  have hAc : A.subgroupOf S ≤ normalClosure (B.subgroupOf S : Set S) := by
    apply (map_le_map_iff_of_injective S.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hAS]
    apply (sourceStarAlpha_le_iff d.radical Y _).mpr
    intro g
    rintro _ ⟨b,hb,rfl⟩
    have hg : (g : FreeAmalgam d.radical) ∈ S := by
      simpa only [S,alpha,stabilizer_m_base] using g.property
    exact mem_map_of_mem S.subtype
      ((inferInstance : (normalClosure (B.subgroupOf S : Set S)).Normal).conj_mem
        ⟨b,hBS hb⟩ (le_normalClosure hb) ⟨g,hg⟩)
  have hJn : normalClosure (J.subgroupOf S : Set S) ⊔ T.subgroupOf S = ⊤ := by
    apply (map_injective S.subtype_injective)
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,map_subgroupOf_eq_of_le hTS]
    apply le_antisymm (sup_le (map_subtype_le _) hTS)
    exact hJgen.ge.trans (sup_le_sup_right (conjugatesIn_le_mapped_normalClosure S J hJS) T)
  have hgn : pResidual 2 S ⊔ T.subgroupOf S = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hTS,←MonoidHom.range_eq_map,range_subtype]
    exact hgen
  have htn : IsPGroup 2 (T.subgroupOf S) := by
    have ht : IsPGroup 2 T := by
      rw [show T = d.radical.map (embedM d.radical) from Q_beta _]
      exact (h.replacement_two_group d).map _
    exact ht.comap_subtype
  have htri : ⁅⁅A.subgroupOf S,pResidual 2 S⁆,Q₀.subgroupOf S⁆ = ⊥ := by
    apply map_injective S.subtype_injective
    rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hAS,
      map_subgroupOf_eq_of_le hQS,Subgroup.map_bot]
    exact htriple
  have hbjn : B.subgroupOf S ≤ centralizer (J.subgroupOf S : Set S) := by
    intro b hb j hj
    exact Subtype.ext (hBJ hb j.val hj)
  have hbn : T.subgroupOf S ≤ normalizer (B.subgroupOf S : Set S) :=
    (comap_mono hBn).trans (le_normalizer_comap S.subtype)
  have hbound := seed_core_displacement (A.subgroupOf S) (B.subgroupOf S)
    (Q₀.subgroupOf S) (T.subgroupOf S) (J.subgroupOf S)
    (comap_mono hBA) hAc (comap_mono hQT) htn hgn hbn htri hbjn hJn
  have hh := map_mono (f := S.subtype) hbound
  rw [map_commutator,map_subgroupOf_eq_of_le hAS,map_subgroupOf_eq_of_le hQS] at hh
  intro x hx
  obtain ⟨y,hy,rfl⟩ := hh hx
  refine ⟨hy.1,?_⟩
  rintro _ ⟨l,hl,rfl⟩
  exact congrArg Subtype.val (hy.2 l hl)

/-- In particular the full characteristic holomorph star has the displacement
required by the centralizer cut, before its moving-plus-fixed inclusion. -/
theorem Input.replacement_starSpan_core_displacement
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical))) :
    ⁅(starSpan d.radical Y).map (embedS d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical) := by
  obtain ⟨z,path,hfirst⟩ := exists_replacement_critical_path_through_beta d geometry hb
  have hB : (starSpan d.radical Y).map (embedS d.radical) ≤ sourceStarAlpha d.radical Y := by
    have hh := (sourceStarAlpha_le_iff d.radical Y (sourceStarAlpha d.radical Y)).mp
      le_rfl (1 : Mbar d.radical)
    have he : (MulAut.conj (1 : FreeAmalgam d.radical)).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change 1 * x * 1⁻¹ = x
      simp
    simpa only [OneMemClass.coe_one,he,Subgroup.map_id] using hh
  exact (commutator_mono hB le_rfl).trans
    (h.replacement_sourceStarAlpha_core_displacement d geometry hb path hfirst Y P hY hn)

/-- The intrinsic input supplies the seed and geometry with both proved
commutator comparisons. No star inclusion is assumed in this constructor. -/
theorem Input.exists_replacement_star_displacements :
    ∃ geometry : Geometry d.radical, 0 < geometry.b d.radical ∧
      ∃ P : Sylow 2 (Ltilde d.radical (alpha d.radical)), ∃ Y : Subgroup d.radical,
        Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P ∧
        Q d.radical (beta d.radical) ≤
          normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical)) ∧
        ⁅sourceStarAlpha d.radical Y,Ltilde d.radical (alpha d.radical)⁆ ≤
          U d.radical (alpha d.radical) ∧
        ⁅sourceStarAlpha d.radical Y,Q d.radical (alpha d.radical)⁆ ≤
          fixedCore d.radical (alpha d.radical) := by
  obtain ⟨geometry,hb,_⟩ := h.replacement_positive_even_geometry d
  obtain ⟨P,Y,hY,hn,_,_⟩ := h.exists_replacement_source_seed d
  obtain ⟨z,path,hfirst⟩ := exists_replacement_critical_path_through_beta d geometry hb
  exact ⟨geometry,hb,P,Y,hY,hn,
    h.replacement_sourceStarAlpha_commutator_le_U d geometry hb Y P hY hn,
    h.replacement_sourceStarAlpha_core_displacement d geometry hb path hfirst Y P hY hn⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
