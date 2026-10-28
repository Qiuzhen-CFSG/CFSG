module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicCover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.QuadraticSylow

/-!
# Radius-image control in the remaining cubic full-symmetric branch

Every seed in a sufficiently close radius acts quadratically on the actual
natural central quotient. The radius normalizes each seed and is a two-group.
The normal-quadratic Sylow calculation bounds its permutation image by eight.
Because the retained kernel E/Q has order three, the same bound measures the
index modulo the literal two-core Q. The proof never replaces E by Q.

Conjugation transports this estimate to arbitrary component vertices and
the vertex two steps before the actual critical endpoint. The whole-core
and literal rank-two alternatives retain these bounds and both central-cover
orders. The radius centrality, critical-path exclusions of Section 5, and
final reconstruction remain with qt-e-ms-small-a6-reconstruction.

Source: MS93 (5.2), printed pp.914--915. The graph argument adapts
Natural.Exhaustion.LargeDistance.SectionFive.RadiusImage to the original
cubic-kernel pair, retaining its group, quotient, and action conventions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open CubicAction
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "X₀" => centralOmega L R
local notation "W" => (⁅X₀,K⁆ : Subgroup M)
local notation "π" => projection h e hz hk
local notation "T" => edge L R

open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

/-- A centralizing commutator on the full cover fixes the actual moved image
in the natural quotient. Surjectivity suffices; injectivity is not assumed. -/
theorem image_centralizes_moved (A B : Subgroup M)
    (hfix : ⁅W,A⁆ ≤ centralizer (B : Set M)) :
    B.map π ≤ subspaceKernel (BinaryPermutation.naturalRepresentation (Fin 6))
      (subspaceCommutator (BinaryPermutation.naturalRepresentation (Fin 6)) ⊤ (A.map π)) ⊤ := by
  let := h.relative_normal
  rintro _ ⟨b,hb,rfl⟩
  refine ⟨mem_top _,?_⟩
  have hf : subspaceCommutator (BinaryPermutation.naturalRepresentation (Fin 6)) ⊤ (A.map π) ≤
      LinearMap.ker (BinaryPermutation.naturalRepresentation (Fin 6) (π b) - LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨a,ha,rfl⟩,v,_,rfl⟩
    obtain ⟨w,hw⟩ := coverProjection_surjective h e hz hk (Multiplicative.ofAdd v)
    let z : W := MulAut.conjNormal a w * w⁻¹
    have hzA : (z : M) ∈ ⁅W,A⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator ha w.property
    have hfixed : MulAut.conjNormal b z = z := by
      apply Subtype.ext
      change b * (z : M) * b⁻¹ = z
      rw [hfix hzA b hb, mul_inv_cancel_right]
    have hcz : (coverProjection h e hz hk z).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (π a) v - v := by
      change (coverProjection h e hz hk (MulAut.conjNormal a w * w⁻¹)).toAdd = _
      rw [map_mul,map_inv]
      simp only [toAdd_mul,toAdd_inv,sub_eq_add_neg]
      rw [coverProjection_conjugate h e hz hk a w (MulAut.conjNormal a w) rfl,hw]
      rfl
    have hact := coverProjection_conjugate h e hz hk b z (MulAut.conjNormal b z) rfl
    rw [hfixed,hcz] at hact
    change BinaryPermutation.naturalRepresentation (Fin 6) (π b)
      (BinaryPermutation.naturalRepresentation (Fin 6) (π a) v-v) -
      (BinaryPermutation.naturalRepresentation (Fin 6) (π a) v-v) = 0
    exact sub_eq_zero.mpr hact.symm
  intro v hv
  simpa only [LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero] using hf hv

theorem image_quadratic_of_commutator (A : Subgroup M)
    (hfix : ⁅W,A⁆ ≤ centralizer (A : Set M)) :
    QuadraticPointCore.Quadratic (A.map π) := by
  intro a ha b hb v
  exact (image_centralizes_moved h e hz hk A A hfix ha).2 _
    (Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩)

private theorem seed_le_stabilizer_of_dist_le {a b : Vertex T}
    (ha : color T a = false)
    (hd : (cosetGraph T).dist a b ≤ sourceDistance h) :
    Z T a ≤ stabilizer T b := by
  apply Z_le_stabilizer_of_dist_le a ((sourceGeometry h).exists_critical a ha)
  rwa [(sourceGeometry h).distance_constant a ha]

private theorem graph_seed_quadratic (a : Vertex T) (ha : color T a = false)
    (hd : (cosetGraph T).dist a (alpha T) ≤ sourceDistance h) :
    QuadraticPointCore.Quadratic (CubicAction.graphImage h e hz hk (Z T a)) := by
  let A := (Z T a).comap (embedM T)
  have hm : A.map (embedM T) = Z T a :=
    map_comap_eq_self ((seed_le_stabilizer_of_dist_le (h := h) ha hd).trans_eq (stabilizer_m_base T))
  have hZa : Z T (alpha T) ≤ stabilizer T a :=
    seed_le_stabilizer_of_dist_le (h := h) rfl (by rwa [SimpleGraph.dist_comm])
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a ha
  have hcomm : ⁅U T (alpha T),Z T a⁆ ≤ Z T a :=
    le_normalizer_iff_commutator_le_right.mp ((show U T (alpha T) ≤ Z T (alpha T) from
      le_normalizer_iff_commutator_le_left.mp
        ((map_subtype_le _).trans (Z_normalized T (alpha T)))).trans
      (hZa.trans (Z_normalized T a)))
  apply image_quadratic_of_commutator h e hz hk A
  intro x hx y hy
  apply embedM_injective T
  simp only [map_mul]
  have hx' : embedM T x ∈ Z T a := by
    apply hcomm
    rw [←graph_U_map h e hz,←hm,←map_commutator]
    exact mem_map_of_mem _ hx
  exact (le_centralizer_iff_isMulCommutative.mpr inferInstance) hx' _ hy

private theorem graphImage_normalizes {A B : Subgroup (FreeAmalgam T)}
    (hn : B ≤ normalizer (A : Set (FreeAmalgam T))) :
    CubicAction.graphImage h e hz hk B ≤ normalizer (CubicAction.graphImage h e hz hk A : Set S) := by
  exact (map_mono ((comap_mono hn).trans (le_normalizer_comap (embedM T)))).trans
    (le_normalizer_map π)

include h e hz hk in
private theorem radius_image_at_base_le_eight (hb : 2 < sourceDistance h) (a : Vertex T)
    (ha : color T a = false)
    (hd : (cosetGraph T).dist a (alpha T) + 2 ≤ sourceDistance h) :
    (Q T (alpha T)).relIndex (V T a) ≤ 8 := by
  have hVaQ : V T a ≤ Q T a := V_le_Q T (geometry := sourceGeometry h) ha hb
  have hVbase : V T a ≤ stabilizer T (alpha T) := by
    apply (V_le_iff T ha _).mpr
    intro d hdcol hda
    apply seed_le_stabilizer_of_dist_le (h := h) hdcol
    have ht := (cosetGraph_connected T).dist_triangle (u:=d) (v:=a) (w:=alpha T)
    omega
  let I := {d : Vertex T // color T d = false ∧
    (cosetGraph T).dist d a ≤ 2}
  have hV : V T a = ⨆ d : I, Z T d.val := by
    apply le_antisymm
    · apply (V_le_iff T ha _).mpr
      intro d hd hda
      exact le_iSup_of_le (⟨d,hd,hda⟩ : I) le_rfl
    · exact iSup_le fun d => le_iSup_of_le d.val (le_iSup_of_le d.property.2 le_rfl)
  have hseed (d : I) : Z T d.val ≤ V T a :=
    hV ▸ le_iSup (fun d : I => Z T d.val) d
  have hm (d : I) : ((Z T d.val).comap (embedM T)).map (embedM T) =
      Z T d.val := map_comap_eq_self ((hseed d).trans hVbase |>.trans_eq (stabilizer_m_base T))
  have hgen : CubicAction.graphImage h e hz hk (V T a) = ⨆ d : I, CubicAction.graphImage h e hz hk (Z T d.val) := by
    have hcmap : (V T a).comap (embedM T) =
        ⨆ d : I, (Z T d.val).comap (embedM T) := by
      apply map_injective (embedM_injective T)
      rw [Subgroup.map_iSup]
      simp only [hm]
      rw [map_comap_eq_self (hVbase.trans_eq (stabilizer_m_base T)),hV]
    change ((V T a).comap (embedM T)).map π = _
    rw [hcmap,Subgroup.map_iSup]
    rfl
  have hP : IsPGroup 2 (CubicAction.graphImage h e hz hk (V T a)) :=
    (((Q_isPGroup T (h.relative_radical.isPGroup)
      (h.relative_radical.twoCore_le) a ha).to_le hVaQ).comap_of_injective
        (embedM T) (embedM_injective T)).map π
  have hP0 : IsPGroup 2 ((V T a).comap (embedM T)) :=
    ((Q_isPGroup T h.relative_radical.isPGroup
      h.relative_radical.twoCore_le a ha).to_le hVaQ).comap_of_injective
      (embedM T) (embedM_injective T)
  have hcard : Nat.card (CubicAction.graphImage h e hz hk (V T a)) =
      (Q T (alpha T)).relIndex (V T a) := by
    change Nat.card (((V T a).comap (embedM T)).map π) = _
    rw [permutation_image_card_of_two h e hz hk _ hP0]
    have hQ : (Q T (alpha T)).comap (embedM T) = pCore 2 M := by
      rw [Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le,
        comap_map_eq_self_of_injective (embedM_injective T)]
    rw [←hQ,relIndex_comap,map_comap_eq_self (hVbase.trans_eq (stabilizer_m_base T))]
  rw [←hcard]
  apply Natural.Exhaustion.LargeDistance.SectionFive.QuadraticSylow.generated_normal_quadratic_bound _ hP _ hgen
  · intro d
    let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) d.val d.property.1
    let := IsElementaryAbelian.comap_of_injective (p:=2) (embedM T)
      (embedM_injective T) (Z T d.val)
    exact IsElementaryAbelian.map π
  · intro d
    apply graphImage_normalizes h e hz hk
    exact hVaQ.trans ((Q_le_stabilizer_of_dist_le_two a d.val ha d.property.1
      (by rw [SimpleGraph.dist_comm]; exact d.property.2)).trans (Z_normalized T d.val))
  · intro d
    apply graph_seed_quadratic h e hz hk d.val d.property.1
    have ht := (cosetGraph_connected T).dist_triangle (u:=d.val) (v:=a) (w:=alpha T)
    have hda := d.property.2
    omega


include h e hz hk in
/-- Source (5.2)'s radius image estimate, for either central cover and every
actual radical image. -/
theorem radius_image_index_le_eight (a c : Vertex T)
    (ha : color T a = false) (he : color T c = false)
    (hd : (cosetGraph T).dist a c + 2 ≤ sourceDistance h) :
    (Q T c).relIndex (V T a) ≤ 8 := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color T he
  have hbase : act T g⁻¹ c = alpha T := by
    rw [hg,act_mVertex]
    simp only [mul_inv_cancel]
    rfl
  have hbnd := radius_image_at_base_le_eight h e hz hk (distance_gt_two h e hz hk) (act T g⁻¹ a)
    (by rwa [action_preserves_color]) (by rw [←hbase,dist_act]; exact hd)
  rw [←hbase,Q_act,V_act,
    relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective] at hbnd
  exact hbnd

include h e hz hk in
/-- The source estimate at the original critical path's component vertex two
steps before its endpoint. No point-core premise is needed. -/
theorem critical_radius_image_index_le_eight {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a') :
    (Q T (p.walk.getVert (p.walk.length-2))).relIndex (V T a) ≤ 8 := by
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  apply radius_image_index_le_eight h e hz hk a _ p.start_color
  · apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have heven := sourceDistance_even h
    rw [hl,Nat.even_iff]
    rw [Nat.even_iff] at heven
    omega
  · rw [p.dist_start (Nat.sub_le _ _),hl]
    have hb := distance_gt_two h e hz hk
    omega



omit hk in
include h e hz in
/-- The original whole-core alternative now supplies the actual radius-image
bound and both central-cover orders in its only remaining cubic branch. -/
theorem coreExhaustion_or_cubic_radius_bounds :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧ 2 < sourceDistance h ∧
      (∀ a : Vertex T, color T a = false →
        Nat.card (U T a) = 16 ∨ Nat.card (U T a) = 32) ∧
      ∀ a c : Vertex T, color T a = false → color T c = false →
        (cosetGraph T).dist a c + 2 ≤ sourceDistance h →
          (Q T c).relIndex (V T a) ≤ 8 := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,
      radius_image_index_le_eight h e hz hk⟩

omit hk in
include h e hz in
/-- The literal C.1.32 consumer keeps the entire core and the cubic kernel. -/
theorem rankTwo_or_cubic_radius_bounds :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧ 2 < sourceDistance h ∧
      (∀ a : Vertex T, color T a = false →
        Nat.card (U T a) = 16 ∨ Nat.card (U T a) = 32) ∧
      ∀ a c : Vertex T, color T a = false → color T c = false →
        (cosetGraph T).dist a c + 2 ≤ sourceDistance h →
          (Q T c).relIndex (V T a) ≤ 8 :=
  (coreExhaustion_or_cubic_radius_bounds h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
