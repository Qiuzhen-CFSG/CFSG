module
public import Theory.GroupTheory.Recognition.TransvectionFive.CoreFusionSingleRoot
public import Theory.GroupTheory.Recognition.TransvectionFive.CoreFusionCoverage
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceInvolutions

/-!
# The precise isolated-root alternative in the source recognition

The marked point-centralizer involution coverage and the single-root
rectangle census put every returning point conjugate in the original root.
Sylow conjugacy inside its full normalizer then gives the exact equality
`z^G ∩ N_G(U₁) = U₁#`, the hypothesis of source 39.9. Consequently the
remaining §39–40 alternatives are the two recognition types, Held's
normalizer pattern, or this isolated-root case in one of the two markings.

Source: Aschbacher, *Sporadic Groups* (1994), 39.5–39.10, pp.214–216.
The implication from root isolation to ambient normality (39.9, using
Exercise 2.7) remains unproved here and belongs to
`qt-d-12213-four-recognition`. The conditional theorem at the end and
`FourRecognitionIsolation` expose this exact remaining premise; neither
claims the unconditional source recognition theorem.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.CoreFusion
open UniquenessLinear PlaneTensor
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- The literal class-intersection hypothesis of source 39.9. -/
@[expose] def RowIsolation : Prop :=
  ∀ a ∈ rowNormalizer F, IsConj z a ↔ a ∈ F.row ∧ a ≠ 1

omit [Finite G] in
include F in
private theorem orderOf_of_fused {a : G} (h : IsConj z a) : orderOf a = 2 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  have he : MulAut.conj g z = a := hg
  rw [← he,MulEquiv.orderOf_eq,F.point_orderOf]

/-- The one-root branch has no fused involutions elsewhere in the full
point centralizer. This completes the local placement step of source 39.8. -/
theorem row_only_centralizer_fusion_mem (hrow : IsConj z (element F 1))
    (hcolumn : ¬ IsConj z (element F 32)) {a : G}
    (ha : a ∈ Subgroup.centralizer ({z} : Set G)) (hf : IsConj z a) : a ∈ F.row := by
  obtain ⟨c,hc⟩ := CoreFusionCoverage.marked_involution_conjugate_rectangle F a ha
    (orderOf_of_fused F hf)
  have hf' : IsConj z ((c : G)*a*(c : G)⁻¹) :=
    hf.trans (isConj_iff.mpr ⟨(c:G),rfl⟩)
  have hr : (c : G)*a*(c : G)⁻¹ ∈ F.row := by
    rcases hc with hc | hc
    · exact row_only_plane_fusion_mem F hrow hcolumn hc hf'
    · exact row_only_threeSpace_fusion_mem F hrow hcolumn hc hf'
  exact (mem_normalizer_iff.mp (point_centralizer_le_row_normalizer F c.property) a).mpr hr

/-- Source 39.8's isolated alternative in the entire literal row normalizer,
with no assumption about its splitting or an abstract normalizer model. -/
theorem row_only_isolation (hrow : IsConj z (element F 1))
    (hcolumn : ¬ IsConj z (element F 32)) : RowIsolation F := by
  intro a ha
  constructor
  · intro hf
    let M := rowNormalizer F
    let aM : M := ⟨a,ha⟩
    let S := (sourceSylow F).subtype
      ((sourceSylow_le_point_centralizer F).trans (point_centralizer_le_row_normalizer F))
    have ho : orderOf aM = 2 :=
      (Subgroup.orderOf_coe aM).symm.trans (orderOf_of_fused F hf)
    obtain ⟨y,hy⟩ := involution_into_sylow S aM ho
    obtain ⟨g,hg⟩ := isConj_iff.mp hy
    have he : (g:G)*a*(g:G)⁻¹ = ((y : M) : G) := congrArg Subtype.val hg
    have hyH : ((y : M) : G) ∈ Subgroup.centralizer ({z} : Set G) :=
      sourceSylow_le_point_centralizer F y.property
    have hyrow := row_only_centralizer_fusion_mem F hrow hcolumn hyH
      (hf.trans (isConj_iff.mpr ⟨(g:G),he⟩))
    have har : a ∈ F.row := (mem_normalizer_iff.mp g.property a).mpr (he.symm ▸ hyrow)
    refine ⟨har,?_⟩
    intro he1
    have ho := orderOf_of_fused F hf
    simp [he1] at ho
  · rintro ⟨har,ha1⟩
    exact (row_fusion_iff F).mp hrow a har ha1

/-- The source §39 reduction leaves only the two local fusion types, Held's
normalizer pattern, or the precise isolated-root premise of 39.9. -/
theorem alternatives_or_isolation (hcore : PointCoreFusion z) :
    F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern ∨
      RowIsolation F ∨ RowIsolation (oppositeMarking F) := by
  have hroot := root_fusion_disjunction F hcore
  by_cases hr : IsConj z (element F 1)
  · by_cases hc : IsConj z (element F 32)
    · rcases FusionTypes.alternatives_of_tests F hr hc (not_conjugate_core33 F)
        ((opposite_root_fusion F).1.mpr hc) ((opposite_root_fusion F).2.mpr hr)
        (not_conjugate_core33 (oppositeMarking F)) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (row_only_isolation F hr hc))))
  · have hc := hroot.resolve_left hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (row_only_isolation (oppositeMarking F)
      ((opposite_root_fusion F).1.mpr hc) (fun h => hr ((opposite_root_fusion F).2.mp h))))))

omit [Finite G] in
/-- Simplicity excludes a normal marked root. The subgroup and full
centralizer are the original ones. -/
theorem not_row_normal (hG : IsSimpleGroup G) (hcore : PointCoreFusion z) : ¬ F.row.Normal := by
  intro hn
  have he : rowNormalizer F = ⊤ := normalizer_eq_top_iff.mpr hn
  exact (flag_normalizers_ne_top F hG hcore).1 he

/-- Once source 39.9 is proved, the complete local type alternative follows.
Its remaining normality proof belongs to the dimension-four assembly owner. -/
theorem alternatives_of_isolation_normality (hG : IsSimpleGroup G) (hcore : PointCoreFusion z)
    (normality : ∀ (w : G) (E : MarkedCentralizer w), RowIsolation E → E.row.Normal) :
    F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern := by
  rcases alternatives_or_isolation F hcore with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (not_row_normal F hG hcore (normality z F h)).elim
  · exact (not_row_normal (oppositeMarking F) hG hcore
      (normality z (oppositeMarking F) h)).elim

end Theory.GroupTheory.TransvectionFive.CoreFusion
