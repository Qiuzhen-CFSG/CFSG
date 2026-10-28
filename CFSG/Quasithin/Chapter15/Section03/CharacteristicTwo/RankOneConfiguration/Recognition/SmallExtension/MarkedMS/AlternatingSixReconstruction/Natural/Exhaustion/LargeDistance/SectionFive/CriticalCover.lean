module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Graph
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates.CriticalCommutator
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore.MovingFixer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalAction

/-!
# Critical commutators on the full symmetric central cover

The faithful natural quotient detects the centralizer of the graph moving
layer. Thus the local centralizer is precisely the two-core. Critical-pair
reversal and the full-stabilizer commutator identity then place the nonzero
critical commutator in both moving layers. In particular the opposite seed
acts quadratically on the original cover and its natural quotient.

These statements retain the actual replacement and both possible cover
orders. They are the local input to the Section 5 radius calculation, without
a natural subgroup, a point-radical image or a split central kernel.
Source: MS93 (2.2), (3.3), (5.0)--(5.2), printed pp.856,866--867,912--914.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
  (hc : DistanceTwo.CentralLayer d)

include s hc in
/-- The exact centralizer uses the faithful quotient of the whole cover. -/
theorem C_alpha : C d.radical (alpha d.radical) = Q d.radical (alpha d.radical) := by
  apply le_antisymm
  · rintro x ⟨hx,hxC⟩
    obtain ⟨m,rfl⟩ := (stabilizer_m_base d.radical) ▸ hx
    have hm : m ∈ centralizer (replacementMoved d : Set d.overgroup) := by
      intro w hw
      apply embedM_injective d.radical
      simp only [map_mul]
      apply hxC
      apply DistanceEight.U_le_Z d.radical (alpha d.radical)
      rw [hc.U_eq_moved]
      exact mem_map_of_mem _ hw
    rw [moved_centralizer s] at hm
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)]
    exact mem_map_of_mem _ hm
  · intro x hx
    exact ⟨hx.1, le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical (alpha d.radical) rfl)) hx⟩

include s hc in
/-- The same centralizer identity at every component vertex. -/
theorem C_eq_Q (a : Vertex d.radical) (ha : color d.radical a = false) :
    C d.radical a = Q d.radical a := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  have hh := C_act (R := d.radical) g (alpha d.radical)
  have hq := Q_act d.radical g (alpha d.radical)
  simp only [alpha, act_mVertex, one_mul] at hh hq
  have hbase := C_alpha s hc
  change C d.radical (mVertex d.radical 1) = Q d.radical (mVertex d.radical 1) at hbase
  rw [hh,hbase,hq]

include s hc in
theorem edgeCentralizerCondition : EdgeCentralizerCondition d.radical := by
  intro a t ha hat
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases hcol : color d.radical t <;> simp_all
  apply le_antisymm
  · rintro x ⟨hx,hxC⟩
    rw [← C_eq_Q s hc a ha]
    exact ⟨hx.2 a (adjacent_symm d.radical hat),hxC⟩
  · intro x hx
    exact ⟨Q_le_adjacent_h d.radical ht hat hx,
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a ha)) hx⟩

/-- The image uses the given symmetric marking and the literal graph inclusion. -/
def graphImage (A : Subgroup (FreeAmalgam d.radical)) : Subgroup (Equiv.Perm (Fin 6)) :=
  (A.comap (embedM d.radical)).map s.projection

/-- The order of this image is the actual relative two-core index. -/
theorem graphImage_card (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ stabilizer d.radical (alpha d.radical)) :
    Nat.card (graphImage s A) = (Q d.radical (alpha d.radical)).relIndex A := by
  rw [graphImage, ← relIndex_ker, s.projection_kernel]
  have hm : (A.comap (embedM d.radical)).map (embedM d.radical) = A :=
    map_comap_eq_self (hA.trans_eq (stabilizer_m_base d.radical))
  rw [← relIndex_map_map_of_injective _ _ (embedM_injective d.radical), hm,
    ← Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]

variable {a a' : Vertex d.radical}
  (p : CriticalPath d.radical (replacementGeometry h d) a a')

include s hc in
theorem critical_reverse_pair :
    CriticalPair d.radical a' a ((replacementGeometry h d).exists_critical a' p.end_color) := by
  apply critical_reverse d.radical (replacementGeometry h d) (edgeCentralizerCondition s hc)
    a p.start_color _ a' p.end_color p.critical
  rw [(replacementGeometry h d).distance_constant a p.start_color]
  exact replacementDistance_pos h d

include p in
/-- No central attachment is discarded from either critical moving layer. -/
theorem critical_Z_commutator_le_moving :
    ⁅Z d.radical a,Z d.radical a'⁆ ≤ U d.radical a ⊓ U d.radical a' := by
  have hza : Z d.radical a ≤ stabilizer d.radical a' :=
    Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hza' : Z d.radical a' ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [SimpleGraph.dist_comm,p.critical.1,
      (replacementGeometry h d).distance_constant a p.start_color,
      (replacementGeometry h d).distance_constant a' p.end_color]
  apply le_inf
  · rw [← SourceReduction.Estimates.Z_full_commutator h d a p.start_color]
    exact commutator_mono le_rfl hza'
  · rw [commutator_comm, ← SourceReduction.Estimates.Z_full_commutator h d a' p.end_color]
    exact commutator_mono le_rfl hza

include s hc p in
/-- The critical commutator is nonzero on the original free-amalgam carriers. -/
theorem critical_Z_commutator_ne_bot : ⁅Z d.radical a,Z d.radical a'⁆ ≠ ⊥ := by
  apply critical_noncommutation d.radical (replacementGeometry h d)
    (edgeCentralizerCondition s hc) a p.start_color _ p.critical
  rw [(replacementGeometry h d).distance_constant a p.start_color]
  exact replacementDistance_pos h d

include p in
/-- The opposite seed acts quadratically on the entire moved cover. -/
theorem critical_moving_double_commutator : ⁅⁅U d.radical a,Z d.radical a'⁆,Z d.radical a'⁆ = ⊥ := by
  let : IsElementaryAbelian 2 (X d.radical a') := omegaCenter_elementary _
  let : IsElementaryAbelian 2 (Z d.radical a') := IsElementaryAbelian.of_le
    ((replacementGeometry h d).omega_bound a' p.end_color (by
      rw [(replacementGeometry h d).distance_constant a' p.end_color]
      exact replacementDistance_pos h d))
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact ((commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl).trans
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right)).trans
      ((DistanceEight.U_le_Z d.radical a').trans
        (le_centralizer_iff_isMulCommutative.mpr inferInstance))

omit hc p in
/-- A centralizing commutator on the full cover fixes the actual moved image
in the natural quotient. Surjectivity suffices; injectivity is not assumed. -/
theorem image_centralizes_moved (A B : Subgroup d.overgroup)
    (hfix : ⁅replacementMoved d,A⁆ ≤ centralizer (B : Set d.overgroup)) :
    B.map s.projection ≤ subspaceKernel (naturalRepresentation (Fin 6))
      (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map s.projection)) ⊤ := by
  let := replacementMoved_normal h d
  rintro _ ⟨b,hb,rfl⟩
  refine ⟨mem_top _,?_⟩
  have hf : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map s.projection) ≤
      LinearMap.ker (naturalRepresentation (Fin 6) (s.projection b) - LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨a,ha,rfl⟩,v,_,rfl⟩
    obtain ⟨w,hw⟩ := coverProjection_surjective h e hz hn d (Multiplicative.ofAdd v)
    let z : replacementMoved d := MulAut.conjNormal a w * w⁻¹
    have hzA : (z : d.overgroup) ∈ ⁅replacementMoved d,A⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator ha w.property
    have hfixed : MulAut.conjNormal b z = z := by
      apply Subtype.ext
      change b * (z : d.overgroup) * b⁻¹ = z
      rw [hfix hzA b hb, mul_inv_cancel_right]
    have hcz : (coverProjection h e hz hn d z).toAdd =
        naturalRepresentation (Fin 6) (s.projection a) v - v := by
      change (coverProjection h e hz hn d (MulAut.conjNormal a w * w⁻¹)).toAdd = _
      rw [map_mul,map_inv]
      simp only [toAdd_mul,toAdd_inv,sub_eq_add_neg]
      rw [s.cover_conjugate a w (MulAut.conjNormal a w) rfl,hw]
      rfl
    have hact := s.cover_conjugate b z (MulAut.conjNormal b z) rfl
    rw [hfixed,hcz] at hact
    change naturalRepresentation (Fin 6) (s.projection b)
      (naturalRepresentation (Fin 6) (s.projection a) v-v) -
      (naturalRepresentation (Fin 6) (s.projection a) v-v) = 0
    exact sub_eq_zero.mpr hact.symm
  intro v hv
  simpa only [LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero] using hf hv

omit hc p in
theorem image_quadratic_of_commutator (A : Subgroup d.overgroup)
    (hfix : ⁅replacementMoved d,A⁆ ≤ centralizer (A : Set d.overgroup)) :
    QuadraticPointCore.Quadratic (A.map s.projection) := by
  intro a ha b hb v
  exact (image_centralizes_moved s A A hfix ha).2 _
    (Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩)

include hc in
/-- Quadraticity at the literal opposite endpoint, on the quotient of either cover. -/
theorem critical_opposite_image_quadratic {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    QuadraticPointCore.Quadratic (graphImage s (Z d.radical a')) := by
  let A := (Z d.radical a').comap (embedM d.radical)
  have hAe : A.map (embedM d.radical) = Z d.radical a' := map_comap_eq_self
    ((critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl
      (replacementDistance_pos h d) p.critical).trans_eq (stabilizer_m_base d.radical))
  apply image_quadratic_of_commutator s A
  intro x hx a ha
  apply embedM_injective d.radical
  simp only [map_mul]
  have hx' : embedM d.radical x ∈ ⁅U d.radical (alpha d.radical),Z d.radical a'⁆ := by
    rw [hc.U_eq_moved, ← hAe, ← map_commutator]
    exact mem_map_of_mem _ hx
  exact (commutator_eq_bot_iff_le_centralizer.mp
    (critical_moving_double_commutator (h := h) p)) hx' _ ha

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
