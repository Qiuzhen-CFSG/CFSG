module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticRadiusAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.LargeDisplacement

/-!
# The original radius displacement outside the root branch

The radius kernel two steps before a critical endpoint lies in the endpoint
stabilizer. Since it lies in the initial two-core, it centralizes the critical
commutator. Failure of displacement into the initial natural seed therefore
forces the small critical-image branch. The original field-four comparison
then gives both critical indices equal to four; center-freeness removes the
full-X attachments at both ends.

Thus critical index at least sixteen supplies its own displacement, yielding
an actual overlapping backward critical path. A separate consumer isolates
the displacement still needed when both indices are four. This leaves the
root branch and the final distance exclusion open.

Source: MS93 (3.3), p.867, and (5.2), (5.7)--(5.8), pp.914,919--920;
Aschbacher--Smith 9.3.10, p.734.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

/-- Failure of the original radius displacement forces the exact order-four
root branch at both endpoints, and eliminates both full-X attachments. -/
theorem original_radius_displacement_or_root
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (path : CriticalPath R geometry a z),
      ⁅V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)),Z R z⁆ ≤ Z R a ∨
      ((Q R z).relIndex (Z R a) = 4 ∧ (Q R a).relIndex (Z R z) = 4 ∧
        X R a = Z R a ∧ X R z = Z R z) := by
  intro R geometry a z path
  by_cases hdisp : ⁅V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)),Z R z⁆ ≤ Z R a
  · exact Or.inl hdisp
  apply Or.inr
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hcard,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hself : centralizer (pCore 2 c.M : Set c.M) ≤ pCore 2 c.M := by
    simpa only [c.fitting_center.1] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := c.M))
  have hne : R ≠ ⊥ := fun hr => hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  have hfour : 4 ≤ geometry.b R := c.original_geometry_four_le eK geometry
  let Y := V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))
  have hYQ : Y ≤ Q R a := inf_le_left.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hcentral : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _) :=
    (hYQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color)))).trans
      (centralizer_le (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path))
  have hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅Z R a,Z R z⁆ := by
    intro h
    apply hdisp
    rw [commutator_comm]
    exact h.trans (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path)
  have hsmall := original_large_critical_index_lt_sixteen_of_critical_escape R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path (by omega) Y (truncated_radius_le_endpoint_stabilizer path (by omega))
    hcentral hbad
  obtain ⟨ha4,hz4⟩ := original_small_critical_indices_eq_four R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path (by omega) hsmall
  have hXa := original_small_critical_X_decomposition R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path (by omega) hsmall
  have rev := c.original_critical_reverse eK geometry
    (lt_of_lt_of_le (by decide : 0 < 4) hfour) path
  have hXz := original_small_critical_X_decomposition R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq rev (by omega) (by rw [hz4]; decide)
  rw [c.graph_X_fixed_eq_bot a path.start_color,sup_bot_eq,←c.original_Z_eq_U a path.start_color] at hXa
  rw [c.graph_X_fixed_eq_bot z path.end_color,sup_bot_eq,←c.original_Z_eq_U z path.end_color] at hXz
  exact ⟨ha4,hz4,hXa,hXz⟩

theorem original_radius_displacement_of_large_critical_index
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (path : CriticalPath R geometry a z),
      16 ≤ (Q R z).relIndex (Z R a) →
      ⁅V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)),Z R z⁆ ≤ Z R a := by
  intro R geometry a z path hlarge
  rcases c.original_radius_displacement_or_root eK geometry path with h | h
  · exact h
  · change 16 ≤ (Q R z).relIndex (Z R a) at hlarge
    rw [h.1] at hlarge
    omega

/-- The large critical-image branch now supplies its own radius displacement
and hence the original overlapping backward critical path. -/
theorem original_backward_path_of_large_critical_index
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a t z : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → 16 ≤ (Q R z).relIndex (Z R a) →
      ∃ d t', Adjacent R a t' ∧ Adjacent R d t' ∧
        (∃ back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = t' ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry a t z path hat hlarge
  exact c.original_backward_path_of_radius_displacement eK geometry path hat
    (c.original_radius_displacement_of_large_critical_index eK geometry path hlarge)

/-- It suffices to establish the remaining displacement only in the precise
root branch: both critical images have order four and both full-X layers
are already the original natural seeds. -/
theorem original_backward_path_of_root_displacement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a t z : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t →
      ((Q R z).relIndex (Z R a) = 4 → (Q R a).relIndex (Z R z) = 4 →
        X R a = Z R a → X R z = Z R z →
        ⁅V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)),Z R z⁆ ≤ Z R a) →
      ∃ d t', Adjacent R a t' ∧ Adjacent R d t' ∧
        (∃ back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = t' ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry a t z path hat hroot
  apply c.original_backward_path_of_radius_displacement eK geometry path hat
  rcases c.original_radius_displacement_or_root eK geometry path with h | ⟨ha,hz,hXa,hXz⟩
  · exact h
  · exact hroot ha hz hXa hXz

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
