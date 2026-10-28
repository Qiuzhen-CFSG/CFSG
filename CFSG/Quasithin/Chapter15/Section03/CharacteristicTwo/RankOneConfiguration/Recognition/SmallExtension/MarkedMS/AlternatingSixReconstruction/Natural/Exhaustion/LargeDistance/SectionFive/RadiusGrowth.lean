module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SmallCriticalLine
public import Theory.GroupTheory.CentralizerInjectiveImage
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# Strict growth from critical seeds to their actual radii

Every actor outside the two-core moves each normal section on which the
component acts nontrivially. Otherwise its action kernel has nontrivial
normal image in S₆, contains A₆, and then contains the original two-residual.
Apply this to the full radius modulo its initial seed. Multiplicativity of
fixed indices makes the radius index at least twice the seed index.

Both endpoints use the same critical walk, reversed literally. The actual
replacement application reduces a failure of the strict bound in MS93
(5.11)(1), printed pp.923--924, to radius index exactly four and both seed
indices two. It preserves both cover orders and their central attachment.
The source-selected shifts, the stronger strict bound and intermediate R₄/R₆
noncentrality, and the (5.12) terminal estimates remain with
qt-e-ms-small-a6-exhaustion-large-distance. This is numerical preparation,
not a proof of either terminal source theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- An actor escaping the original two-core cannot fix a normal section
on which the original component acts nontrivially. -/
theorem section_index_two_le (B C : NormalNode d.overgroup)
    (hmove : ¬ ⁅C.val,replacementComponent d⁆ ≤ B.val)
    (A : Subgroup d.overgroup) (hA : ¬ A ≤ pCore 2 d.overgroup) :
    2 ≤ SymmetricSixBudget.sectionIndex A B C := by
  let ρ := sectionAction B C
  let : MulDistribMulAction d.overgroup (Section B C) :=
    MulDistribMulAction.compHom _ ρ
  have hpos : 0 < (FixedPoints.subgroup A (Section B C)).index :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  by_contra! hsmall
  change (FixedPoints.subgroup A (Section B C)).index < 2 at hsmall
  have he : (FixedPoints.subgroup A (Section B C)).index = 1 := by omega
  have htop : FixedPoints.subgroup A (Section B C) = ⊤ := index_eq_one.mp he
  have hAK : A ≤ ρ.ker := by
    intro a ha
    apply MulEquiv.ext
    intro x
    have hx : x ∈ FixedPoints.subgroup A (Section B C) := htop ▸ mem_top x
    exact hx ⟨a,ha⟩
  let : (ρ.ker.map s.projection).Normal := Normal.map inferInstance _ s.surjective
  have hne : ρ.ker.map s.projection ≠ ⊥ := by
    intro hh
    apply hA
    exact hAK.trans (s.projection_kernel ▸ (map_eq_bot_iff ρ.ker).mp hh)
  have hAlt : alternatingGroup (Fin 6) ≤ ρ.ker.map s.projection :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp)
      ((nontrivial_iff_ne_bot _).mpr hne)
  have hcover : replacementComponent d ≤ ρ.ker ⊔ pCore 2 d.overgroup := by
    have hi : (replacementComponent d).map s.projection ≤ ρ.ker.map s.projection := by
      rw [s.component_image]
      exact hAlt
    have hi' := (le_comap_map s.projection (replacementComponent d)).trans (comap_mono hi)
    rwa [comap_map_eq,s.projection_kernel] at hi'
  have hL : replacementComponent d ≤ ρ.ker :=
    le_normal_of_isPPerfect_of_le_sup_pGroup (replacementComponent d) ρ.ker
      (pCore 2 d.overgroup) (by
        have hres : pResidual 2 d.overgroup = replacementComponent d := replacement_residual h d
        rw [←hres]
        exact isPPerfect_pResidual 2)
      pCore_isPGroup hcover
  apply hmove
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha c hc
  have heq := congrArg (fun f : MulAut (Section B C) =>
    f (QuotientGroup.mk' (B.val.subgroupOf C.val) ⟨c,hc⟩)) (hL ha)
  change QuotientGroup.mk' (B.val.subgroupOf C.val) (MulAut.conjNormal a ⟨c,hc⟩) =
    QuotientGroup.mk' (B.val.subgroupOf C.val) ⟨c,hc⟩ at heq
  have hm := QuotientGroup.eq_iff_div_mem.mp heq
  change a*c*a⁻¹/c ∈ B.val at hm
  simpa only [commutatorElement_def,div_eq_mul_inv] using hm

include s in
/-- Every nontrivial marked actor has movement beyond the initial seed. -/
theorem radius_actor_index_two_mul_seed_le (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d)
    (A : Subgroup d.overgroup) (hA : ¬ A ≤ pCore 2 d.overgroup) :
    2 * (centralizer (A : Set d.overgroup)).relIndex (radiusSeed d) ≤
      (centralizer (A : Set d.overgroup)).relIndex (radiusPreimage d) := by
  let B : NormalNode d.overgroup := ⟨radiusSeed d,(inferInstance : (radiusSeed d).Normal)⟩
  let C : NormalNode d.overgroup := ⟨radiusPreimage d,(inferInstance : (radiusPreimage d).Normal)⟩
  have hidx := section_index_two_le s B C (radius_moving_not_le_seed s hc hb) A hA
  exact (Nat.mul_le_mul_right _ hidx).trans
    (SymmetricSixBudget.sectionIndex_mul_lower_le A B C radiusSeed_le_radiusPreimage)

include s in
private theorem critical_radius_index_two_mul_seed_le_base
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    2 * (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) ≤
      (Q d.radical a').relIndex (V d.radical (alpha d.radical)) := by
  let f := embedM d.radical
  let A := (Z d.radical a').comap f
  let K := (Q d.radical a').comap f
  have hAG : Z d.radical a' ≤ f.range :=
    (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical)
      rfl (replacementDistance_pos h d) p.critical).trans_eq (stabilizer_m_base d.radical)
  have hmA : A.map f = Z d.radical a' := map_comap_eq_self hAG
  have hmZ : (radiusSeed d).map f = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
  have hA : ¬ A ≤ pCore 2 d.overgroup := by
    intro hh
    apply (critical_reverse_pair s hc p).2
    rw [←hmA,Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)]
    exact map_mono hh
  have hfixed : Z d.radical (alpha d.radical) ⊓
      centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) =
      Z d.radical (alpha d.radical) ⊓ Q d.radical a' := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←C_eq_Q s hc a' p.end_color]
      exact ⟨Z_le_stabilizer_of_dist_le (alpha d.radical) _ p.critical.1.le hx.1,hx.2⟩
    · exact inf_le_inf_left _ (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a' p.end_color)))
  have hidx : (centralizer (A : Set d.overgroup)).relIndex (radiusSeed d) =
      (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) := by
    calc
      _ = ((radiusSeed d).map f ⊓ centralizer (A.map f : Set (FreeAmalgam d.radical))).relIndex
          ((radiusSeed d).map f) := by
        rw [map_inf_centralizer_of_injective f (embedM_injective d.radical),
          relIndex_map_map_of_injective _ _ (embedM_injective d.radical),inf_relIndex_left]
      _ = _ := by rw [hmA,hmZ,hfixed,inf_relIndex_left]
  have hKA : K ≤ centralizer (A : Set d.overgroup) := by
    intro x hx y hy
    apply embedM_injective d.radical
    simp only [map_mul]
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))) hx _ hy
  have hi := (radius_actor_index_two_mul_seed_le s hc hb A hA).trans
    (relIndex_le_of_le_left hKA index_ne_zero_of_finite)
  rw [hidx,relIndex_comap,radius_comap_map (h := h) hb] at hi
  exact hi

include s in
/-- The radius index at a critical endpoint is at least twice the seed index,
including the transposition branch and the central attachment. -/
theorem critical_radius_index_two_mul_seed_le
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    2 * (Q d.radical a').relIndex (Z d.radical a) ≤
      (Q d.radical a').relIndex (V d.radical a) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex]
    simp only [mul_inv_cancel]
    rfl
  have pc := p.act g⁻¹
  rw [hbase] at pc
  have hi := critical_radius_index_two_mul_seed_le_base s hc hb pc
  rw [←hbase,Q_act,Z_act,V_act,relIndex_map_map_of_injective _ _
    (MulAut.conj (g⁻¹)⁻¹).injective,relIndex_map_map_of_injective _ _
    (MulAut.conj (g⁻¹)⁻¹).injective] at hi
  exact hi

include s in
/-- Strict index growth at both endpoints of the same critical walk. -/
theorem critical_radius_indices_gt_seed
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    (Q d.radical a').relIndex (Z d.radical a) < (Q d.radical a').relIndex (V d.radical a) ∧
      (Q d.radical a).relIndex (Z d.radical a') < (Q d.radical a).relIndex (V d.radical a') := by
  have hf := critical_radius_index_two_mul_seed_le s hc hb p
  let q : CriticalPath d.radical (replacementGeometry h d) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc p⟩
  have hr := critical_radius_index_two_mul_seed_le s hc hb q
  let := finite_Z d.radical a
  let := finite_Z d.radical a'
  have hp : 0 < (Q d.radical a').relIndex (Z d.radical a) :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hp' : 0 < (Q d.radical a).relIndex (Z d.radical a') :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  constructor <;> omega

/-- On the actual replacement, the remaining small opposite-radius branch
has index four or eight, and both endpoint seed indices are exactly two. -/
theorem small_opposite_radius_four_or_eight_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a).relIndex (V d.radical a') ≤ 8) :
    (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
      (Q d.radical a).relIndex (Z d.radical a') = 2 ∧
      ((Q d.radical a).relIndex (V d.radical a') = 4 ∨
        (Q d.radical a).relIndex (V d.radical a') = 8) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := critical_index_two_of_small_opposite_radius s hc hb p hsmall
  have hi' := (small_critical_indices s hc p (by omega)).2
  have hl := (critical_radius_indices_gt_seed s hc hb p).2
  have hVQ := V_le_Q d.radical p.end_color hb
  let := finite_stabilizer d.radical a'
  let : Finite (V d.radical a') := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  obtain ⟨n,hn⟩ := ((Q_isPGroup d.radical (replacement_radical_isPGroup h d)
    (replacement_core_le_radical h d) a' p.end_color).to_le hVQ).index
      ((Q d.radical a).subgroupOf (V d.radical a'))
  change (Q d.radical a).relIndex (V d.radical a') = 2^n at hn
  have hnlo : 2 ≤ n := by
    by_contra! hh
    interval_cases n <;> simp_all
  have hnhi : n ≤ 3 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hh
    omega
  refine ⟨hi,hi',?_⟩
  have hn23 : n = 2 ∨ n = 3 := by omega
  rcases hn23 with rfl | rfl <;> simp_all

/-- In the negation of source (5.11)(1), the actual opposite radius has
index exactly four and both critical seeds have index two. -/
theorem small_opposite_radius_eq_four_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a).relIndex (V d.radical a') ≤ 4) :
    (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
      (Q d.radical a).relIndex (Z d.radical a') = 2 ∧
      (Q d.radical a).relIndex (V d.radical a') = 4 := by
  obtain ⟨hi,hi',hr⟩ := small_opposite_radius_four_or_eight_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p (by omega)
  exact ⟨hi,hi',by omega⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
