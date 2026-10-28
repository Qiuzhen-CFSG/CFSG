module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedLarge
public import Theory.GroupTheory.Commutator.IndexTwoSaturation

/-!
# Whole-radius lines in the mixed-plane terminal argument

For a critical walk from a to a', put c = a' - 2. The predecessor-radius
theorem already gives |V_c : V_c intersect Q_a| = 2. Reverse the actual
strict backward critical walk, retaining its vertex at position two.
The same theorem then gives the opposite index |V_a : V_a intersect Q_c| = 2
and identifies [V_a,Z_c] with its full critical commutator.

This intrinsic line has order two, lies in Z_a intersect Z_c, and is
noncentral in the stabilizer of c. The first containment uses the mixed
group's quadratic three-pair action on the actual natural graph. It does
not replace a whole core by a selected span.

Every eligible critical seed within radius two of a crosses the same
index-two kernel in V_a, so its commutator with Z_c is this same line.
Full-cover kernel rigidity makes its kernel in Z_c independent of the
backward choice, including every central attachment. The terminal-path
consumer identifies that kernel with C_(Z_c)(V_a), and proves that the
actual first-edge relative normalizer at each backward seed fixes the line.

The proofs apply at every original component vertex, retain both covers
of orders sixteen and thirty-two, and use the literal minimum characteristic
replacement, quotient and inverse-conjugation graph maps. No full point-core
equation or identification with the exceptional cubic graph is used.
Noncentrality at c is not asserted at a. The mixed-plane terminal
contradiction, larger original-Sylow branches, distance four and the
unconditional distance-two conclusion remain necessary.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the overlapping critical paths and radius-kernel comparisons in
(5.10)--(5.11), printed pp.922--924. This module establishes the stated
mixed-image radius data, not the full conclusions of those source lemmas.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedRadius
local notation "S" => Equiv.Perm (Fin 6)
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem reversed_radius_data
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a c z : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) z c)
    (hq2 : q.walk.getVert 2 = a) :
    (Q d.radical c).relIndex (V d.radical a) = 2 ∧
      Q d.radical c ⊔ V d.radical a = Q d.radical c ⊔ Z d.radical z ∧
      ⁅V d.radical a,Z d.radical c⁆ = ⁅Z d.radical z,Z d.radical c⁆ ∧
      Z d.radical c ⊓ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) =
        Z d.radical c ⊓ Q d.radical z := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let rev : CriticalPath d.radical (replacementGeometry h d) c z :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc q⟩
  have hl : 2 < q.walk.length := q.length_eq_b ▸ (show 2 < replacementDistance h d by omega)
  have he : rev.walk.getVert (rev.walk.length-2) = a := by
    dsimp only [rev]
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse]
    rw [show q.walk.length-(q.walk.length-2)=2 by omega,hq2]
  have hd := MixedLarge.mixed_predecessor_radius_data_knownSimple hb u him rev
  dsimp only at hd
  rw [he] at hd
  refine ⟨hd.1,hd.2.1,?_,hd.2.2.2⟩
  exact (commutator_comm _ _).trans (hd.2.2.1.trans (commutator_comm _ _))

private theorem radius_line_base
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    let c := p.walk.getVert (p.walk.length-2)
    let D := ⁅V d.radical (alpha d.radical),Z d.radical c⁆
    (Q d.radical c).relIndex (V d.radical (alpha d.radical)) = 2 ∧
      Nat.card D = 2 ∧
      D ≤ Z d.radical (alpha d.radical) ⊓ Z d.radical c ∧
      ¬ D ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨t,hat,hgen,x,hx,hxt,k,hk,q,hq1,hover,hidx,hstrict⟩ :=
    MixedLarge.mixed_backward_path_of_four_lt_knownSimple hb u him p
  have hq2 : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hr := reversed_radius_data hb u him q hq2
  have hi := MixedLarge.mixed_critical_indices_two_knownSimple hb u him q
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono plus_le_D
  have hline : ⁅Z d.radical (act d.radical k (act d.radical x (p.walk.getVert 2))),
      Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤ Z d.radical t := by
    simpa only [hq1] using cube_critical_commutator_le_first_seed s hc u hR q
  have hend : ⁅Z d.radical (act d.radical k (act d.radical x (p.walk.getVert 2))),
      Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      Z d.radical (p.walk.getVert (p.walk.length-2)) :=
    ((critical_Z_commutator_le_moving (h := h) q).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  dsimp only
  refine ⟨hr.1,?_,?_,?_⟩
  · rw [hr.2.2.1]
    exact hi.2.2
  · rw [hr.2.2.1]
    exact le_inf (hline.trans (adjacent_Z_le d.radical rfl hat)) hend
  · let rev := CriticalPath.ofPair (geometry := replacementGeometry h d) q.end_color
      (critical_reverse_pair s hc q)
    rw [hr.2.2.1,commutator_comm]
    exact critical_commutator_not_central s hc rev


/-- Every mixed-plane critical walk determines an intrinsic order-two line:
the commutator of the entire starting radius with the predecessor seed.
The opposite radius index is two, and the line lies in both full seeds and
is noncentral at the predecessor. -/
theorem mixed_opposite_radius_line_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    let c := p.walk.getVert (p.walk.length-2)
    let D := ⁅V d.radical a,Z d.radical c⁆
    (Q d.radical c).relIndex (V d.radical a) = 2 ∧
      Nat.card D = 2 ∧
      D ≤ Z d.radical a ⊓ Z d.radical c ∧
      ¬ D ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hga,act_mVertex,mul_inv_cancel]
    rfl
  have base := radius_line_base hb u him (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  have hd := base (p.act g⁻¹)
  dsimp only [CriticalPath.act] at hd
  simp only [actWalk_length,actWalk_getVert] at hd
  let c := p.walk.getVert (p.walk.length-2)
  let D := ⁅V d.radical a,Z d.radical c⁆
  let f := (MulAut.conj g).toMonoidHom
  have hD : ⁅V d.radical (act d.radical g⁻¹ a),
      Z d.radical (act d.radical g⁻¹ c)⁆ = D.map f := by
    rw [V_act,Z_act,inv_inv,←map_commutator]
  have hi := hd.1
  rw [Q_act,V_act,inv_inv,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  have hcard := hd.2.1
  change Nat.card (⁅V d.radical (act d.radical g⁻¹ a),
    Z d.radical (act d.radical g⁻¹ c)⁆ : Subgroup (FreeAmalgam d.radical)) = 2 at hcard
  rw [hD,card_map_of_injective (MulAut.conj g).injective] at hcard
  have hle := hd.2.2.1
  change ⁅V d.radical (act d.radical g⁻¹ a),
      Z d.radical (act d.radical g⁻¹ c)⁆ ≤
    Z d.radical (act d.radical g⁻¹ a) ⊓ Z d.radical (act d.radical g⁻¹ c) at hle
  rw [hD,Z_act,Z_act,inv_inv,←Subgroup.map_inf _ _ _ (MulAut.conj g).injective] at hle
  have hle' : D ≤ Z d.radical a ⊓ Z d.radical c :=
    (map_le_map_iff_of_injective (MulAut.conj g).injective).mp hle
  dsimp only
  refine ⟨hi,hcard,hle',?_⟩
  intro hcentral
  apply hd.2.2.2
  change ⁅V d.radical (act d.radical g⁻¹ a),
      Z d.radical (act d.radical g⁻¹ c)⁆ ≤
    centralizer (stabilizer d.radical (act d.radical g⁻¹ c) : Set (FreeAmalgam d.radical))
  rw [hD,stabilizer_act,inv_inv]
  exact (map_mono (f := f) hcentral).trans (map_centralizer_le_centralizer_image _ _)


/-- Every critical seed within radius two of the original start gives the
same commutator with its predecessor seed as the whole starting radius.
Thus the terminal line is independent of the backward selection. -/
theorem mixed_near_seed_radius_commutator_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) z
      (p.walk.getVert (p.walk.length-2)))
    (hnear : (cosetGraph d.radical).dist z a ≤ 2) :
    ⁅V d.radical a,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ =
      ⁅Z d.radical z,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ := by
  let c := p.walk.getVert (p.walk.length-2)
  let W := V d.radical a
  have hi := (mixed_opposite_radius_line_knownSimple hb u him p).1
  have hZ : Z d.radical z ≤ W := le_iSup_of_le z (le_iSup_of_le hnear le_rfl)
  have hWG : W ≤ stabilizer d.radical c := by
    apply (V_le_iff d.radical p.start_color _).mpr
    intro v hv hva
    apply Z_le_stabilizer_of_dist_le v _
    rw [(replacementGeometry h d).distance_constant v hv]
    have hac : (cosetGraph d.radical).dist a c = p.walk.length-2 :=
      p.dist_start (Nat.sub_le _ _)
    have ht := (cosetGraph_connected d.radical).dist_triangle (u := v) (v := a) (w := c)
    have hl : p.walk.length=replacementDistance h d := p.length_eq_b
    change _ ≤ replacementDistance h d
    omega
  have hQ : Q d.radical c ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical c q.end_color))
  exact commutator_eq_of_centralizing_index_two (Z d.radical c) (W ⊓ Q d.radical c) W
    (Z d.radical z) (hWG.trans (Z_normalized d.radical c)) inf_le_left
    (inf_le_right.trans hQ) (by simpa only [inf_relIndex_left] using hi)
    hZ (fun he => q.critical.2 (he.trans inf_le_right))

/-- All eligible backward critical seeds give the same full kernel in the
predecessor seed, including its central attachment. -/
theorem mixed_near_seed_kernels_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' z w : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) z
      (p.walk.getVert (p.walk.length-2)))
    (r : CriticalPath d.radical (replacementGeometry h d) w
      (p.walk.getVert (p.walk.length-2)))
    (hznear : (cosetGraph d.radical).dist z a ≤ 2)
    (hw : (cosetGraph d.radical).dist w a ≤ 2) :
    Z d.radical (p.walk.getVert (p.walk.length-2)) ⊓ Q d.radical z =
      Z d.radical (p.walk.getVert (p.walk.length-2)) ⊓ Q d.radical w := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let qr := CriticalPath.ofPair (geometry := replacementGeometry h d) q.end_color
    (critical_reverse_pair s hc q)
  let rr := CriticalPath.ofPair (geometry := replacementGeometry h d) r.end_color
    (critical_reverse_pair s hc r)
  have hq : (Q d.radical z).relIndex
      (Z d.radical (p.walk.getVert (p.walk.length-2))) < 4 := by
    rw [(MixedLarge.mixed_critical_indices_two_knownSimple hb u him q).2.1]
    decide
  have hr : (Q d.radical w).relIndex
      (Z d.radical (p.walk.getVert (p.walk.length-2))) < 4 := by
    rw [(MixedLarge.mixed_critical_indices_two_knownSimple hb u him r).2.1]
    decide
  apply small_critical_equal_commutators_kernel s hc qr rr hq hr
  exact (commutator_comm _ _).trans
    (((mixed_near_seed_radius_commutator_knownSimple hb u him p q hznear).symm.trans
      (mixed_near_seed_radius_commutator_knownSimple hb u him p r hw)).trans
        (commutator_comm _ _))


private theorem exists_backward_overlap
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) z
      (p.walk.getVert (p.walk.length-2)), q.walk.getVert 2 = a := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hga,act_mVertex,mul_inv_cancel]
    rfl
  have base := MixedLarge.mixed_backward_path_of_four_lt_knownSimple
    hb u him (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  obtain ⟨t,hat,hgen,x,hx,hxt,k,hk,q,hq1,hover,hidx,hstrict⟩ := base (p.act g⁻¹)
  have hq2 : q.walk.getVert 2 = act d.radical g⁻¹ a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hcancel (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hqc : ∃ r : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g (act d.radical k (act d.radical x ((p.act g⁻¹).walk.getVert 2))))
      (act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2))),
      r.walk.getVert 2 = a := by
    refine ⟨q.act g,?_⟩
    change (actWalk d.radical g q.walk).getVert 2 = a
    rw [actWalk_getVert,hq2,hcancel]
  have hend : act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2)) =
      p.walk.getVert (p.walk.length-2) := by
    change act d.radical g ((actWalk d.radical g⁻¹ p.walk).getVert
      ((actWalk d.radical g⁻¹ p.walk).length-2)) = _
    rw [actWalk_length,actWalk_getVert,hcancel]
  rw [hend] at hqc
  exact ⟨_,hqc⟩

/-- The mixed-plane terminal path has both whole-radius indices two. Its
intrinsic predecessor line has order two, lies in both full seeds and is
noncentral at the predecessor. Every eligible backward seed gives the same
full predecessor kernel, and its actual first-edge relative normalizer fixes
this intrinsic line. All backward choices and radius-index premises are
discharged on the original graph. -/
theorem mixed_radius_terminal_data_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    let c := p.walk.getVert (p.walk.length-2)
    let D := ⁅V d.radical a,Z d.radical c⁆
    (Q d.radical a).relIndex (V d.radical c) = 2 ∧
      (Q d.radical c).relIndex (V d.radical a) = 2 ∧
      Nat.card D = 2 ∧
      D ≤ Z d.radical a ⊓ Z d.radical c ∧
      (¬ D ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))) ∧
      ∀ z (q : CriticalPath d.radical (replacementGeometry h d) z c),
        (cosetGraph d.radical).dist z a ≤ 2 →
        Z d.radical c ⊓ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) =
          Z d.radical c ⊓ Q d.radical z ∧
        D ≤ centralizer (normalizer (Q d.radical (q.walk.getVert 1) :
          Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical z :
            Set (FreeAmalgam d.radical)) := by
  have hdata := mixed_opposite_radius_line_knownSimple hb u him p
  have hpdata := MixedLarge.mixed_predecessor_radius_data_knownSimple hb u him p
  obtain ⟨w,r,hr2⟩ := exists_backward_overlap hb u him p
  have hrnear : (cosetGraph d.radical).dist w a ≤ 2 := by
    rw [←hr2,r.dist_start (by
      have hl : r.walk.length=replacementDistance h d := r.length_eq_b
      omega)]
  have hrdata := reversed_radius_data hb u him r hr2
  refine ⟨hpdata.1,hdata.1,hdata.2.1,hdata.2.2.1,hdata.2.2.2,?_⟩
  intro z q hnear
  refine ⟨hrdata.2.2.2.trans
    (mixed_near_seed_kernels_knownSimple hb u him p r q hrnear hnear),?_⟩
  rw [mixed_near_seed_radius_commutator_knownSimple hb u him p q hnear]
  exact (SylowNormalizer.mixed_small_critical_relative_control_knownSimple
    (by omega) u him q (by
      rw [(MixedLarge.mixed_critical_indices_two_knownSimple hb u him q).1]
      decide)).1

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedRadius
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
