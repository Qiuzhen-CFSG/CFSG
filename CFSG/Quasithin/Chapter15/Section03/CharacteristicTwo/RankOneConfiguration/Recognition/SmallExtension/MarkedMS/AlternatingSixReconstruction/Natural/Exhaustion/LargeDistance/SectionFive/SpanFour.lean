module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.RadiusFour

/-!
# Derived subgroups of selected spans at distance four

Assume that the original radical has the full marked point-core image.
The radius-four commutator identity transports to every critical path in
its actual amalgam graph. For a selected backward path through the original
vertex, reversing that same walk identifies the entire midpoint-radius
commutator with the selected critical line. This line is fixed by the
starting stabilizer. Normal generation of the original forward seed then
identifies the selected span's commutator with the radius, and its derived
subgroup, with that same line of order two.

A forward slice larger than two supplies this backward path through the
existing source selection, retaining its conjugator and common vertices.
Combining this with the proved small-slice calculation shows that every
selected span at distance four has derived subgroup of order at most two,
fixed by its starting stabilizer. Both the order-sixteen natural cover and
the order-thirty-two augmentation cover remain intact.

The natural-quotient consumer now retains only nonabelianness and the
endpoint commutator estimate; the large-slice branch supplies nonabelianness
as well. The literal chosen-replacement distance-two application discharges
critical smallness, selected index and derived-fixedness in the existing
terminal argument. Its nonabelianness, endpoint movement, opposite-core
estimates and full point-core equality remain explicit. The small-image
distance-four contradiction and the other radical-image branches are still
obligations of the large-distance assembly owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.8) and (5.12), printed pp.919--920 and 924--927, especially the
selected derived-subgroup step on p.927. The proof uses the original-cover
RadiusFour, SelectedFour and FullSeed results, not the native moving
subgroup's stronger zero-fixed-line hypothesis.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


/-- The midpoint commutator identity on every critical path. -/
theorem four_midpoint_radius_commutator_at
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (u : S) (hfull : d.radical.map s.projection =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ⁅Z d.radical a,V d.radical (p.walk.getVert 2)⁆ =
      ⁅Z d.radical a,Z d.radical a'⁆ := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := four_midpoint_radius_commutator_eq_critical s hc hb u hfull
    (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  have he := base (p.act g⁻¹)
  change ⁅Z d.radical (act d.radical g⁻¹ a),
      V d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2)⁆ =
    ⁅Z d.radical (act d.radical g⁻¹ a),Z d.radical (act d.radical g⁻¹ a')⁆ at he
  rw [actWalk_getVert,Z_act,Z_act,V_act,←map_commutator,←map_commutator] at he
  exact (Subgroup.map_injective (MulAut.conj (g⁻¹)⁻¹).injective) he

/-- A selected backward critical line controls the whole orbit span's
commutator with the radius, and is its exact derived subgroup. -/
theorem four_selected_span_derived
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (u : S) (hfull : d.radical.map s.projection =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (alpha d.radical))
    (q : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g (p.walk.getVert 2)) (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = alpha d.radical)
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical a' =
      stabilizer d.radical (alpha d.radical)) :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    let D := ⁅Z d.radical (act d.radical g (p.walk.getVert 2)),Z d.radical (p.walk.getVert 2)⁆
    ⁅P,V d.radical (alpha d.radical)⁆ = D ∧ ⁅P,P⁆ = D ∧
      Nat.card D = 2 ∧
      D ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  let D := ⁅Z d.radical (act d.radical g c),Z d.radical c⁆
  let V₀ := V d.radical (alpha d.radical)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hb2 : 2 < replacementDistance h d := by omega
  have hca : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  have hPV : P ≤ V₀ := localZSpan_le_V d.radical hca
  have hVG : V₀ ≤ stabilizer d.radical (alpha d.radical) :=
    (replacementGeometry h d).V_local _ rfl hb2
  have hDC : D ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    selected_critical_commutator_central s hc u hfull.le hb2 q p
      (by simpa only [hq2] using (q.dist_start (i := 2) (by omega)).le)
      hca (by rw [p.dist_end,hl,hb]; decide) hgen
  have hDN : stabilizer d.radical (alpha d.radical) ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hDC).trans (Subgroup.centralizer_le_normalizer _)
  let r : CriticalPath d.radical (replacementGeometry h d) c (act d.radical g c) := {
    start_color := q.end_color
    walk := q.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc q }
  have hr2 : r.walk.getVert 2 = alpha d.radical := by
    change q.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,hql]
    exact hq2
  have hZV : ⁅Z d.radical c,V₀⁆ = D := by
    have he := four_midpoint_radius_commutator_at s hc hb u hfull r
    rw [hr2,commutator_comm (Z d.radical c) (Z d.radical (act d.radical g c))] at he
    exact he
  have hPVD : ⁅P,V₀⁆ ≤ D := by
    dsimp only [P]
    rw [localZSpan_eq_conjugates]
    apply commutator_iSup_le_of_relative_normal (stabilizer d.radical (alpha d.radical)) V₀ D _ hDN
    · intro k
      have hPG : P ≤ stabilizer d.radical (alpha d.radical) := hPV.trans hVG
      exact (le_iSup (fun j : stabilizer d.radical (alpha d.radical) =>
        (Z d.radical c).map (MulAut.conj (j : FreeAmalgam d.radical)⁻¹).toMonoidHom) k).trans
        (by rwa [←localZSpan_eq_conjugates])
    · intro k
      have he := congrArg (Subgroup.map (MulAut.conj (k : FreeAmalgam d.radical)⁻¹).toMonoidHom) hZV
      have hVm : V₀.map (MulAut.conj (k : FreeAmalgam d.radical)⁻¹).toMonoidHom = V₀ :=
        mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized d.radical _
          ((stabilizer d.radical (alpha d.radical)).inv_mem k.property))
      have hDm : D.map (MulAut.conj (k : FreeAmalgam d.radical)⁻¹).toMonoidHom = D :=
        mem_normalizer_iff_map_conj_eq.mp (hDN
          ((stabilizer d.radical (alpha d.radical)).inv_mem k.property))
      rw [map_commutator,hVm,hDm] at he
      exact he.le
  have hcP : Z d.radical c ≤ P := Z_le_localZSpan d.radical _ _
  have hgP : Z d.radical (act d.radical g c) ≤ P := by
    rw [Z_act]
    exact (map_mono hcP).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized d.radical _ _ ((stabilizer d.radical (alpha d.radical)).inv_mem hg)))
  have hDP : D ≤ ⁅P,P⁆ := commutator_mono hgP hcP
  have heP : ⁅P,P⁆ = D := le_antisymm ((commutator_mono le_rfl hPV).trans hPVD) hDP
  refine ⟨le_antisymm hPVD (hDP.trans (commutator_mono le_rfl hPV)),heP,?_,hDC⟩
  have hf : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hfull
  exact (full_point_four_critical_indices_two_at_knownSimple hb u hf q).2.2

/-- At distance four, a forward slice larger than two supplies a nonabelian
selected span with central derived subgroup of order two. -/
theorem full_point_four_large_slice_derived_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    ⁅P,V d.radical (alpha d.radical)⁆ = ⁅P,P⁆ ∧
      Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,_,hgen,g,hg,hgt,q,hq1,hover,_⟩ :=
    full_point_backward_shift_knownSimple hb2 u hfull p hdelta hlarge
  have he : p.walk.getVert (p.walk.length-2) = p.walk.getVert 2 := by rw [hl]
  let q' : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g (p.walk.getVert 2)) (p.walk.getVert 2) := {
    start_color := q.start_color
    walk := q.walk.copy rfl he
    shortest := by rw [SimpleGraph.Walk.length_copy,q.shortest,he]
    critical := by simpa only [he] using q.critical }
  have hq2 : q'.walk.getVert 2 = alpha d.radical := by
    change (q.walk.copy rfl he).getVert 2 = _
    rw [SimpleGraph.Walk.getVert_copy]
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hgen' : Q d.radical (q'.walk.getVert 1) ⊔ Z d.radical a' =
      stabilizer d.radical (alpha d.radical) := by
    change Q d.radical ((q.walk.copy rfl he).getVert 1) ⊔ Z d.radical a' = _
    rwa [SimpleGraph.Walk.getVert_copy,hq1]
  have hout := four_selected_span_derived s hc hb u hf p g hg q' hq2 hgen'
  exact ⟨hout.1.trans hout.2.1.symm,hout.2.1 ▸ hout.2.2.1,hout.2.1 ▸ hout.2.2.2⟩

/-- The large-slice branch supplies nonabelianness and fixed derived group
for the existing natural quotient construction. Only endpoint movement remains. -/
theorem selected_natural_quotient_of_full_point_four_large_slice_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    ∃ (E : ((forwardMovedSpan d.radical (p.walk.getVert 2)) ⧸
          center (forwardMovedSpan d.radical (p.walk.getVert 2))) ≃*
        Multiplicative (BinaryPermutation.natural (Fin 6)))
      (τ : S ≃* S),
      ∀ (m : d.overgroup) (x : forwardMovedSpan d.radical (p.walk.getVert 2)),
        (E (QuotientGroup.mk' _ (forwardMovedSpanAction d.radical (p.walk.getVert 2) m x))).toAdd =
          BinaryPermutation.naturalRepresentation (Fin 6)
            (τ (SourceReduction.projection h e hz hn d m))
            (E (QuotientGroup.mk' _ x)).toAdd := by
  have hd := full_point_four_large_slice_derived_knownSimple hb u hfull p hlarge
  have hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ := by
    intro he
    have hcard := hd.2.1
    rw [he,card_bot] at hcard
    omega
  exact selected_natural_quotient_of_full_point_four_estimates_knownSimple hb u hfull p
    hnon (hd.2.2.trans (centralizer_le (Ltilde_le_stabilizer _))) hcomm

/-- Every selected orbit span at distance four has a derived subgroup of
order at most two, fixed by its full starting stabilizer. -/
theorem full_point_four_selected_span_derived_bound_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  by_cases hzero : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ = ⊥
  · dsimp only
    rw [hzero,card_bot]
    exact ⟨by decide,bot_le⟩
  by_cases hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2
  · have hi := (full_point_four_critical_indices_two_knownSimple hb u hfull p).1
    have hd := small_selected_span_derived_knownSimple (e := e) (hz := hz) (hn := hn)
      (by omega : 2 < replacementDistance h d) p (by omega) hslice hzero
    exact ⟨hd.2.1.le,hd.2.2⟩
  · have hd := full_point_four_large_slice_derived_knownSimple hb u hfull p (Nat.lt_of_not_ge hslice)
    exact ⟨hd.2.1.le,hd.2.2⟩

/-- The derived bound is valid on the original graph at every starting
vertex, with the same transported critical path. -/
theorem full_point_four_selected_span_derived_bound_at_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    let P := localZSpan d.radical (p.walk.getVert 2) a
    Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := full_point_four_selected_span_derived_bound_knownSimple hb u hfull
    (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  have hd := base (p.act g⁻¹)
  change Nat.card (⁅localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2)
      (act d.radical g⁻¹ a),localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2)
      (act d.radical g⁻¹ a)⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
    ⁅localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2) (act d.radical g⁻¹ a),
      localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2) (act d.radical g⁻¹ a)⁆ ≤
        centralizer (stabilizer d.radical (act d.radical g⁻¹ a) : Set (FreeAmalgam d.radical)) at hd
  have hrestore (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hcard := hd.1
  rw [actWalk_getVert,LocalCommutator.CriticalCase.localZSpan_act,←map_commutator,
    card_map_of_injective (MulAut.conj (g⁻¹)⁻¹).injective] at hcard
  have hm := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hd.2).trans
    (map_centralizer_le_centralizer_image _ _)
  change (⁅localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2) (act d.radical g⁻¹ a),
      localZSpan d.radical ((actWalk d.radical g⁻¹ p.walk).getVert 2) (act d.radical g⁻¹ a)⁆ :
        Subgroup (FreeAmalgam d.radical)).map (MulAut.conj g⁻¹).toMonoidHom ≤
      centralizer ((stabilizer d.radical (act d.radical g⁻¹ a)).map (MulAut.conj g⁻¹).toMonoidHom :
        Set (FreeAmalgam d.radical)) at hm
  rw [actWalk_getVert,map_commutator,←LocalCommutator.CriticalCase.localZSpan_act,
    ←stabilizer_act,hrestore,hrestore] at hm
  exact ⟨hcard,hm⟩

/-- The full-point distance-four data discharge both the derived-fixedness
and index premises in the literal selected natural quotient construction. -/
theorem selected_natural_quotient_of_full_point_four_endpoint_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnonabelian : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    ∃ (E : ((forwardMovedSpan d.radical (p.walk.getVert 2)) ⧸
          center (forwardMovedSpan d.radical (p.walk.getVert 2))) ≃*
        Multiplicative (BinaryPermutation.natural (Fin 6)))
      (τ : S ≃* S),
      ∀ (m : d.overgroup) (x : forwardMovedSpan d.radical (p.walk.getVert 2)),
        (E (QuotientGroup.mk' _ (forwardMovedSpanAction d.radical (p.walk.getVert 2) m x))).toAdd =
          BinaryPermutation.naturalRepresentation (Fin 6)
            (τ (SourceReduction.projection h e hz hn d m))
            (E (QuotientGroup.mk' _ x)).toAdd := by
  have hd := full_point_four_selected_span_derived_bound_knownSimple hb u hfull p
  exact selected_natural_quotient_of_full_point_four_estimates_knownSimple hb u hfull p
    hnonabelian (hd.2.trans (centralizer_le (Ltilde_le_stabilizer _))) hcomm

/-- Literal chosen-replacement application. The preceding results remove
critical smallness, selected index and derived-fixedness from the terminal
premises. Nonabelianness, endpoint movement and opposite-core estimates
remain explicit source obligations. -/
theorem original_full_point_distance_two_of_selected_estimates_knownSimple
    (u : S)
    (hfull : (replacement h).radical.map
      (SourceReduction.projection h e hz hn (replacement h)) =
        pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex (replacement h).radical}
    (p : CriticalPath (replacement h).radical (replacementGeometry h (replacement h))
      (alpha (replacement h).radical) a')
    (hnonabelian : ⁅localZSpan (replacement h).radical (p.walk.getVert 2) (alpha (replacement h).radical),
      localZSpan (replacement h).radical (p.walk.getVert 2) (alpha (replacement h).radical)⁆ ≠ ⊥)
    (hcomm : ⁅localZSpan (replacement h).radical (p.walk.getVert 2) (alpha (replacement h).radical) ⊓
        Q (replacement h).radical (p.walk.getVert 2),Z (replacement h).radical a'⁆ ≤
      Z (replacement h).radical (alpha (replacement h).radical))
    (hCcard : Nat.card (⁅⁅Q (replacement h).radical (p.walk.getVert 2),Ltilde (replacement h).radical (p.walk.getVert 2)⁆,
      ⁅Q (replacement h).radical (p.walk.getVert 2),Ltilde (replacement h).radical (p.walk.getVert 2)⁆⁆ :
        Subgroup (FreeAmalgam (replacement h).radical)) ≤ 2)
    (hcross : ⁅localZSpan (replacement h).radical (p.walk.getVert 2) (alpha (replacement h).radical) ⊓
      Q (replacement h).radical (p.walk.getVert 2),
      ⁅Q (replacement h).radical (p.walk.getVert 2),Ltilde (replacement h).radical (p.walk.getVert 2)⁆⁆ ≤
      ⁅⁅Q (replacement h).radical (p.walk.getVert 2),Ltilde (replacement h).radical (p.walk.getVert 2)⁆,
        ⁅Q (replacement h).radical (p.walk.getVert 2),Ltilde (replacement h).radical (p.walk.getVert 2)⁆⁆) :
    replacementDistance h (replacement h) = 2 := by
  rcases full_point_distance_two_or_four_knownSimple u hfull with hb | hb
  · exact hb
  · have hi := (full_point_four_critical_indices_two_knownSimple hb u hfull p).1
    have hd := full_point_four_selected_span_derived_bound_knownSimple hb u hfull p
    exact (selected_natural_terminal_false_knownSimple (e := e) (hz := hz) (hn := hn)
      (by omega : 2 < replacementDistance h (replacement h)) p hnonabelian (by omega)
      (hd.2.trans (centralizer_le (Ltilde_le_stabilizer _)))
      (full_point_four_selected_span_index_knownSimple hb u hfull p) hcomm hCcard hcross).elim

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
