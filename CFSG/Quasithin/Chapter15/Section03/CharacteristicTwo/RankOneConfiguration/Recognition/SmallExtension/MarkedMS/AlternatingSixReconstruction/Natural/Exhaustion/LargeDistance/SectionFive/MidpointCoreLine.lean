module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardAttachment
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardCore

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ConsecutiveSlices

/-!
# Midpoint core lines and consecutive slices

At critical distance four with the literal full point-core image, a large
forward slice produces a nonzero backward-kernel commutator. The existing
order bound identifies it with the commutator of the full reverse critical
kernel with the whole midpoint two-core. This line is fixed by the starting
stabilizer and lies in the starting seed and the last edge seed.

The line cannot be central at the critical endpoint. Indeed, central
movement of a fixed hyperplane vanishes on the faithful natural quotient.
The quotient hyperplane's pointwise fixer has order two, forcing the actor
back into the original critical image and making its full-cover movement
trivial. This keeps the actual order-32 central attachment.

If the critical endpoints are conjugate under the midpoint stabilizer, a
small predecessor slice makes that same line central at the midpoint.
Transport would then make it central at the endpoint, a contradiction. The
small-forward-slice case uses the existing full-seed terminal theorem.
Consequently every such path has a large predecessor slice. Applying this
to the reciprocal path constructed from a nonabelian selected span proves
that its forward slice is large. In particular two consecutive small slices
are impossible on one critical path, without a supplied midpoint conjugator.

This completes the contradiction for that selection, not its existence.
Selecting the two small slices, other radical-image exclusions and the
unconditional distance-two theorem remain with the large-distance owner.
No selected-span bound is substituted for a whole residual-core bound.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3), (3.10) and (5.12)(1)--(3), printed pp.866--867,879--881,
924--927. Uses the original characteristic replacement and graph, with both
order-sixteen and order-thirty-two covers and the nonsylow original radical.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


include s in
/-- A small actor's fixed hyperplane cannot acquire a nonzero central
commutator. The faithful natural quotient detects the pointwise fixer. -/
theorem cover_fixed_central_commutator_eq_bot
    (A B : Subgroup d.overgroup) (hAB : A ≤ B)
    (hne : ¬ A ≤ pCore 2 d.overgroup)
    (hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2)
    (hcomm : ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),B⁆ ≤
      center d.overgroup) :
    ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),B⁆ = ⊥ := by
  let := replacementMoved_normal h d
  let π := coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)
  let F := fixedSpace (coverAction s) (A.map s.projection)
  let T := fixedSpace (naturalRepresentation (Fin 6)) (B.map s.projection)
  have hfix : F ≤ T.comap π := by
    intro v hv b
    obtain ⟨x,hx,hxb⟩ := b.property
    have hva : (v.toMul : d.overgroup) ∈ centralizer (A : Set d.overgroup) :=
      (NormalElementaryQuotient.mem_fixedSpace_image (replacementMoved d)
        s.projection s.surjective (s.projection_kernel.trans (moved_centralizer s).symm) A v).mp hv
    let z : replacementMoved d := MulAut.conjNormal x v.toMul * v.toMul⁻¹
    have hzC : (z : d.overgroup) ∈ center d.overgroup := by
      apply hcomm
      rw [commutator_comm]
      exact commutator_mem_commutator hx ⟨v.toMul.property,hva⟩
    have hz0 : coverProjection h e hz hn d z = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [coverProjection_kernel_center s]
      exact hzC
    have hzEq : (coverProjection h e hz hn d z).toAdd =
        naturalRepresentation (Fin 6) (s.projection x) (π v) - π v := by
      change (coverProjection h e hz hn d (MulAut.conjNormal x v.toMul * v.toMul⁻¹)).toAdd = _
      rw [map_mul,map_inv]
      simp only [toAdd_mul,toAdd_inv,sub_eq_add_neg]
      rw [s.cover_conjugate x v.toMul (MulAut.conjNormal x v.toMul) rfl]
      rfl
    change naturalRepresentation (Fin 6) b (π v) = π v
    rw [hz0] at hzEq
    rw [←hxb]
    exact sub_eq_zero.mp hzEq.symm
  let q := F.mapQ T π hfix
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨w,rfl⟩ := T.mkQ_surjective v
    obtain ⟨v,rfl⟩ := coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d) w
    exact ⟨F.mkQ v,rfl⟩
  have hsmall : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (B.map s.projection) ≤ 1 :=
    (LinearMap.finrank_le_finrank_of_surjective hq).trans hsmall
  have hnA : A.map s.projection ≠ ⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff A).mp he)
  have hnB : B.map s.projection ≠ ⊥ := by
    intro he
    exact hnA (le_bot_iff.mp ((map_mono hAB).trans_eq he))
  obtain ⟨t,_,ht,hBt⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers
    (B.map s.projection) hnB hnat
  have hcard : Nat.card (B.map s.projection) = 2 := by
    rw [hBt,Nat.card_zpowers,ht.orderOf]
  have hlo := (one_lt_card_iff_ne_bot (A.map s.projection)).mpr hnA
  have heq : A.map s.projection = B.map s.projection :=
    eq_of_le_of_card_ge (map_mono hAB) (by omega)
  have hB : B ≤ pCore 2 d.overgroup ⊔ A := by
    have hh := le_comap_map s.projection B
    rw [←heq,Subgroup.comap_map_eq,s.projection_kernel] at hh
    exact hh.trans_eq (sup_comm _ _)
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  exact hB.trans (sup_le
    ((moved_centralizer s).ge.trans (centralizer_le inf_le_left))
    (le_centralizer_iff.mpr inf_le_right))

include s in
/-- A nonzero reverse-kernel commutator with the midpoint core is
noncentral at the endpoint, including on the augmentation cover. -/
theorem four_kernel_core_noncentral
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hne : ⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical (p.walk.getVert 2)⁆ ≠ ⊥) :
    ¬ ⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical (p.walk.getVert 2)⁆ ≤
      centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) := by
  intro hcentral
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let c := p.walk.getVert 2
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hdist : (cosetGraph d.radical).dist c a' = 2 := by rw [p.dist_end,hl]
  have hQG : Q d.radical c ≤ stabilizer d.radical a' :=
    Q_le_stabilizer_of_dist_two d.radical c a' hcol hdist
  have hZaQ : Z d.radical a ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact hb2
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a' p.end_color
  let A := (Z d.radical a).comap i
  let B := (Q d.radical c).comap i
  have hmA : A.map i = Z d.radical a :=
    map_comap_eq_self ((hZaQ.trans hQG).trans_eq hir.symm)
  have hmB : B.map i = Q d.radical c := map_comap_eq_self (hQG.trans_eq hir.symm)
  have hAB : A ≤ B := comap_mono hZaQ
  have hnA : ¬ A ≤ pCore 2 d.overgroup := by
    intro hh
    have he := map_mono (f := i) hh
    rw [hmA,hiQ] at he
    exact p.critical.2 he
  have hfix : U d.radical a' ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical a' ⊓ Q d.radical a := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←C_eq_Q s hc a p.start_color]
      exact ⟨critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
        (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
            exact replacementDistance_pos h d) p.critical
          (DistanceEight.U_le_Z d.radical a' hx.1),hx.2⟩
    · exact inf_le_inf_left _ (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a p.start_color)))
  have hmF : (replacementMoved d ⊓ centralizer (A : Set d.overgroup)).map i =
      U d.radical a' ⊓ Q d.radical a := by
    rw [←map_inf_centralizer_of_injective i hi,hiU,hmA,hfix]
  have hcF : ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),B⁆ ≤ center d.overgroup := by
    intro x hx
    apply mem_center_iff.mpr
    intro m
    apply hi
    simp only [map_mul]
    apply hcentral
    · have hh := mem_map_of_mem i hx
      rw [map_commutator,hmF,hmB] at hh
      exact commutator_mono (inf_le_inf_right _ (DistanceEight.U_le_Z d.radical a')) le_rfl hh
    · rw [←hir]
      exact ⟨m,rfl⟩
  let := finite_Z d.radical a'
  let : Finite (U d.radical a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a')) (inclusion_injective _)
  have hidx : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,hmF,hiU,
      inf_relIndex_left]
    exact (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a')
      index_ne_zero_of_finite).trans_eq (small_critical_indices s hc p hsmall).2
  have hz := congrArg (Subgroup.map i) (cover_fixed_central_commutator_eq_bot s A B hAB hnA hidx hcF)
  rw [map_commutator,hmF,hmB,Subgroup.map_bot] at hz
  have hm := (critical_kernel_predecessor_moving s hc hb2 p).2.2 (Q d.radical c)
    (by simp only [hl,Nat.reduceSub]; exact le_rfl)
  exact hne (hm.trans hz)


/-- The backward line is the whole midpoint two-core commutator, fixed by
the starting stabilizer. The backward path is constructed from the large slice. -/
theorem full_point_four_large_slice_core_line_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
    let H := ⁅K,Q d.radical (p.walk.getVert 2)⁆
    Nat.card H = 2 ∧
      H ≤ Z d.radical (alpha d.radical) ∧
      H ≤ Z d.radical (p.walk.getVert 3) ∧
      H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,hgen,g,hg,hgt,q,hq1,hover,hlargeq⟩ :=
    full_point_backward_shift_knownSimple hb2 u hfull p hdelta hlarge
  have he : p.walk.getVert (p.walk.length-2) = p.walk.getVert 2 := by rw [hl]
  let q' : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g (p.walk.getVert 2)) (p.walk.getVert 2) := {
    start_color := q.start_color
    walk := q.walk.copy rfl he
    shortest := by rw [SimpleGraph.Walk.length_copy,q.shortest,he]
    critical := by simpa only [he] using q.critical }
  have hq1' : q'.walk.getVert 1 = t := by
    change (q.walk.copy rfl he).getVert 1 = t
    rwa [SimpleGraph.Walk.getVert_copy]
  have hq2' : q'.walk.getVert 2 = alpha d.radical := by
    change (q.walk.copy rfl he).getVert 2 = _
    rw [SimpleGraph.Walk.getVert_copy]
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hline := backward_kernel_attachment s hc hb u hf p q' hat hq1' hq2' hgen hlargeq
  let A := Z d.radical (act d.radical g (p.walk.getVert 2)) ⊓
    Q d.radical (p.walk.getVert 2)
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let H := ⁅K,Q d.radical (p.walk.getVert 2)⁆
  let J := ⁅A,K⁆
  have hi := (full_point_four_critical_indices_two_knownSimple hb u hfull p).1
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  have hbound := small_critical_kernel_predecessor_card s hc hb2 u hf.le p hsmall
  have hlast := small_critical_predecessor_commutator_le_last_seed s hc hb2 u hf.le p hsmall
  rw [hl] at hbound hlast
  change Nat.card H ≤ 2 at hbound
  change H ≤ Z d.radical (p.walk.getVert 3) at hlast
  have hJH : J ≤ H := by
    dsimp only [J,H]
    rw [commutator_comm A K]
    exact commutator_mono le_rfl inf_le_right
  let := finite_Z d.radical (p.walk.getVert 3)
  let : Finite H := Finite.of_injective (inclusion hlast) (inclusion_injective _)
  have heq : J = H := eq_of_le_of_card_ge hJH (hbound.trans_eq hline.1.symm)
  change Nat.card H = 2 ∧ H ≤ Z d.radical (alpha d.radical) ∧
    H ≤ Z d.radical (p.walk.getVert 3) ∧ H ≤ centralizer
      (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))
  refine ⟨?_,?_,hlast,?_⟩
  · rw [←heq]; exact hline.1
  · rw [←heq]; exact hline.2.1.trans (adjacent_Z_le d.radical rfl hat)
  · rw [←heq]; exact hline.2.2.1

/-- Every critical path whose endpoints are conjugate under its midpoint
has a large predecessor slice. No forward-slice assumption is required. -/
theorem midpoint_conjugate_predecessor_large_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (hge : act d.radical g (alpha d.radical) = a') :
    2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') := by
  by_contra! hpre
  by_cases hf : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2
  · exact selected_terminal_false_of_full_seed_slices_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p
      (small_predecessor_selected_span_nonabelian_knownSimple hb u hfull p hpre) hf g hg hge hpre
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  let H := ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Q d.radical (p.walk.getVert 2)⁆
  have hline := full_point_four_large_slice_core_line_knownSimple hb u hfull p (by omega)
  have hcentral := (predecessor_slice_kernel_core_commutator s hc hb u hfull'.le p hpre).2.2.2
  have hmap : H.map (MulAut.conj g⁻¹).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hcentral ((stabilizer d.radical (p.walk.getVert 2)).inv_mem hg)))
  have hend : H ≤ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) := by
    have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hline.2.2.2).trans
      (map_centralizer_le_centralizer_image _ _)
    change H.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer
      ((stabilizer d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom :
        Set (FreeAmalgam d.radical)) at hh
    rwa [hmap,←stabilizer_act,hge] at hh
  have hi := (full_point_four_critical_indices_two_knownSimple hb u hfull p).1
  apply four_kernel_core_noncentral s hc hb p (by omega) ?_ hend
  intro he
  have hh := hline.1
  rw [he,card_bot] at hh
  omega

/-- Transport the midpoint-conjugate bound on the original graph, retaining
one conjugator and the same critical walk. -/
theorem midpoint_conjugate_predecessor_large_at_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (hge : act d.radical g a = a') :
    2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  obtain ⟨x,hx⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical x⁻¹ a = alpha d.radical := by
    rw [hx,act_mVertex,mul_inv_cancel]
    rfl
  have hrestore (v : Vertex d.radical) : act d.radical x (act d.radical x⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  let k := x*g*x⁻¹
  have hk : k ∈ stabilizer d.radical ((p.act x⁻¹).walk.getVert 2) := by
    change k ∈ stabilizer d.radical ((actWalk d.radical x⁻¹ p.walk).getVert 2)
    rw [actWalk_getVert,stabilizer_act]
    refine ⟨g,hg,?_⟩
    change (x⁻¹)⁻¹*g*((x⁻¹)⁻¹)⁻¹ = k
    simp only [inv_inv,k]
  have hke : act d.radical k (act d.radical x⁻¹ a) = act d.radical x⁻¹ a' := by
    dsimp only [k]
    rw [act_mul,act_mul,hrestore,hge]
  have base := midpoint_conjugate_predecessor_large_knownSimple hb u hfull
    (a' := act d.radical x⁻¹ a')
  rw [←hbase] at base
  have hh := base (p.act x⁻¹) k hk hke
  change 2 < (B d.radical ((actWalk d.radical x⁻¹ p.walk).getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical x⁻¹ a')) at hh
  rw [actWalk_getVert,Escape.PairingControl.FirstPairing.B_act hb2 x⁻¹ _ hcol,
    U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective] at hh
  exact hh

/-- A nonabelian selected span forces its forward slice to be large.
The reciprocal path and midpoint conjugator are constructed from that span. -/
theorem nonabelian_selected_span_forward_large_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥) :
    2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨_,x,hx,q,_,hq,_⟩ := selected_span_conjugate_critical_path (h := h) hb2 p hnon
  have hh := midpoint_conjugate_predecessor_large_at_knownSimple hb u hfull q x
    (hq.symm ▸ hx) rfl
  rw [hq] at hh
  have hBm : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      (geometry := replacementGeometry h d) hb2 (alpha d.radical) rfl
      ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  rw [U_act,←hBm,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective] at hh
  exact hh

/-- Two consecutive small slices are impossible on the same literal
critical path, without an independently chosen midpoint conjugator. -/
theorem consecutive_small_slices_false_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hpredecessor : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) : False := by
  exact (Nat.not_lt_of_ge hforward) (nonabelian_selected_span_forward_large_knownSimple hb u hfull p
    (small_predecessor_selected_span_nonabelian_knownSimple hb u hfull p hpredecessor))

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
