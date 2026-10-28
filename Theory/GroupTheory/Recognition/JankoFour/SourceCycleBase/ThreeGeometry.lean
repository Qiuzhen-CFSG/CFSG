module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.ThreePair
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.BridgeReduction
/-!
# The δ₃ plane-hitting argument

A checked native pair and the original orbital transitivity provide a common
δ₁ line. The actual point-core stabilizer gives a second common neighbor on
it. The line's three visible directions form a singular pencil; outside the
pencil, one of the two common neighbors sees all five points of the target
line. Its oval meets the pencil of a shared octad, yielding the required
coplanar step. Every chosen middle vertex stays in the original induced
common-neighbor component. This proves (7.4.2) without needing the separate
six-point disc classification for this particular conclusion.

Source: Aschbacher–Segev (1991), (3.10), (5.4), (7.3)–(7.4), pp.596,600,603–604.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open SimpleGraph Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

theorem delta_three_common_delta_one {u : Point d.P} {a b : Line d.L}
    (ht : LineType d.residue 3 u a b) :
    ∃ k, LineType d.residue 1 u a k ∧ LineType d.residue 1 u b k := by
  let e := d.residue.linesAt u
  let l := e.symm Native.FarPair.line
  let m := e.symm (Native.FarOrbit.seedLine 1)
  let k := e.symm (Native.FarOrbit.seedLine 3)
  have hlm : LineType d.residue 3 u l.val m.val := by
    apply d.residue.lineType_of_native_at u l m
    simpa only [l,m,e,Equiv.apply_symm_apply] using Native.ThreePair.delta_three
  have hlk : LineType d.residue 1 u l.val k.val := by
    apply d.residue.lineType_of_native_at u l k
    simpa only [l,k,e,Equiv.apply_symm_apply] using Native.ThreePair.common_delta_one.1
  have hmk : LineType d.residue 1 u m.val k.val := by
    apply d.residue.lineType_of_native_at u m k
    simpa only [m,k,e,Equiv.apply_symm_apply] using Native.ThreePair.common_delta_one.2
  obtain ⟨g,hgu,hgl,hgm⟩ := d.lineType_pair_transitive hlm ht
  exact ⟨g • k.val,by simpa only [hgu,hgl] using lineType_smul g hlk,
    by simpa only [hgu,hgm] using lineType_smul g hmk⟩

private theorem other_of_three {S : Set (Point d.P)} (hc : S.ncard = 3) (u : Point d.P) :
    ∃ v ∈ S, v ≠ u := by
  classical
  by_contra! hn
  have hs : S ⊆ {u} := fun v hv => hn v hv
  have hle := Set.ncard_le_ncard hs
  rw [hc,Set.ncard_singleton] at hle
  omega

/-- The core stabilizer in (5.4) supplies the second common neighbor on the
common δ₁ line in the proof of (7.4), not merely one intersecting point. -/
theorem delta_three_second_common {x u y : Point d.P} {a b k : Line d.L}
    (hxu : Adj d.L x u) (huy : Adj d.L u y)
    (hua : OnLine d.L u a) (hxa : OnLine d.L x a)
    (_hub : OnLine d.L u b) (hyb : OnLine d.L y b)
    (ht : LineType d.residue 3 u a b)
    (hak : LineType d.residue 1 u a k) (hbk : LineType d.residue 1 u b k) :
    ∃ v, OnLine d.L v k ∧ Adj d.L x v ∧ Adj d.L y v ∧ v ≠ u := by
  have huk := (lineType_incident hak).2
  obtain ⟨v,⟨hvk,hxv⟩,hvu⟩ := d.other_of_three
    (d.delta_one_neighbors u x a k hua hxa hxu.1 hak) u
  have hvbcard := d.delta_one_neighbors u v k b huk hvk hvu (d.lineType_symm hbk)
  obtain ⟨w,⟨hwb,hvw⟩,hwu⟩ := d.other_of_three hvbcard u
  obtain ⟨e,hex,hew⟩ := d.core_stabilizer_transitive u x a b 3 hua hxa hxu.1
    (by decide) ht w y hwb hwu hyb huy.1.symm
  have heu := d.core_fixes_point u e
  refine ⟨(e : G) • v,?_,?_,?_,?_⟩
  · simpa only [OnLine,d.core_fixes_lines u e k huk] using incident_smul (e : G) hvk
  · simpa only [hex] using adj_smul (e : G) hxv
  · simpa only [hew] using adj_smul (e : G) (adj_symm hvw)
  · intro he
    exact hvu ((MulAction.injective (e : G)) (he.trans heu.symm))

/-- Moving the middle vertex along that line retains the original δ₁
relation to the endpoint line, by the triangle-label identity (5.6). -/
theorem delta_one_at_common_on_line {u y v : Point d.P} {b k : Line d.L}
    (huy : Adj d.L u y) (hyv : Adj d.L y v)
    (hub : OnLine d.L u b) (hyb : OnLine d.L y b)
    (huk : OnLine d.L u k) (hvk : OnLine d.L v k)
    (hbk : LineType d.residue 1 u b k) :
    LineType d.residue 1 v (d.joiningLine hyv) k := by
  by_cases hvu : v = u
  · subst v
    have he := d.line_eq_of_incident hyv.1 (d.joiningLine_incident hyv).1
      (d.joiningLine_incident hyv).2 hyb hub
    simpa only [he] using hbk
  · have huv : Adj d.L u v := ⟨Ne.symm hvu,k,huk,hvk⟩
    apply d.lineType_symm
    exact (d.triangle_labels u v y k b (d.joiningLine hyv) 1 huv (adj_symm hyv)
      (adj_symm huy) huk hvk hub hyb (d.joiningLine_incident hyv).2
      (d.joiningLine_incident hyv).1).mp (d.lineType_symm hbk)

/-- An oval in a plane meets the pencil of a shared native octad. This gives
an actual coplanar line to the outside endpoint line. -/
theorem oval_visible_hits_delta_one {v : Point d.P} {π : Plane z} {m b k : Line d.L}
    (hvπ : OnPlane d.P v π) (hmπ : LineOnPlane d.L m π)
    (ho : Native.Polar.Oval (d.visibleSynthemes hvπ hmπ))
    (hvk : OnLine d.L v k) (hkπ : LineOnPlane d.L k π)
    (hbk : LineType d.residue 1 v b k) :
    ∃ w q, OnLine d.L w m ∧ Adj d.L v w ∧ OnLine d.L v q ∧
      OnLine d.L w q ∧ Coplanar d.L b q := by
  have hvb := (lineType_incident hbk).1
  let σ := d.residue.planesAt v ⟨π,hvπ⟩
  let e := ResidueChart.tetradLabel σ
  let B := d.residue.linesAt v ⟨b,hvb⟩
  let K := d.residue.linesAt v ⟨k,hvk⟩
  have hd : Native.Delta 1 B K := (d.residue.lineType_one_at v ⟨b,hvb⟩ ⟨k,hvk⟩).mp hbk
  obtain ⟨_,A,hA⟩ := hd
  obtain ⟨hAB,hAK⟩ := Finset.mem_inter.mp hA
  have hAσ : Native.PlaneOctad σ A :=
    ((d.residue.incidenceAt v ⟨k,hvk⟩ ⟨π,hvπ⟩).mp hkπ) A hAK
  obtain ⟨a,ha⟩ := Native.planeOctad_duad σ e hAσ
  obtain ⟨s,⟨hs,has⟩,_⟩ := Native.Polar.oval_hits_pencil _ ho a
  obtain ⟨q,hq⟩ := (d.mem_visibleSynthemes hvπ hmπ s).mp hs
  obtain ⟨w,hwm,hvw,hvq,hwq⟩ := q.property
  have hqπ := (d.lineView_in_plane hvπ hmπ q.property).2
  have hAQ : A ∈ (d.residue.linesAt v ⟨q.val,hvq⟩).parts := by
    rw [←ha]
    apply (Native.residueEquiv_incidence σ e
      (d.residue.flagLinesNative v π hvπ ⟨q.val,hvq,hqπ⟩) a).mp
    change incident a (d.lineViewEmbedding hvπ hmπ q)
    rw [hq]
    exact has
  refine ⟨w,q.val,hwm,hvw,hvq,hwq,?_⟩
  by_cases he : b = q.val
  · exact ⟨π,he.symm ▸ hqπ,hqπ⟩
  · apply (d.delta_coplanar v b q.val hvb hvq).mpr
    refine ⟨1,by decide,(d.residue.lineType_one_at v ⟨b,hvb⟩ ⟨q.val,hvq⟩).mpr ?_⟩
    refine ⟨?_,A,Finset.mem_inter.mpr ⟨hAB,hAQ⟩⟩
    intro hp
    exact he (congrArg Subtype.val ((d.residue.linesAt v).injective
      (Native.line_parts_injective hp)))

private theorem pencil_two_noncollinear (a : Duad) (s t m : Syntheme)
    (hs : incident a s) (ht : incident a t) (hst : s ≠ t) (hm : ¬ incident a m) :
    (s ≠ m ∧ ¬ synthemeCollinear s m) ∨ (t ≠ m ∧ ¬ synthemeCollinear t m) := by
  have hsm : s ≠ m := fun he => hm (he ▸ hs)
  have htm : t ≠ m := fun he => hm (he ▸ ht)
  by_cases hc : synthemeCollinear s m
  · right
    refine ⟨htm,?_⟩
    intro htc
    obtain ⟨v,_,hv⟩ := quadrangle_unique_collinear_dual a m hm
    have symm (p q : Syntheme) : synthemeCollinear p q → synthemeCollinear q p := by
      intro h
      obtain ⟨hne,b,hp,hq⟩ := (syntheme_collinear_iff_common_duad p q).mp h
      exact (syntheme_collinear_iff_common_duad q p).mpr ⟨hne.symm,b,hq,hp⟩
    exact hst ((hv s ⟨hs,symm s m hc⟩).trans (hv t ⟨ht,symm t m htc⟩).symm)
  · exact Or.inl ⟨hsm,hc⟩

/-- Two distinct neighbors on a three-visible line select a δ₂ direction
for every line outside its singular pencil. -/
theorem lineView_three_select_delta_two {x u v : Point d.P} {k m : Line d.L} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hkπ : LineOnPlane d.L k π)
    (hxl : ¬ OnLine d.L x k) (hcard : {w | OnLine d.L w k ∧ Adj d.L x w}.ncard = 3)
    (huk : OnLine d.L u k) (hvk : OnLine d.L v k) (hxu : Adj d.L x u)
    (hxv : Adj d.L x v) (huv : u ≠ v)
    (hxm : OnLine d.L x m) (hmπ : LineOnPlane d.L m π) (hm : m ∉ d.lineView x k) :
    ∃ w n, (w = u ∨ w = v) ∧ OnLine d.L x n ∧ OnLine d.L w n ∧
      LineType d.residue 2 x n m := by
  let U : d.lineView x k := ⟨d.joiningLine hxu,u,huk,hxu,d.joiningLine_incident hxu⟩
  let V : d.lineView x k := ⟨d.joiningLine hxv,v,hvk,hxv,d.joiningLine_incident hxv⟩
  let M := d.residue.flagLines x π hxπ ⟨m,hxm,hmπ⟩
  obtain ⟨a,ha⟩ := d.lineView_three_singular hxπ hkπ hxl hcard
  have label_mem (q : d.lineView x k) : incident a (d.lineViewEmbedding hxπ hkπ q) := by
    have hq := (d.mem_visibleSynthemes hxπ hkπ _).mpr ⟨q,rfl⟩
    rw [ha] at hq
    exact (Finset.mem_filter.mp hq).2
  have hM : ¬ incident a M := by
    intro h
    have hmem : M ∈ d.visibleSynthemes hxπ hkπ := by
      rw [ha]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
    obtain ⟨q,hq⟩ := (d.mem_visibleSynthemes hxπ hkπ M).mp hmem
    have he : q.val = m := congrArg Subtype.val ((d.residue.flagLines x π hxπ).injective hq)
    exact hm (he ▸ q.property)
  have hUV : d.lineViewEmbedding hxπ hkπ U ≠ d.lineViewEmbedding hxπ hkπ V := by
    intro he
    have he' : d.joiningLine hxu = d.joiningLine hxv :=
      congrArg Subtype.val ((d.lineViewEmbedding hxπ hkπ).injective he)
    have hve : OnLine d.L v (d.joiningLine hxu) := he'.symm ▸ (d.joiningLine_incident hxv).2
    have hk := d.line_eq_of_incident huv huk hvk (d.joiningLine_incident hxu).2 hve
    exact hxl (hk.symm ▸ (d.joiningLine_incident hxu).1)
  have finish (q : d.lineView x k) (w : Point d.P)
      (hw : w = u ∨ w = v) (hwq : OnLine d.L w q.val)
      (hne : d.lineViewEmbedding hxπ hkπ q ≠ M)
      (hn : ¬ synthemeCollinear (d.lineViewEmbedding hxπ hkπ q) M) :
      ∃ w n, (w = u ∨ w = v) ∧ OnLine d.L x n ∧ OnLine d.L w n ∧
        LineType d.residue 2 x n m := by
    have hi := d.lineView_in_plane hxπ hkπ q.property
    have hqm : q.val ≠ m := fun he => hne
      (congrArg (d.residue.flagLines x π hxπ) (Subtype.ext he))
    have hnot : ¬ LineType d.residue 1 x q.val m := fun ht => hn
      ((d.residue.flagLines_collinear_iff x π hxπ ⟨q.val,hi⟩ ⟨m,hxm,hmπ⟩).mpr ht)
    obtain ⟨i,hi',ht⟩ := (d.delta_coplanar x q.val m hi.1 hxm).mp ⟨π,hi.2,hmπ⟩
    refine ⟨w,q.val,hw,hi.1,hwq,?_⟩
    fin_cases i
    · exact (hqm ((d.delta_zero x q.val m).mp ht).2.symm).elim
    · exact (hnot ht).elim
    · exact ht
    · norm_num at hi'
    · norm_num at hi'
  rcases pencil_two_noncollinear a _ _ M (label_mem U) (label_mem V) hUV hM with hU | hV
  · exact finish U u (Or.inl rfl) (d.joiningLine_incident hxu).2 hU.1 hU.2
  · exact finish V v (Or.inr rfl) (d.joiningLine_incident hxv).2 hV.1 hV.2

/-- AS91 (7.4.2). The common δ₁ line and its second common neighbor suffice
for the hitting assertion; both remain in the specified component. -/
theorem deltaThreePlaneHitting : d.DeltaThreePlaneHitting := by
  intro x u y ht hn
  have hxu := ht.1
  have huy := ht.2.1
  have hd : d.deltaThreeStep x u y := ht.2.2.resolve_left (fun hc => hn ⟨hxu,huy,hc⟩)
  obtain ⟨a,b,hua,hxa,hub,hyb,hab⟩ := hd
  obtain ⟨k,hak,hbk⟩ := d.delta_three_common_delta_one hab
  have huk := (lineType_incident hak).2
  obtain ⟨π,haπ,hkπ⟩ := (d.delta_coplanar u a k hua huk).mpr ⟨1,by decide,hak⟩
  have hxπ := d.string x a π hxa haπ
  have huπ := d.string u a π hua haπ
  have hxk : ¬ OnLine d.L x k := by
    intro hxk
    have he := d.line_eq_of_incident hxu.1 hxa hua hxk huk
    have hz := (d.delta_zero u a k).mpr ⟨hua,he.symm⟩
    obtain ⟨i,_,hi⟩ := d.orbital_partition u a k hua huk
    have bad : (0 : Fin 5) = 1 := (hi 0 hz).trans (hi 1 hak).symm
    exact (by decide : (0 : Fin 5) ≠ 1) bad
  have hcard := d.delta_one_neighbors u x a k hua hxa hxu.1 hak
  obtain ⟨v,hvk,hxv,hyv,hvu⟩ := d.delta_three_second_common hxu huy hua hxa hub hyb hab hak hbk
  have huc := mem_commonComponent_self (graph d.L) hxu (adj_symm huy)
  have hvc := commonComponent_step (graph d.L) huc ⟨hxv,hyv⟩ ⟨Ne.symm hvu,k,huk,hvk⟩
  have hyoff : ¬ OnPlane d.P y π := fun hyπ => hn
    ⟨hxu,huy,(d.coplanarStep_iff_plane hxu huy).mpr ⟨π,hxπ,huπ,hyπ⟩⟩
  refine ⟨π,hxπ,huπ,?_⟩
  intro m hxm hmπ
  by_cases hm : m ∈ d.lineView x k
  · obtain ⟨w,hwk,hxw,_,hwm⟩ := hm
    have hwπ := d.string w k π hwk hkπ
    by_cases hwu : w = u
    · subst w
      exact ⟨u,Or.inl huc,hwm⟩
    · have huw : Adj d.L u w := ⟨Ne.symm hwu,k,huk,hwk⟩
      have hcop := (d.delta_coplanar u b k hub huk).mpr ⟨1,by decide,hbk⟩
      exact ⟨w,Or.inr ⟨hxw,u,huc,adj_symm huy,huw,b,k,hub,hyb,huk,hwk,hcop⟩,hwm⟩
  · obtain ⟨w,n,hw,hxn,hwn,hnm⟩ := d.lineView_three_select_delta_two hxπ hkπ hxk hcard
      huk hvk hxu hxv (Ne.symm hvu) hxm hmπ hm
    have hwk : OnLine d.L w k := hw.elim (fun he => he.symm ▸ huk) (fun he => he.symm ▸ hvk)
    have hxw : Adj d.L x w := hw.elim (fun he => he.symm ▸ hxu) (fun he => he.symm ▸ hxv)
    have hyw : Adj d.L y w := hw.elim (fun he => he.symm ▸ adj_symm huy) (fun he => he.symm ▸ hyv)
    have hwc : w ∈ commonComponent (graph d.L) x u y :=
      hw.elim (fun he => he.symm ▸ huc) (fun he => he.symm ▸ hvc)
    have hwπ := d.string w k π hwk hkπ
    have hall := d.delta_two_neighbors x w n m hxn hwn hxw.1.symm hnm
    have ho := d.lineView_five_oval hwπ hmπ hall
    have htype := d.delta_one_at_common_on_line huy hyw hub hyb huk hwk hbk
    obtain ⟨q,r,hqm,hwq,hwr,hqr,hcop⟩ := d.oval_visible_hits_delta_one hwπ hmπ ho hwk hkπ htype
    have hqx : q ≠ x := by
      intro he
      subst q
      have hwp := d.joiningLine_incident hyw
      have hc : d.coplanarStep x w y :=
        ⟨r,d.joiningLine hyw,hwr,hqr,hwp.2,hwp.1,by
          obtain ⟨σ,hbσ,hrσ⟩ := hcop
          exact ⟨σ,hrσ,hbσ⟩⟩
      obtain ⟨σ,hxσ,hwσ,hyσ⟩ := (d.coplanarStep_iff_plane hxw (adj_symm hyw)).mp hc
      have hxy : DistanceTwo d.L x y := by
        refine ⟨?_,?_,u,hxu,huy⟩
        · rintro rfl
          exact hyoff hxπ
        · intro hxy
          exact hn (d.ternary_zero_le_one ⟨hxu,huy,hxy⟩)
      have huσ := d.common_neighbors_in_plane x y σ hxy hxσ hyσ u hxu (adj_symm huy)
      exact hn ⟨hxu,huy,(d.coplanarStep_iff_plane hxu huy).mpr ⟨σ,hxσ,huσ,hyσ⟩⟩
    exact ⟨q,Or.inr ⟨⟨Ne.symm hqx,m,hxm,hqm⟩,w,hwc,hyw,hwq,
      d.joiningLine hyw,r,(d.joiningLine_incident hyw).2,(d.joiningLine_incident hyw).1,
      hwr,hqr,hcop⟩,hqm⟩

/-- B2 with the δ₃ and δ₄ hitting branches proved. Only (7.6.2) remains. -/
theorem bridge_of_componentClose (close : d.ComponentClose) : d.Bridge :=
  d.bridge_of_deltaThree_componentClose d.deltaThreePlaneHitting close

/-- The actual coset graph under the remaining component-distance bound. -/
theorem triangulable_of_componentClose (close : d.ComponentClose) :
    WalkClosure.Triangulable d.system.graph :=
  d.triangulable_of_deltaThree_componentClose d.deltaThreePlaneHitting close

/-- The ambient uniqueness-system base; (7.6.2) is still an explicit
obligation of this family, never a field of the earlier-source Input. -/
theorem isBase_of_componentClose (close : d.ComponentClose) : d.system.IsBase :=
  d.isBase_of_deltaThree_componentClose d.deltaThreePlaneHitting close

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
