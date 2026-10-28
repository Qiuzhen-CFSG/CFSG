module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.TerminalLine
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Inputs

/-!
# Small critical images at distance four in the full-point branch

The actual backward selection has a central critical commutator at the
original vertex. If either of its critical images were large, edge
commutator control would make the full point-core action quadratic on the
original moved cover. Its nonzero double commutator excludes this, retaining
both possible cover orders, sixteen and thirty-two.

For a large original critical image at distance four, the selected backward
path therefore supplies a forward slice of index two and a nonabelian
selected span. On the elementary central quotient of this span the actual
symmetric action is faithful. The original radius commutator estimate makes
an even involution from the endpoint image fix a subgroup of index at most
two, contrary to the alternating-six displacement bound. Thus all critical
images at distance four have order two, at every vertex of the original
graph. In particular, a large critical image forces the full-point
replacement to have distance two.

Source: Meierfrankenfeld--Stellmacher (1993), (5.12)(2), printed pp.925--926,
using (3.3)(ii), (5.2), and the selected backward path from (5.7)--(5.8).
The odd-image centralizer and selected-commutator arguments adapt
SymplecticSetup.SelectedCritical and SelectedChain. The central quotient
argument uses the original-cover SelectedSpan and SelectedKernel APIs;
it does not identify a central cover with its natural quotient.

The final application is to the literal minimum characteristic replacement.
Full point-core equality remains explicit. The small-image distance-four
exclusion and the other radical-image branches remain obligations of the
large-distance assembly owner.
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
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem edge_derived_le_core_of_abelian_image
    (hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ⁅Q d.radical t,Q d.radical t⁆ ≤ Q d.radical a := by
  have hr : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup := by
    rw [←s.projection_kernel,←Subgroup.map_eq_bot_iff,map_commutator]
    exact hab
  have hbase : ⁅Q d.radical (beta d.radical),Q d.radical (beta d.radical)⁆ ≤
      Q d.radical (alpha d.radical) := by
    rw [Q_beta,Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d),←map_commutator]
    exact map_mono hr
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [map_commutator,←Q_act,←Q_act] at hh
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using hh
  · rw [hg.1] at ha
    cases ha

private theorem fixed_mod_central_normalizes_line {H : Type*} [Group H]
    (A Q D : Subgroup H) (hAQ : A ≤ normalizer (Q : Set H))
    (hDQ : D ≤ normalizer (Q : Set H))
    (hDA : ⁅D,A⁆ ≤ centralizer (Q : Set H)) :
    D ≤ normalizer ((⁅A,Q⁆ : Subgroup H) : Set H) := by
  apply le_normalizer_closure_iff.mpr
  rintro d hd _ ⟨a,ha,q,hq,rfl⟩
  have hq' : d*q*d⁻¹ ∈ Q := (mem_normalizer_iff.mp (hDQ hd) q).mp hq
  have hk : ⁅d,a⁆ ∈ centralizer (Q : Set H) := hDA (commutator_mem_commutator hd ha)
  have hcomm : ⁅a,d*q*d⁻¹⁆ ∈ Q :=
    le_normalizer_iff_commutator_le_right.mp hAQ (commutator_mem_commutator ha hq')
  have hzero : ⁅⁅d,a⁆,d*q*d⁻¹⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hk _ hq').symm
  rw [conjugate_commutatorElement,show d*a*d⁻¹ = ⁅d,a⁆*a by
    simp [commutatorElement_def,mul_assoc],commutatorElement_mul_left_eq_conj_mul,
    hzero,mul_one,←hk _ hcomm,mul_inv_cancel_right]
  exact commutator_mem_commutator ha hq'


theorem critical_commutator_normalized_first_of_abelian_image
    (hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥)
    {a e : Vertex d.radical} (p : CriticalPath d.radical (replacementGeometry h d) a e) :
    Q d.radical (p.walk.getVert 1) ≤ normalizer ((⁅Z d.radical a,Z d.radical e⁆:Subgroup (FreeAmalgam d.radical)):Set (FreeAmalgam d.radical)) := by
  let D := ⁅Z d.radical a,Z d.radical e⁆
  let t := p.walk.getVert 1
  have hpos : 0<p.walk.length := p.length_eq_b ▸ (replacementDistance_pos h d)
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero,Nat.zero_add] using
      p.walk.adj_getVert_succ (i:=0) hpos
  have ht : color d.radical t=true := by
    have hn := adjacent_color_ne d.radical hat
    rw [p.start_color] at hn
    cases hc : color d.radical t <;> simp_all
  have hZe : Z d.radical e≤Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical e ((replacementGeometry h d).exists_critical e p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(replacementGeometry h d).distance_constant e p.end_color]
    change p.walk.length-1<(replacementGeometry h d).b d.radical
    rw [←p.length_eq_b]
    omega
  have hQtG : Q d.radical t≤stabilizer d.radical a := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hQtZ := hQtG.trans (Z_normalized d.radical a)
  have hder : ⁅Q d.radical t,Z d.radical e⁆≤centralizer (Z d.radical a:Set (FreeAmalgam d.radical)) :=
    ((commutator_mono le_rfl hZe).trans (edge_derived_le_core_of_abelian_image s hab p.start_color hat)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)))
  exact (show Q d.radical t≤normalizer (D:Set (FreeAmalgam d.radical)) from by
    dsimp only [D]
    rw [commutator_comm (Z d.radical a)]
    exact fixed_mod_central_normalizes_line (Z d.radical e) (Z d.radical a) (Q d.radical t)
      (hZe.trans hQtZ) hQtZ hder)

private theorem even_quadratic_conjugate_bound (A : Subgroup S) (g : S)
    (hcore : A≤pointCore.map (MulAut.conj g).toMonoidHom)
    (heven : A≤alternatingGroup (Fin 6)) (hq : QuadraticPointCore.Quadratic A) :
    Nat.card A≤2 := by
  let B:=A.map (MulAut.conj g⁻¹).toMonoidHom
  have hB : B≤pointCore := by
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨b,hb,he⟩ := hcore ha
    rw [←he]
    change g⁻¹*(g*b*g⁻¹)*g∈pointCore
    rw [show g⁻¹*(g*b*g⁻¹)*g=b by group]
    exact hb
  have hBe : B≤alternatingGroup (Fin 6) :=
    (map_mono heven).trans_eq (Subgroup.Normal.map_conj_eq _ g⁻¹)
  have hh:=QuadraticPointCore.even_quadratic_card_le_two B (le_inf hB hBe)
    (QuadraticPointCore.quadratic_conjugate A hq g⁻¹)
  rwa [card_map_of_injective (MulAut.conj g⁻¹).injective] at hh

private theorem normal_eq_top_of_odd_image
    (N : Subgroup d.overgroup) [N.Normal] (hk : pCore 2 d.overgroup≤N)
    (hodd : ¬ N.map s.projection≤alternatingGroup (Fin 6)) : N=⊤ := by
  have hne : ¬ N≤pCore 2 d.overgroup := by
    intro hh
    apply hodd
    rw [show N.map s.projection=⊥ from
      (map_eq_bot_iff N).mpr (hh.trans_eq s.projection_kernel.symm)]
    exact bot_le
  have hnon : N.map s.projection ≠ ⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff N).mp he)
  let : (N.map s.projection).Normal := Subgroup.Normal.map inferInstance _ s.surjective
  have hAlt : alternatingGroup (Fin 6) ≤ N.map s.projection :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) ((nontrivial_iff_ne_bot _).mpr hnon)
  obtain ⟨a,ha,hodd⟩ := SetLike.not_le_iff_exists.mp hodd
  have hsign : Equiv.Perm.sign a = -1 :=
    (Int.units_eq_one_or _).resolve_left (fun h => hodd (Equiv.Perm.mem_alternatingGroup.mpr h))
  have htop : N.map s.projection=⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x∈alternatingGroup (Fin 6)
    · exact hAlt hx
    · have hxsign : Equiv.Perm.sign x = -1 :=
        (Int.units_eq_one_or _).resolve_left (fun h => hx (Equiv.Perm.mem_alternatingGroup.mpr h))
      have hmem : x*a⁻¹∈alternatingGroup (Fin 6) := by
        rw [Equiv.Perm.mem_alternatingGroup,map_mul,map_inv,hxsign,hsign]
        decide
      have hh := (N.map s.projection).mul_mem (hAlt hmem) ha
      simpa only [inv_mul_cancel_right] using hh
  have he := comap_map_eq_self (f:=s.projection) (H:=N) (s.projection_kernel ▸ hk)
  rw [htop,comap_top] at he
  exact he.symm

private theorem normalized_subgroup_central_of_critical_odd
    (D A : Subgroup (FreeAmalgam d.radical))
    (hD : D≤stabilizer d.radical (alpha d.radical))
    (hn : stabilizer d.radical (alpha d.radical)≤normalizer (D:Set (FreeAmalgam d.radical)))
    (hQ : Q d.radical (alpha d.radical)≤centralizer (D:Set (FreeAmalgam d.radical)))
    (hAC : A≤centralizer (D:Set (FreeAmalgam d.radical)))
    (hodd : ¬ (A.comap (embedM d.radical)).map s.projection≤alternatingGroup (Fin 6)) :
    D≤centralizer (stabilizer d.radical (alpha d.radical):Set (FreeAmalgam d.radical)) := by
  let D₀ := D.comap (embedM d.radical)
  let N := centralizer (D₀:Set d.overgroup)
  have hDm : D₀.map (embedM d.radical)=D := map_comap_eq_self (hD.trans_eq (stabilizer_m_base d.radical))
  have hg (m:d.overgroup) : embedM d.radical m∈stabilizer d.radical (alpha d.radical) := by
    change embedM d.radical m∈stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : D₀.Normal := ⟨by
    intro z hd m
    change embedM d.radical (m*z*m⁻¹)∈D
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hn (hg m)) _).mp hd⟩
  let : N.Normal := inferInstance
  have hk : pCore 2 d.overgroup≤N := by
    intro m hm z hd
    apply embedM_injective d.radical
    simp only [map_mul]
    exact hQ (by rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]; exact mem_map_of_mem _ hm) _ hd
  have hAN : A.comap (embedM d.radical)≤N := by
    intro a ha z hd
    apply embedM_injective d.radical
    simp only [map_mul]
    exact hAC ha _ hd
  have htop : N=⊤ := normal_eq_top_of_odd_image s N hk
    (fun hh => hodd ((map_mono hAN).trans hh))
  rintro z hd g hg'
  obtain ⟨m,rfl⟩ := (show stabilizer d.radical (alpha d.radical)≤(embedM d.radical).range from
    (stabilizer_m_base d.radical).le) hg'
  obtain ⟨x,hx,rfl⟩ := hDm.symm ▸ hd
  have hc : m∈N := htop ▸ mem_top m
  simpa only [map_mul] using (congrArg (embedM d.radical) (hc x hx)).symm


/-- Every opposite critical image contains an odd permutation, for either
central cover. Point-core containment is sufficient. -/
theorem critical_opposite_image_not_le_alternating (hc : DistanceTwo.CentralLayer d) (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ¬ graphImage s (Z d.radical a') ≤ alternatingGroup (Fin 6) := by
  intro heven
  by_cases hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))
  · have hp := replacementDistance_pos h d
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
      have hh := (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
      simpa only [SimpleGraph.Walk.getVert_zero] using hh
    have hAt : Z d.radical a' ≤ Q d.radical (p.walk.getVert 1) := by
      apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
      rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end]
      change p.walk.length-1 < replacementDistance h d
      omega
    obtain ⟨v,hv⟩ := graphImage_le_pointCore_of_le_edge s u hR _ hat _ hAt
    have hbound := even_quadratic_conjugate_bound _ v hv heven
      (critical_opposite_image_quadratic s hc p)
    rw [graphImage_card s _ (critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl hp p.critical)] at hbound
    have hrev := reverse_critical_image_four_le s hc hp p hlarge
    omega
  · obtain ⟨a,ha,hs⟩ := small_critical_image_swap s hc p (by omega)
    have hh := Equiv.Perm.mem_alternatingGroup.mp (heven ha)
    rw [hs.sign_eq] at hh
    norm_num at hh

/-- A selected critical commutator is fixed at the midpoint. The original
point-core containment, central cover and generating edge are retained. -/
theorem selected_critical_commutator_central
    (hc : DistanceTwo.CentralLayer d) (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < replacementDistance h d) {m c a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) m c)
    (q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hm : (cosetGraph d.radical).dist m (alpha d.radical) ≤ 2)
    (hcm : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2)
    (hce : (cosetGraph d.radical).dist c a' < replacementDistance h d)
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical)) :
    ⁅Z d.radical m,Z d.radical c⁆ ≤
      centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  let D := ⁅Z d.radical m,Z d.radical c⁆
  have hVm : Z d.radical m ≤ V d.radical (alpha d.radical) :=
    le_iSup_of_le m (le_iSup_of_le hm le_rfl)
  have hVc : Z d.radical c ≤ V d.radical (alpha d.radical) :=
    le_iSup_of_le c (le_iSup_of_le hcm le_rfl)
  have hDX : D ≤ X d.radical (alpha d.radical) :=
    (commutator_mono hVm hVc).trans ((radius_bounds_of_two_lt s hc u hR hb rfl m c).2.1)
  have hDQ : D ≤ Q d.radical (alpha d.radical) := hDX.trans (omegaCenter_le _)
  have hQC : Q d.radical (alpha d.radical) ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (hDX.trans (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2))
  have hDc : D ≤ Z d.radical c := ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right).trans
    (DistanceEight.U_le_Z d.radical c)
  have hC : Z d.radical a' ≤ centralizer (D : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    apply (hDc.trans (Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c p.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' q.end_color)))
    rwa [(replacementGeometry h d).distance_constant c p.end_color]
  have hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥ := by
    let := pointCore_elementary
    let : IsElementaryAbelian 2 (pointCore.map (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
    let helem : IsElementaryAbelian 2 (d.radical.map s.projection) :=
      IsElementaryAbelian.of_le (B := pointCore.map (MulAut.conj u).toMonoidHom) hR
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr helem.toIsMulCommutative))
  have hN : stabilizer d.radical (alpha d.radical) ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le (critical_commutator_normalized_first_of_abelian_image s hab p)
      (hC.trans (Subgroup.centralizer_le_normalizer _))
  exact normalized_subgroup_central_of_critical_odd s D (Z d.radical a')
    (hDQ.trans (fun _ hx => hx.1)) hN hQC hC
    (critical_opposite_image_not_le_alternating s hc u hR q)

/-- If a critical commutator is fixed by its entire first edge kernel,
its critical images have order two. The nonquadratic full point-core action
supplies the bound without deleting the center of the order-32 cover. -/
theorem critical_indices_two_of_first_edge_central
    (hc : DistanceTwo.CentralLayer d) (u : S)
    (hfull : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hcentral : ⁅Z d.radical a,Z d.radical a'⁆ ≤
      centralizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical))) :
    (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
      (Q d.radical a).relIndex (Z d.radical a') = 2 := by
  apply small_critical_indices s hc p
  by_contra! hlarge
  have hp := replacementDistance_pos h d
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hAt : Z d.radical a' ≤ Q d.radical (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-1 < replacementDistance h d
    omega
  have hU : ⁅U d.radical a,Z d.radical a'⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ :=
    commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl
  have hcomm := edge_commutator_control_at s hc u hfull.le a _ p.start_color hat
    (Z d.radical a') (Q d.radical (p.walk.getVert 1)) hAt le_rfl
    (reverse_critical_image_four_le s hc hp p hlarge)
    ((hU.trans hcentral).trans (centralizer_le hAt)) (hU.trans hcentral)
  apply edge_double_commutator_ne_bot s hc u hfull p.start_color hat
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact ((commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl).trans hcomm).trans hcentral

/-- The same selected commutator has order two and both critical images
have order two, without a zero fixed-space assumption on the cover. -/
theorem selected_critical_indices_two
    (hc : DistanceTwo.CentralLayer d) (u : S)
    (hfull : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < replacementDistance h d) {m c a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) m c)
    (q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hm : (cosetGraph d.radical).dist m (alpha d.radical) ≤ 2)
    (hcm : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2)
    (hce : (cosetGraph d.radical).dist c a' < replacementDistance h d)
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical)) :
    (Q d.radical c).relIndex (Z d.radical m) = 2 ∧
      (Q d.radical m).relIndex (Z d.radical c) = 2 ∧
      Nat.card (⁅Z d.radical m,Z d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hcentral := selected_critical_commutator_central s hc u hfull.le hb p q hm hcm hce hgen
  have hi := critical_indices_two_of_first_edge_central s hc u hfull p
    (hcentral.trans (centralizer_le (show Q d.radical (p.walk.getVert 1) ≤
      stabilizer d.radical (alpha d.radical) by rw [←hgen]; exact le_sup_left)))
  exact ⟨hi.1,hi.2,small_critical_commutator_card s hc p (by omega)⟩

/-- At distance four, the prescribed backward chain has small images.
The original generating edge and every path vertex remain literal. -/
theorem selected_backward_indices_two_of_distance_four
    (hc : DistanceTwo.CentralLayer d) (u : S)
    (hfull : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : replacementDistance h d = 4) {a' c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert (p.walk.length-2)))
    (hq2 : q.walk.getVert 2 = alpha d.radical)
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical)) :
    (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical c) = 2 ∧
      (Q d.radical c).relIndex (Z d.radical (p.walk.getVert (p.walk.length-2))) = 2 ∧
      Nat.card (⁅Z d.radical c,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  apply selected_critical_indices_two s hc u hfull (by omega) q p
  · simpa only [hq2] using (q.dist_start (i := 2) (by omega)).le
  · have hh := (p.dist_start (i := p.walk.length-2) (Nat.sub_le _ _)).le
    simpa only [SimpleGraph.dist_comm,hl,Nat.reduceSub] using hh
  · rw [p.dist_end,hl,hb]
    decide
  · exact hgen

/-- In the large-critical-image branch at distance four, the original
forward Baumann slice has index at most two. A larger slice produces a
backward path whose proved large and small image bounds contradict. -/
theorem large_image_four_forward_slice_le_two_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    (u : S) (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2 := by
  by_contra! hindex
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,_,hgen,g,hg,hgt,q,hq1,hover,hqlarge,_⟩ :=
    large_image_backward_large_radii_knownSimple hb2 u hfull p hlarge hdelta hindex
  have hq2 : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hi := selected_backward_indices_two_of_distance_four s hc u hf hb p q hq2 (by rwa [hq1])
  omega

/-- The literal large-image distance-four branch supplies an index-two
forward slice, a nonabelian forward span, and a small backward critical
line central at the original vertex. The same conjugator and complete
walk overlap are retained. -/
theorem large_image_four_selected_chain_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    (u : S) (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) = 2 ∧
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
        ∃ g ∈ stabilizer d.radical (alpha d.radical),
          act d.radical g (p.walk.getVert 1) = t ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (act d.radical g (p.walk.getVert 2)) (p.walk.getVert (p.walk.length-2)),
            q.walk.getVert 1 = t ∧
            (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex
              (Z d.radical (act d.radical g (p.walk.getVert 2))) = 2 ∧
            (Q d.radical (act d.radical g (p.walk.getVert 2))).relIndex
              (Z d.radical (p.walk.getVert (p.walk.length-2))) = 2 ∧
            Nat.card (⁅Z d.radical (act d.radical g (p.walk.getVert 2)),
              Z d.radical (p.walk.getVert (p.walk.length-2))⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
            ⁅Z d.radical (act d.radical g (p.walk.getVert 2)),
              Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
              centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,hgen⟩ := full_point_generating_neighbor s hc u hf p
  have hel := critical_forward_not_le_slice_of_escape s hc hb2
    (full_point_criticalEscape s hc hb2 u hf) p
  obtain ⟨g,hg,hgt,q,hq1,hover,hindex⟩ :=
    large_image_backward_shift s hc hb2 u hf.le p hlarge hdelta hel hat hgen
  have hq2 : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hgen' : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical a' =
      stabilizer d.radical (alpha d.radical) := by rwa [hq1]
  have hi := selected_backward_indices_two_of_distance_four s hc u hf hb p q hq2 hgen'
  have hcentral := selected_critical_commutator_central s hc u hf.le hb2 q p
    (by simpa only [hq2] using (q.dist_start (i := 2) (by rw [q.length_eq_b]; change 2 ≤ replacementDistance h d; omega)).le)
    (by have hh := (p.dist_start (i := p.walk.length-2) (Nat.sub_le _ _)).le
        simpa only [SimpleGraph.dist_comm,hl,Nat.reduceSub] using hh)
    (by rw [p.dist_end,hl,hb]; decide) hgen'
  have hcP : Z d.radical (p.walk.getVert 2) ≤
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) := Z_le_localZSpan d.radical _ _
  have hgP : Z d.radical (act d.radical g (p.walk.getVert 2)) ≤
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) := by
    rw [Z_act]
    exact (map_mono hcP).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized d.radical _ _ ((stabilizer d.radical (alpha d.radical)).inv_mem hg)))
  have hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ := by
    intro hz
    apply critical_Z_commutator_ne_bot s hc q
    apply le_bot_iff.mp
    exact (commutator_mono hgP (by simpa only [hl,Nat.reduceSub] using hcP)).trans_eq hz
  exact ⟨hindex (by omega),hnon,t,hat,hgen,g,hg,hgt,q,hq1,hover,hi.1,hi.2.1,hi.2.2,hcentral⟩

private theorem linearized_cyclic_codim_eq_one
    {Y : Type*} [Group Y] [Finite Y] [IsElementaryAbelian 2 Y]
    {D : Type*} [Group D] (ρ : D→*MulAut Y) (hf : Function.Injective ρ)
    (a : D) (ha : a≠1) (hi : (ρ a).fixedSubgroup.index≤2) :
    fixedCodim (Offenders.linearize ρ) (zpowers a)=1 := by
  let σ := Offenders.linearize ρ
  change fixedCodim σ (zpowers a)=1
  let e : fixedSpace σ (zpowers a) ≃ (ρ a).fixedSubgroup := {
    toFun := fun v => ⟨v.val.toMul, (MulAut.mem_fixedSubgroup _ _).mpr
      (congrArg Additive.toMul ((mem_fixedSpace_zpowers_iff σ a v.val).mp v.property))⟩
    invFun := fun v => ⟨Additive.ofMul v.val,(mem_fixedSpace_zpowers_iff σ a _).mpr
      (congrArg Additive.ofMul ((MulAut.mem_fixedSubgroup _ _).mp v.property))⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcard : Nat.card Y≤Nat.card ((ρ a).fixedSubgroup)*2 := by
    rw [←(ρ a).fixedSubgroup.card_mul_index]
    exact Nat.mul_le_mul_left _ hi
  rw [←Nat.card_congr e] at hcard
  change Nat.card (Additive Y)≤_ at hcard
  have hV := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive Y)
  have hF := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=fixedSpace σ (zpowers a))
  rw [Nat.card_zmod] at hV hF
  rw [hV,hF] at hcard
  have hd : Module.finrank (ZMod 2) (Additive Y)≤
      Module.finrank (ZMod 2) (fixedSpace σ (zpowers a))+1 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    simpa only [pow_succ] using hcard
  have hne : zpowers a≠⊥ := fun he => ha (mem_bot.mp (he ▸ mem_zpowers a))
  have hp := fixedCodim_pos_of_faithful σ (Offenders.linearize_injective ρ hf) hne
  have hs := fixedCodim_add_finrank σ (zpowers a)
  omega


private theorem even_actor_not_small_fixed
    {Y : Type*} [Group Y] [Finite Y] [IsElementaryAbelian 2 Y]
    (ρ : S →* MulAut Y) (hf : Function.Injective ρ) (a : S)
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) :
    ¬ (ρ a).fixedSubgroup.index ≤ 2 := by
  intro hi
  have hne : a ≠ 1 := by intro he; rw [he,orderOf_one] at ha; omega
  have hup := linearized_cyclic_codim_eq_one ρ hf a hne hi
  let σ := Offenders.linearize ρ
  change fixedCodim σ (zpowers a) = 1 at hup
  have hinj := Offenders.linearize_injective ρ hf
  have hevenne : σ a ≠ 1 := by
    intro he
    apply hne
    exact hinj (he.trans σ.map_one.symm)
  have hlo := Representation.AlternatingSixInvolutionDisplacement.fixedCodim_lower_of_even_involution_mem
    σ ⟨⟨a,heven⟩,hevenne⟩ a ha heven (mem_zpowers a)
  omega

/-- A large critical image is impossible at distance four in the full
point-core branch. The selected span has faithful S₆ action on its central
quotient, but an even involution would fix a subgroup of index at most two,
contradicting the A₆ displacement bound. Both central covers are retained. -/
theorem large_critical_image_four_false_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    (u : S) (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨hslice,hnon,_⟩ := large_image_four_selected_chain_knownSimple hb u hfull p hlarge
  have hd : (cosetGraph d.radical).dist (p.walk.getVert 2) (alpha d.radical) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by
      have hh : p.walk.length = replacementDistance h d := p.length_eq_b; omega)]
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  have hPG : P ≤ stabilizer d.radical (alpha d.radical) :=
    (localZSpan_le_V d.radical hd).trans ((replacementGeometry h d).V_local _ rfl hb2)
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  let := selected_span_central_quotient_elementary s hc hb2 (p.walk.getVert 2) hd
  let ρ := selectedSpanSymmetricAction s hc hb2 (p.walk.getVert 2) hd
  have hρ : Function.Injective ρ := selected_span_symmetric_action_injective s hb2 p hnon ρ
    (selectedSpanSymmetricAction_projection s hc hb2 (p.walk.getVert 2) hd)
  obtain ⟨a,haA,ha,heven⟩ := exists_even_involution_reverse_critical_image s hc
    (replacementDistance_pos h d) p hlarge
  obtain ⟨m,hm,rfl⟩ := haA
  have hindex := (selected_span_index_of_forward_slice s hc hb2 p hslice.le).2
  have hcomm : ⁅P ⊓ Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤
      Z d.radical (alpha d.radical) := by
    have hbound := critical_radius_commutator_le_Z s hc u hf.le hb2 p hlarge
    have he : p.walk.length-2 = 2 := by
      have hh : p.walk.length = replacementDistance h d := p.length_eq_b; omega
    rw [he] at hbound
    exact (commutator_mono (inf_le_inf_right _ (localZSpan_le_V d.radical hd)) le_rfl).trans hbound
  exact even_actor_not_small_fixed ρ hρ (s.projection m) ha heven
    (selected_span_endpoint_fixed_index s hc hb2 p hd hindex hcomm m hm)

/-- Thus every critical pair at distance four has both seed indices two
under the literal full point-core marking. -/
theorem full_point_four_critical_indices_two_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    (u : S) (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) = 2 ∧
      (Q d.radical (alpha d.radical)).relIndex (Z d.radical a') = 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  apply small_critical_indices s (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) p
  by_contra! hlarge
  exact large_critical_image_four_false_knownSimple hb u hfull p hlarge

/-- The distance-four index calculation holds at every vertex of the
original graph, transported by its actual amalgam action. -/
theorem full_point_four_critical_indices_two_at_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    (u : S) (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
      (Q d.radical a).relIndex (Z d.radical a') = 2 ∧
      Nat.card (⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := full_point_four_critical_indices_two_knownSimple hb u hfull
    (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  have hi := base (p.act g⁻¹)
  simp only [Q_act,Z_act,inv_inv,relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) _ _
    (MulAut.conj g).injective] at hi
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  exact ⟨hi.1,hi.2,small_critical_commutator_card s
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) p (by omega)⟩

/-- In the full-point branch, any actual critical image of order at least
four forces distance two for the original characteristic replacement. -/
theorem full_point_distance_two_of_large_critical_image_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    replacementDistance h d = 2 := by
  rcases full_point_distance_two_or_four_knownSimple u hfull with hb | hb
  · exact hb
  · have hi := (full_point_four_critical_indices_two_at_knownSimple hb u hfull p).1
    omega

/-- For the literal minimum replacement, the only remaining full-point
branch is distance four with both indices and every critical line of order
two. This does not assert the unresolved small-image exclusion. -/
theorem original_full_point_distance_two_or_four_small_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    (u : S)
    (hfull : (replacement h).radical.map
      (SourceReduction.projection h e hz hn (replacement h)) =
        pointCore.map (MulAut.conj u).toMonoidHom) :
    replacementDistance h (replacement h) = 2 ∨
      (replacementDistance h (replacement h) = 4 ∧
        ∀ (a a' : Vertex (replacement h).radical)
          (_p : CriticalPath (replacement h).radical (replacementGeometry h (replacement h)) a a'),
          (Q (replacement h).radical a').relIndex (Z (replacement h).radical a) = 2 ∧
          (Q (replacement h).radical a).relIndex (Z (replacement h).radical a') = 2 ∧
          Nat.card (⁅Z (replacement h).radical a,Z (replacement h).radical a'⁆ :
            Subgroup (FreeAmalgam (replacement h).radical)) = 2) := by
  rcases full_point_distance_two_or_four_knownSimple u hfull with hb | hb
  · exact Or.inl hb
  · exact Or.inr ⟨hb,fun _ _ p => full_point_four_critical_indices_two_at_knownSimple hb u hfull p⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
