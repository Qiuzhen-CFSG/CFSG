module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CriticalEscape

public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Shifted spans in the full-point small-image branch

The forward kernel commutator is a line fixed by the starting stabilizer.
Relative normal generation keeps the commutator of the entire forward seed
span in that same line. Conjugate the span and kernel by the component
element selected with the forward critical extension.

A putative critical pair from the shifted start to the old endpoint forces
the span to centralize the predecessor seed and the endpoint's reverse
kernel. The existing small- and large-image commutator bounds then put the
normal span in its Baumann subgroup, a contradiction. Two further
centralizer steps place both the shifted seed and span in the old endpoint
kernel. Repeating this calculation under the line centralizer places both
centralizer spans in that kernel too.

The application retains the exact critical extension, every shared vertex,
one component conjugator giving both generation and line movement, and the
shifted seed's escape from the second vertex's Baumann subgroup. It uses the
actual characteristic replacement and canonical quotient, with both the
order-16 and order-32 covers. The small original critical image and full
point-radical image remain explicit branches. No trivial fixed subgroup or
natural complement in the cover is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), proof of (5.9), pp.920--921,
through the containment of both centralizer spans in the old endpoint kernel.
The common-kernel span exclusion and remaining Section 5 branches are still
needed for the strict slice estimate and final distance bound. This adapts
SymplecticSetup.ShiftedForwardClosure and ShiftedForwardConfiguration to the
original central covers, using the existing small-image and point-core
commutator controls.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


include h in
private theorem critical_last_edge_inputs (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) ∧
      Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical (p.walk.getVert (p.walk.length-1)) ∧
      Z d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-1)) := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hct : Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-1) (by omega)
    have hi : p.walk.length-1+1 = p.walk.length := by omega
    rw [hi,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical (p.walk.getVert (p.walk.length-1)) = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [p.end_color] at hh
    cases hc : color d.radical (p.walk.getVert (p.walk.length-1)) <;> simp_all
  have het : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-2) (by omega)
    have hi : p.walk.length-2+1 = p.walk.length-1 := by omega
    rw [hi] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  refine ⟨hct,Q_le_adjacent_h d.radical ht het,?_⟩
  apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
  rw [p.dist_start (Nat.sub_le _ _),(replacementGeometry h d).distance_constant a p.start_color]
  change p.walk.length-1 < replacementDistance h d
  have he : p.walk.length = replacementDistance h d := p.length_eq_b
  omega

include h in
private theorem radius_le_predecessor_stabilizer (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical} (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    V d.radical (alpha d.radical) ≤ stabilizer d.radical (p.walk.getVert (p.walk.length-2)) := by
  apply (V_le_iff d.radical rfl _).mpr
  intro v hd hdist
  apply Z_le_stabilizer_of_dist_le v ((replacementGeometry h d).exists_critical v hd)
  rw [(replacementGeometry h d).distance_constant v hd]
  change (cosetGraph d.radical).dist v (p.walk.getVert (p.walk.length-2)) ≤ replacementDistance h d
  have ht := (cosetGraph_connected d.radical).dist_triangle (u:=v) (v:=alpha d.radical)
    (w:=p.walk.getVert (p.walk.length-2))
  rw [p.dist_start (Nat.sub_le _ _)] at ht
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  omega

/-- A normal radius subgroup with a controlled line noncentral on the nearby
endpoint cannot remain outside the starting Baumann subgroup. -/
theorem shifted_critical_controlled_line_false
    (hc : DistanceTwo.CentralLayer d) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection=pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 4<replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (z : Vertex d.radical) (hd : color d.radical z=false)
    (hed : (cosetGraph d.radical).dist a' z≤2)
    (hpd : (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) z≤4)
    (Y T₀ H₁ : Subgroup (FreeAmalgam d.radical))
    (hYV : Y≤V d.radical (alpha d.radical))
    (hYN : stabilizer d.radical (alpha d.radical)≤normalizer (Y:Set (FreeAmalgam d.radical)))
    (hYB : ¬Y≤B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    (hHZ : H₁≤Z d.radical (alpha d.radical)) (hcard : Nat.card H₁≤2)
    (hHd : ¬H₁≤centralizer (Z d.radical z:Set (FreeAmalgam d.radical)))
    (hcomm : ⁅Y,T₀⁆≤H₁)
    (hinner : Z d.radical (p.walk.getVert (p.walk.length-2)) ⊔ (Z d.radical a'⊓Q d.radical (alpha d.radical))≤T₀) :
    False := by
  have hb2 : 2<replacementDistance h d := by omega
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hprecol : color d.radical (p.walk.getVert (p.walk.length-2))=false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := (replacementGeometry h d).even (alpha d.radical) rfl
    change Even (replacementDistance h d) at he
    rw [Nat.even_iff] at he ⊢
    omega
  let := finite_Z d.radical (alpha d.radical)
  let : Finite H₁ := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hsmall (A : Subgroup (FreeAmalgam d.radical)) (hAH : A≤H₁)
      (hAC : A≤centralizer (Z d.radical z:Set (FreeAmalgam d.radical))) : A=⊥ := by
    by_contra hn
    let : Finite A := Finite.of_injective (inclusion hAH) (inclusion_injective _)
    have hpos := (one_lt_card_iff_ne_bot A).mpr hn
    have he : A=H₁ := eq_of_le_of_card_ge hAH (by omega)
    exact hHd (he ▸ hAC)
  have hQd : Q d.radical z≤centralizer (Z d.radical z:Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical z hd))
  have hZpd : Z d.radical (p.walk.getVert (p.walk.length-2))≤centralizer (Z d.radical z:Set (FreeAmalgam d.radical)) := by
    apply le_trans _ hQd
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ hprecol)
    rw [(replacementGeometry h d).distance_constant _ hprecol]
    exact lt_of_le_of_lt hpd hb
  have hZed : Z d.radical a'≤centralizer (Z d.radical z:Set (FreeAmalgam d.radical)) := by
    apply le_trans _ hQd
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [(replacementGeometry h d).distance_constant a' p.end_color]
    change (cosetGraph d.radical).dist a' z<replacementDistance h d
    exact lt_of_le_of_lt hed (by omega)
  have hYGp : Y≤stabilizer d.radical (p.walk.getVert (p.walk.length-2)) :=
    hYV.trans (radius_le_predecessor_stabilizer (h := h) hb2 p)
  have hYp : ⁅Y,Z d.radical (p.walk.getVert (p.walk.length-2))⁆=⊥ := by
    apply hsmall _ ((commutator_mono le_rfl (le_sup_left.trans hinner)).trans hcomm)
    exact (le_normalizer_iff_commutator_le_right.mp (hYGp.trans (Z_normalized d.radical _))).trans hZpd
  have hYfixp := commutator_eq_bot_iff_le_centralizer.mp hYp
  have hYQp : Y≤Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    rw [←C_eq_Q s hc _ hprecol]
    exact le_inf hYGp hYfixp
  have hedge := critical_last_edge_inputs (h := h) hb2 p
  have hYGe : Y≤stabilizer d.radical a' :=
    (hYQp.trans hedge.2.1).trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hedge.1))
  have hYQa : Y≤Q d.radical (alpha d.radical) := hYV.trans ((replacementGeometry h d).V_le_Q hb2 (alpha d.radical) rfl)
  have hYNK : Y≤normalizer (Z d.radical a'⊓Q d.radical (alpha d.radical):Set (FreeAmalgam d.radical)) :=
    (le_inf (hYGe.trans (Z_normalized d.radical a'))
      (hYQa.trans (Q d.radical (alpha d.radical)).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hYK : ⁅Y,Z d.radical a'⊓Q d.radical (alpha d.radical)⁆=⊥ := by
    apply hsmall _ ((commutator_mono le_rfl (le_sup_right.trans hinner)).trans hcomm)
    exact (le_normalizer_iff_commutator_le_right.mp hYNK).trans (inf_le_left.trans hZed)
  have hYe : ⁅Y,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) := by
    by_cases hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))
    · exact (commutator_mono (le_inf hYV hYQp) le_rfl).trans
        (critical_radius_commutator_le_Z s hc u hfull.le hb2 p hlarge)
    · exact small_critical_predecessor_commutator s hc hb2 p
        (Nat.lt_of_not_ge hlarge) Y hYQp (commutator_eq_bot_iff_le_centralizer.mp hYK)
  exact hYB (normalized_radius_le_slice_of_critical_commutator s hc hb2 p Y hYV hYN hYe)

/-- The controlled-line exclusion at any original-group vertex, with the
actual critical walk transported by the right-coset action. -/
theorem shifted_critical_controlled_line_false_at
    (hc : DistanceTwo.CentralLayer d) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection=pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 4<replacementDistance h d) {a a' : Vertex d.radical} (ha : color d.radical a=false)
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (z : Vertex d.radical) (hd : color d.radical z=false)
    (hed : (cosetGraph d.radical).dist a' z≤2)
    (hpd : (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) z≤4)
    (Y T₀ H₁ : Subgroup (FreeAmalgam d.radical))
    (hYV : Y≤V d.radical a)
    (hYN : stabilizer d.radical a≤normalizer (Y:Set (FreeAmalgam d.radical)))
    (hYB : ¬Y≤B d.radical a ((replacementGeometry h d).Z_normal _))
    (hHZ : H₁≤Z d.radical a) (hcard : Nat.card H₁≤2)
    (hHd : ¬H₁≤centralizer (Z d.radical z:Set (FreeAmalgam d.radical)))
    (hcomm : ⁅Y,T₀⁆≤H₁)
    (hinner : Z d.radical (p.walk.getVert (p.walk.length-2)) ⊔ (Z d.radical a'⊓Q d.radical a)≤T₀) :
    False := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  have hbase : act d.radical g⁻¹ (mVertex d.radical g)=alpha d.radical := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  let j := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  have base := shifted_critical_controlled_line_false s hc u hfull hb (a':=act d.radical g⁻¹ a')
  rw [←hbase] at base
  refine base (p.act g⁻¹) (act d.radical g⁻¹ z) (by rwa [action_preserves_color])
    (by rwa [dist_act]) ?_ (Y.map j) (T₀.map j) (H₁.map j) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · change (cosetGraph d.radical).dist
      ((actWalk d.radical g⁻¹ p.walk).getVert ((actWalk d.radical g⁻¹ p.walk).length-2)) (act d.radical g⁻¹ z)≤4
    rwa [actWalk_length,actWalk_getVert,dist_act]
  · rw [V_act]
    exact map_mono hYV
  · rw [stabilizer_act]
    exact (map_mono hYN).trans (Y.le_normalizer_map j)
  · rw [Escape.PairingControl.FirstPairing.B_act (by omega : 2<replacementDistance h d) g⁻¹ (mVertex d.radical g) ha]
    exact fun hh => hYB ((map_le_map_iff_of_injective (MulAut.conj (g⁻¹)⁻¹).injective).mp hh)
  · rw [Z_act]
    exact map_mono hHZ
  · rwa [card_map_of_injective (MulAut.conj (g⁻¹)⁻¹).injective]
  · intro hh
    apply hHd
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply map_injective (f:=j) (MulAut.conj (g⁻¹)⁻¹).injective
    rw [map_commutator,Subgroup.map_bot]
    rw [Z_act] at hh
    exact commutator_eq_bot_iff_le_centralizer.mpr hh
  · rw [←map_commutator]
    exact map_mono hcomm
  · change Z d.radical ((actWalk d.radical g⁻¹ p.walk).getVert ((actWalk d.radical g⁻¹ p.walk).length-2)) ⊔
      (Z d.radical (act d.radical g⁻¹ a')⊓Q d.radical (act d.radical g⁻¹ (mVertex d.radical g)))≤T₀.map j
    rw [actWalk_length,actWalk_getVert,Z_act,Z_act,Q_act,←map_inf _ _ j
      (MulAut.conj (g⁻¹)⁻¹).injective,←Subgroup.map_sup]
    exact map_mono hinner

include s in
theorem small_forward_span_commutator_le_line
    (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hindex : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    let T₀ := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical (p.walk.getVert 2),T₀⁆
    H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),T₀⁆ ≤ H := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T₀ := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T₀⁆
  change H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
    ⁅localZSpan d.radical c (alpha d.radical),T₀⁆ ≤ H
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
    (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have ht : color d.radical t ≠ false := Ne.symm (adjacent_color_ne d.radical hat)
  have hTQt : T₀ ≤ Q d.radical t := inf_le_left.trans (Q_le_adjacent_h d.radical (by cases hh:color d.radical t <;> simp_all) hat)
  have hseed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro z hz
    rw [Z,if_neg ht] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  have hHC : H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    small_forward_line_central s hc hb p hsmall hindex
  have hHN : stabilizer d.radical (alpha d.radical) ≤ normalizer (H : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hHC).trans (Subgroup.centralizer_le_normalizer _)
  have hTN : stabilizer d.radical (alpha d.radical) ≤ normalizer (T₀ : Set (FreeAmalgam d.radical)) :=
    selected_forward_kernel_normalized hb2 rfl hat hct
  have hZcG : Z d.radical c ≤ stabilizer d.radical (alpha d.radical) :=
    ((Z_le_localZSpan d.radical c (alpha d.radical)).trans (localZSpan_le_V d.radical (by
      rw [SimpleGraph.dist_comm,p.dist_start (by omega)]))).trans
      ((replacementGeometry h d).V_local (alpha d.radical) rfl hb2)
  have hZcT : ⁅Z d.radical c,T₀⁆ ≤ H := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct]
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
      (U d.radical c) (Z d.radical t) T₀ H hHN
      ((DistanceEight.U_le_Z d.radical c).trans hZcG)
      ((adjacent_Z_le d.radical rfl hat).trans (Z_le_stabilizer d.radical (alpha d.radical))) le_rfl
    exact (commutator_eq_bot_iff_le_centralizer.mpr (hseed.trans (centralizer_le hTQt))).le.trans bot_le
  refine ⟨hHC,?_⟩
  rw [localZSpan_eq_conjugates]
  apply commutator_iSup_le_of_relative_normal (stabilizer d.radical (alpha d.radical)) T₀ H _ hHN
  · intro g
    have hgmap : (stabilizer d.radical (alpha d.radical)).map
        (MulAut.conj (g:FreeAmalgam d.radical)⁻¹).toMonoidHom = stabilizer d.radical (alpha d.radical) :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical (alpha d.radical)).le_normalizer
        ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
    exact (map_mono hZcG).trans_eq hgmap
  · intro g
    have hm := map_mono (f:=(MulAut.conj (g:FreeAmalgam d.radical)⁻¹).toMonoidHom) hZcT
    have hTm : T₀.map (MulAut.conj (g:FreeAmalgam d.radical)⁻¹).toMonoidHom = T₀ :=
      mem_normalizer_iff_map_conj_eq.mp (hTN ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
    have hHm : H.map (MulAut.conj (g:FreeAmalgam d.radical)⁻¹).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (hHN ((stabilizer d.radical (alpha d.radical)).inv_mem g.property))
    rwa [map_commutator,hTm,hHm] at hm
include h in
private theorem shifted_two_walk (hb : 4<replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') (y : FreeAmalgam d.radical)
    (hy : y∈stabilizer d.radical (p.walk.getVert 2)) :
    ∃ q : (cosetGraph d.radical).Walk (act d.radical y⁻¹ (alpha d.radical)) a',
      q.length=p.walk.length ∧ q.getVert 2=p.walk.getVert 2 ∧
      q.getVert (p.walk.length-2)=p.walk.getVert (p.walk.length-2) := by
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hfix : act d.radical y⁻¹ (p.walk.getVert 2)=p.walk.getVert 2 :=
    (stabilizer d.radical (p.walk.getVert 2)).inv_mem hy
  let q₀ := (actWalk d.radical y⁻¹ (p.walk.take 2)).copy rfl hfix
  have hq₀ : q₀.length=2 := by
    simp only [q₀,SimpleGraph.Walk.length_copy,actWalk_length,SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (by omega : 2≤p.walk.length)]
  refine ⟨q₀.append (p.walk.drop 2),?_,?_,?_⟩
  · rw [SimpleGraph.Walk.length_append,hq₀,SimpleGraph.Walk.drop_length]
    omega
  · rw [SimpleGraph.Walk.getVert_append',hq₀,if_pos (by omega)]
    simpa only [q₀,SimpleGraph.Walk.getVert_copy,actWalk_getVert,
      SimpleGraph.Walk.take_getVert,inf_idem] using hfix
  · rw [SimpleGraph.Walk.getVert_append,hq₀,if_neg (by omega),SimpleGraph.Walk.drop_getVert]
    congr 1
    omega

include h in
private theorem radius_le_stabilizer_of_dist (a v : Vertex d.radical) (ha : color d.radical a=false)
    (hdis : (cosetGraph d.radical).dist a v+2≤replacementDistance h d) :
    V d.radical a≤stabilizer d.radical v := by
  apply (V_le_iff d.radical ha _).mpr
  intro z hd hda
  apply Z_le_stabilizer_of_dist_le z ((replacementGeometry h d).exists_critical z hd)
  rw [(replacementGeometry h d).distance_constant z hd]
  have ht := (cosetGraph_connected d.radical).dist_triangle (u:=z) (v:=a) (w:=v)
  change (cosetGraph d.radical).dist z v≤replacementDistance h d
  omega

private theorem line_collapse {G : Type*} [Group G] (H A C : Subgroup G)
    [Finite H] (hc : Nat.card H≤2) (hHC : ¬H≤C) (hAH : A≤H) (hAC : A≤C) : A=⊥ := by
  by_contra hn
  let : Finite A := Finite.of_injective (inclusion hAH) (inclusion_injective _)
  have hpos := (one_lt_card_iff_ne_bot A).mpr hn
  have he : A=H := eq_of_le_of_card_ge hAH (by omega)
  exact hHC (he ▸ hAC)


include h in
private theorem shifted_span_properties
    (hb : 4<replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hindex : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (p.walk.getVert 2))=2)
    (y : FreeAmalgam d.radical) (hy : y∈stabilizer d.radical (p.walk.getVert 2))
    (H : Subgroup (FreeAmalgam d.radical)) (hHZ : H≤Z d.radical (alpha d.radical))
    (hHC : H≤centralizer (stabilizer d.radical (alpha d.radical):Set (FreeAmalgam d.radical)))
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      Q d.radical (alpha d.radical)⊓centralizer (U d.radical (p.walk.getVert 2)⊓B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _):Set (FreeAmalgam d.radical))⁆≤H) :
    let a := act d.radical y⁻¹ (alpha d.radical)
    let Y := (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)).map (MulAut.conj y).toMonoidHom
    let T₀ := Q d.radical (alpha d.radical)⊓centralizer (U d.radical (p.walk.getVert 2)⊓B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _):Set (FreeAmalgam d.radical))
    let T₂ := T₀.map (MulAut.conj y).toMonoidHom
    let H₂ := H.map (MulAut.conj y).toMonoidHom
    T₂=Q d.radical a⊓centralizer (U d.radical (p.walk.getVert 2)⊓B d.radical a ((replacementGeometry h d).Z_normal _):Set (FreeAmalgam d.radical)) ∧
    Z d.radical (p.walk.getVert 2)≤Y ∧ Y≤V d.radical a ∧
    stabilizer d.radical a≤normalizer (Y:Set (FreeAmalgam d.radical)) ∧
    ¬Y≤B d.radical a ((replacementGeometry h d).Z_normal _) ∧ H₂≤Z d.radical a ∧
    H₂≤centralizer (stabilizer d.radical a:Set (FreeAmalgam d.radical)) ∧ ⁅Y,T₂⁆≤H₂ := by
  let f := (MulAut.conj y).toMonoidHom
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hU : (U d.radical (p.walk.getVert 2)).map f=U d.radical (p.walk.getVert 2) :=
    mem_normalizer_iff_map_conj_eq.mp (U_normalized _ hy)
  have hZ : (Z d.radical (p.walk.getVert 2)).map f=Z d.radical (p.walk.getVert 2) :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical _ hy)
  have hB := Escape.PairingControl.FirstPairing.B_act (geometry:=(replacementGeometry h d))
    (by omega : 2<replacementDistance h d) y⁻¹ (alpha d.radical) rfl
  simp only [inv_inv] at hB
  have hYV : localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)≤V d.radical (alpha d.radical) :=
    localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hUB : (U d.radical (p.walk.getVert 2)⊓B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map f =
        U d.radical (p.walk.getVert 2)⊓B d.radical (act d.radical y⁻¹ (alpha d.radical)) ((replacementGeometry h d).Z_normal _) := by
      rw [map_inf _ _ f (MulAut.conj y).injective,hU,hB]
    have hm := map_inf_centralizer_of_injective f (MulAut.conj y).injective
      (Q d.radical (alpha d.radical)) (U d.radical (p.walk.getVert 2)⊓B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    rw [hUB] at hm
    simpa only [Q_act,inv_inv,coe_inf,Set.inf_eq_inter,f] using hm.symm
  · exact hZ.symm.le.trans (map_mono (Z_le_localZSpan d.radical _ _))
  · simpa only [V_act,inv_inv] using (map_mono (f:=f) hYV)
  · rw [stabilizer_act,inv_inv]
    exact (map_mono (localZSpan_normalized d.radical _ _)).trans
      ((localZSpan d.radical _ _).le_normalizer_map f)
  · rw [hB]
    intro hh
    have hAB := (map_le_map_iff_of_injective (MulAut.conj y).injective).mp hh
    have hUB := (U_le_Z _).trans ((Z_le_localZSpan d.radical _ _).trans hAB)
    have hi := relIndex_eq_one.mpr hUB
    omega
  · simpa only [Z_act,inv_inv] using (map_mono (f:=f) hHZ)
  · rw [stabilizer_act,inv_inv]
    intro z hz g hg
    obtain ⟨z,hz,rfl⟩ := hz
    obtain ⟨g,hg,rfl⟩ := hg
    simpa only [map_mul] using congrArg f (hHC hz g hg)
  · rw [←map_commutator]
    exact map_mono hcomm

/-- The shifted span and seed lie in the old endpoint kernel. The same statement
applies after any further conjugation fixing the controlled line. -/
private theorem shifted_span_le_endpoint_kernel
    (hc : DistanceTwo.CentralLayer d) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection=pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 4<replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hindex : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (p.walk.getVert 2))=2)
    (z : Vertex d.radical) (hd : color d.radical z=false) (hed : (cosetGraph d.radical).dist a' z=2)
    (H : Subgroup (FreeAmalgam d.radical)) (hHZ : H≤Z d.radical (alpha d.radical)) (hcard : Nat.card H≤2)
    (hHC : H≤centralizer (stabilizer d.radical (alpha d.radical):Set (FreeAmalgam d.radical)))
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      Q d.radical (alpha d.radical)⊓centralizer (U d.radical (p.walk.getVert 2)⊓B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _):Set (FreeAmalgam d.radical))⁆≤H)
    (y : FreeAmalgam d.radical) (hy : y∈stabilizer d.radical (p.walk.getVert 2))
    (hmove : ¬H.map (MulAut.conj y).toMonoidHom≤centralizer (Z d.radical z:Set (FreeAmalgam d.radical))) :
    Z d.radical (act d.radical y⁻¹ (alpha d.radical))≤Q d.radical a' ∧
      (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)).map (MulAut.conj y).toMonoidHom≤Q d.radical a' := by
  let a := act d.radical y⁻¹ (alpha d.radical)
  let c := p.walk.getVert 2
  let v := p.walk.getVert (p.walk.length-2)
  let f := (MulAut.conj y).toMonoidHom
  let Y := (localZSpan d.radical c (alpha d.radical)).map f
  let T₀ := Q d.radical (alpha d.radical)⊓centralizer (U d.radical c⊓B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _):Set (FreeAmalgam d.radical))
  let T₂ := T₀.map f
  let H₂ := H.map f
  have ha : color d.radical a=false := (action_preserves_color d.radical y⁻¹ (alpha d.radical)).trans rfl
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hcol : color d.radical c=false := (p.vertex_color (by omega)).mpr (by decide)
  have hv : color d.radical v=false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := (replacementGeometry h d).even (alpha d.radical) rfl
    change Even (replacementDistance h d) at he
    rw [Nat.even_iff] at he ⊢
    omega
  obtain ⟨hT,hZcY,hYV,hYN,hYB,hHZa,hHCa,hcomm₂⟩ :=
    shifted_span_properties (h := h) hb p hindex y hy H hHZ hHC hcomm
  change T₂=Q d.radical a⊓centralizer (U d.radical c⊓B d.radical a ((replacementGeometry h d).Z_normal _):Set (FreeAmalgam d.radical)) at hT
  change Y≤V d.radical a at hYV
  change ⁅Y,T₂⁆≤H₂ at hcomm₂
  have hcard₂ : Nat.card H₂≤2 := by
    dsimp only [H₂,f]
    rwa [card_map_of_injective (MulAut.conj y).injective]
  let := finite_Z d.radical a
  let : Finite H₂ := Finite.of_injective (inclusion hHZa) (inclusion_injective _)
  obtain ⟨q,hql,hqc,hqv⟩ := shifted_two_walk (h := h) hb p y hy
  have hdae : (cosetGraph d.radical).dist a a'≤replacementDistance h d := by
    have hh := SimpleGraph.dist_le q
    rwa [hql,hl] at hh
  have hdav : (cosetGraph d.radical).dist a v≤p.walk.length-2 := by
    have hh := SimpleGraph.dist_le (q.take (p.walk.length-2))
    rw [SimpleGraph.Walk.take_length,hql,inf_eq_left.mpr (Nat.sub_le _ _),hqv] at hh
    exact hh
  have hvQc : Z d.radical v≤Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical v ((replacementGeometry h d).exists_critical v hv)
    rw [(replacementGeometry h d).distance_constant v hv,SimpleGraph.dist_comm]
    have hh := SimpleGraph.dist_le ((p.walk.drop 2).take (p.walk.length-4))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
      inf_eq_left.mpr (by omega : p.walk.length-4≤p.walk.length-2),
      SimpleGraph.Walk.drop_getVert,show 2+(p.walk.length-4)=p.walk.length-2 by omega] at hh
    change (cosetGraph d.radical).dist c v<replacementDistance h d
    exact lt_of_le_of_lt hh (by omega)
  have heQc : Z d.radical a'≤Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [(replacementGeometry h d).distance_constant a' p.end_color,SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-2<replacementDistance h d
    omega
  have hvQa : Z d.radical v≤Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical v ((replacementGeometry h d).exists_critical v hv)
    rw [(replacementGeometry h d).distance_constant v hv,SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist a v<replacementDistance h d
    omega
  have hQcC : Q d.radical c≤centralizer (U d.radical c⊓B d.radical a ((replacementGeometry h d).Z_normal _):Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c hcol))).trans
      (centralizer_le (inf_le_left.trans (U_le_Z _)))
  have hinner : Z d.radical v⊔(Z d.radical a'⊓Q d.radical a)≤T₂ := by
    rw [hT]
    exact le_inf (sup_le hvQa inf_le_right)
      ((sup_le hvQc (inf_le_left.trans heQc)).trans hQcC)
  have hvd : (cosetGraph d.radical).dist v z≤4 := by
    have hh := (cosetGraph_connected d.radical).dist_triangle (u:=v) (v:=a') (w:=z)
    have hve : (cosetGraph d.radical).dist v a'=2 := by
      change (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) a'=2
      rw [p.dist_end]
      omega
    omega
  have hZaQe : Z d.radical a≤Q d.radical a' := by
    by_contra hn
    have hmin := criticalDistance_le d.radical a ((replacementGeometry h d).exists_critical a ha) hn
    rw [(replacementGeometry h d).distance_constant a ha] at hmin
    have heq : (cosetGraph d.radical).dist a a'=replacementDistance h d := le_antisymm hdae hmin
    have hcrit : CriticalPair d.radical a a' ((replacementGeometry h d).exists_critical a ha) :=
      ⟨heq.trans ((replacementGeometry h d).distance_constant a ha).symm,hn⟩
    let p₂ : CriticalPath d.radical (replacementGeometry h d) a a' := ⟨ha,q,hql.trans (hl.trans heq.symm),hcrit⟩
    have hpred : p₂.walk.getVert (p₂.walk.length-2)=v := by
      change q.getVert (q.length-2)=v
      rw [hql,hqv]
    apply shifted_critical_controlled_line_false_at s hc u hfull hb ha p₂ z hd hed.le
      (by rwa [hpred]) Y T₂ H₂ hYV hYN hYB hHZa hcard₂ hmove hcomm₂
    rwa [hpred]
  have heQa : Z d.radical a'≤Q d.radical a := by
    rw [←C_eq_Q s hc a ha]
    refine le_inf ?_ ?_
    · apply Z_le_stabilizer_of_dist_le a' ((replacementGeometry h d).exists_critical a' p.end_color)
      rw [(replacementGeometry h d).distance_constant a' p.end_color,SimpleGraph.dist_comm]
      exact hdae
    · exact le_centralizer_iff.mp (hZaQe.trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a' p.end_color))))
  have heT : Z d.radical a'≤T₂ := by
    rw [hT]
    exact le_inf heQa (heQc.trans hQcC)
  have hQd : Q d.radical z≤centralizer (Z d.radical z:Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical z hd))
  have hvC : Z d.radical v≤centralizer (Z d.radical z:Set (FreeAmalgam d.radical)) := by
    apply le_trans _ hQd
    apply Z_le_Q_of_dist_lt d.radical v ((replacementGeometry h d).exists_critical v hv)
    rw [(replacementGeometry h d).distance_constant v hv]
    exact lt_of_le_of_lt hvd hb
  have heC : Z d.radical a'≤centralizer (Z d.radical z:Set (FreeAmalgam d.radical)) := by
    apply le_trans _ hQd
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [(replacementGeometry h d).distance_constant a' p.end_color,hed]
    change 2<replacementDistance h d
    omega
  have hYGv : Y≤stabilizer d.radical v := hYV.trans
    (radius_le_stabilizer_of_dist (h := h) a v ha (by omega))
  have hYv : ⁅Y,Z d.radical v⁆=⊥ :=
    line_collapse H₂ _ (centralizer (Z d.radical z:Set (FreeAmalgam d.radical))) hcard₂ hmove
      ((commutator_mono le_rfl (le_sup_left.trans hinner)).trans hcomm₂)
      ((le_normalizer_iff_commutator_le_right.mp (hYGv.trans (Z_normalized d.radical v))).trans hvC)
  have hYQv : Y≤Q d.radical v := by
    rw [←C_eq_Q s hc v hv]
    exact le_inf hYGv (commutator_eq_bot_iff_le_centralizer.mp hYv)
  have hedge := critical_last_edge_inputs (h := h) (by omega : 2<replacementDistance h d) p
  have hYGe : Y≤stabilizer d.radical a' := (hYQv.trans hedge.2.1).trans
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hedge.1))
  have hYe : ⁅Y,Z d.radical a'⁆=⊥ :=
    line_collapse H₂ _ (centralizer (Z d.radical z:Set (FreeAmalgam d.radical))) hcard₂ hmove
      ((commutator_mono le_rfl heT).trans hcomm₂)
      ((le_normalizer_iff_commutator_le_right.mp (hYGe.trans (Z_normalized d.radical a'))).trans heC)
  refine ⟨hZaQe,?_⟩
  rw [←C_eq_Q s hc a' p.end_color]
  exact le_inf hYGe (commutator_eq_bot_iff_le_centralizer.mp hYe)


/-- Complete the actual source configuration for a prescribed shifted endpoint
and conjugator. This preserves any further properties of the supplied witnesses,
including a generating edge containing the same moving line. -/
theorem small_shifted_forward_configuration_of_choice
    (hc : DistanceTwo.CentralLayer d) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection=pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 4<replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hindex : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (p.walk.getVert 2))=2)
    (z : Vertex d.radical) (hd : color d.radical z=false) (hed : (cosetGraph d.radical).dist a' z=2)
    (y : FreeAmalgam d.radical) (hy : y∈stabilizer d.radical (p.walk.getVert 2)) :
    let T₀ := Q d.radical (alpha d.radical)⊓centralizer
      (U d.radical (p.walk.getVert 2)⊓B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _):Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical (p.walk.getVert 2),T₀⁆
    ((stabilizer d.radical (p.walk.getVert 2)⊓
      centralizer (H.map (MulAut.conj y).toMonoidHom:Set (FreeAmalgam d.radical)))⊔Z d.radical z=
        stabilizer d.radical (p.walk.getVert 2)) →
    (¬H.map (MulAut.conj y).toMonoidHom≤centralizer (Z d.radical z:Set (FreeAmalgam d.radical))) →
    let a := act d.radical y⁻¹ (alpha d.radical)
    let T₂ := T₀.map (MulAut.conj y).toMonoidHom
    let H₂ := H.map (MulAut.conj y).toMonoidHom
    let Y := (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)).map (MulAut.conj y).toMonoidHom
    let P := stabilizer d.radical (p.walk.getVert 2)⊓centralizer (H₂:Set (FreeAmalgam d.radical))
    P⊔Z d.radical z=stabilizer d.radical (p.walk.getVert 2) ∧
    ¬H₂≤centralizer (Z d.radical z:Set (FreeAmalgam d.radical)) ∧
    T₂=Q d.radical a⊓centralizer (U d.radical (p.walk.getVert 2)⊓B d.radical a ((replacementGeometry h d).Z_normal _):Set (FreeAmalgam d.radical)) ∧
    Z d.radical (p.walk.getVert 2)≤Y ∧ Y≤V d.radical a ∧
    stabilizer d.radical a≤normalizer (Y:Set (FreeAmalgam d.radical)) ∧
    ¬Y≤B d.radical a ((replacementGeometry h d).Z_normal _) ∧ H₂≤Z d.radical a ∧ Nat.card H₂≤2 ∧
    H₂≤centralizer (stabilizer d.radical a:Set (FreeAmalgam d.radical)) ∧ ⁅Y,T₂⁆≤H₂ ∧
    Z d.radical a≤Q d.radical a' ∧ Y≤Q d.radical a' ∧
    conjugateSpanBy (Z d.radical a) P≤Q d.radical a' ∧ conjugateSpanBy Y P≤Q d.radical a' := by
  dsimp only
  intro hgen hmove
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T₀ := Q d.radical (alpha d.radical)⊓centralizer (U d.radical c⊓B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _):Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T₀⁆
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hcol : color d.radical c=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
    (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hline := selected_forward_kernel_line s hc (by omega) p hindex.le
  have hcard : Nat.card H≤2 := hline.1
  have hHZ : H≤Z d.radical (alpha d.radical) := hline.2.trans (adjacent_Z_le d.radical rfl hat)
  have hspan := small_forward_span_commutator_le_line s hc (by omega) p hsmall hindex.le
  have hplace := shifted_span_le_endpoint_kernel s hc u hfull hb p hindex
  obtain ⟨hT,hZcY,hYV,hYN,hYB,hHZa,hHCa,hcomm⟩ :=
    shifted_span_properties (h := h) hb p hindex y hy H hHZ hspan.1 hspan.2
  have hyplace := hplace z hd hed H hHZ hcard hspan.1 hspan.2 y hy hmove
  let a := act d.radical y⁻¹ (alpha d.radical)
  let H₂ := H.map (MulAut.conj y).toMonoidHom
  let Y := (localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c⊓centralizer (H₂:Set (FreeAmalgam d.radical))
  have hmap (A : Subgroup (FreeAmalgam d.radical)) (x : FreeAmalgam d.radical) :
      (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        A.map (MulAut.conj (x*y)).toMonoidHom := by
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro z
    change x*(y*z*y⁻¹)*x⁻¹=(x*y)*z*(x*y)⁻¹
    group
  have hconj (x : P) :
      (Z d.radical a).map (MulAut.conj (x:FreeAmalgam d.radical)).toMonoidHom≤Q d.radical a' ∧
      Y.map (MulAut.conj (x:FreeAmalgam d.radical)).toMonoidHom≤Q d.radical a' := by
    have hxH : H₂.map (MulAut.conj (x:FreeAmalgam d.radical)).toMonoidHom=H₂ :=
      mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) x.property.2)
    have hxy : (x:FreeAmalgam d.radical)*y∈stabilizer d.radical c :=
      (stabilizer d.radical c).mul_mem x.property.1 hy
    have hmove' : ¬H.map (MulAut.conj ((x:FreeAmalgam d.radical)*y)).toMonoidHom≤
        centralizer (Z d.radical z:Set (FreeAmalgam d.radical)) := by
      rw [←hmap]
      change ¬H₂.map (MulAut.conj (x:FreeAmalgam d.radical)).toMonoidHom≤_
      rw [hxH]
      exact hmove
    have hh := hplace z hd hed H hHZ hcard hspan.1 hspan.2 _ hxy hmove'
    change (Z d.radical (act d.radical y⁻¹ (alpha d.radical))).map _≤_ ∧
      ((localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom).map _≤_
    rw [Z_act,inv_inv,hmap,hmap]
    simpa only [Z_act,inv_inv] using hh
  refine ⟨hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,?_,hHCa,hcomm,
    hyplace.1,hyplace.2,?_,?_⟩
  · rw [card_map_of_injective (MulAut.conj y).injective]
    exact hcard
  · rw [conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun x => (hconj x).1)
  · rw [conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun x => (hconj x).2)


/-- The full-point small-image branch supplies the literal shifted spans in
its old endpoint kernel. The path, conjugator, generating centralizer and
noncentral line are all the same choices; both central covers are retained. -/
theorem full_point_small_shifted_spans_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    let c := p.walk.getVert 2
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical c,T⁆
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) c z,
      (cosetGraph d.radical).dist a' z = 2 ∧
      (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
      q.walk.getVert (q.walk.length-2) = a' ∧
      ∃ y ∈ Ltilde d.radical c,
        let a := act d.radical y⁻¹ (alpha d.radical)
        let T₂ := T.map (MulAut.conj y).toMonoidHom
        let H₂ := H.map (MulAut.conj y).toMonoidHom
        let Y := (localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom
        let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
        P ⊔ Z d.radical z = stabilizer d.radical c ∧
        ¬ H₂ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ∧
        T₂ = Q d.radical a ⊓ centralizer
          (U d.radical c ⊓ B d.radical a ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical)) ∧
        Z d.radical c ≤ Y ∧ Y ≤ V d.radical a ∧
        stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) ∧
        ¬ Y ≤ B d.radical a ((replacementGeometry h d).Z_normal _) ∧
        H₂ ≤ Z d.radical a ∧ Nat.card H₂ = 2 ∧
        H₂ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
        ⁅Y,T₂⁆ ≤ H₂ ∧ Z d.radical a ≤ Q d.radical a' ∧ Y ≤ Q d.radical a' ∧
        conjugateSpanBy (Z d.radical a) P ≤ Q d.radical a' ∧
        conjugateSpanBy Y P ≤ Q d.radical a' ∧
        Z d.radical a ≤ V d.radical c ∧
        ¬ Z d.radical a ≤ B d.radical c ((replacementGeometry h d).Z_normal _) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨z,q,haz,hover,hpre,y,hy,hgen,hmove⟩ :=
    full_point_forward_shifted_line_choice_knownSimple (by omega) u hfull p hslice hsmall
  have hline := full_point_small_forward_line_knownSimple (by omega) u hfull p hslice hsmall
  have cfg := small_shifted_forward_configuration_of_choice s hc u hfull' hb p hsmall
    hline.1 z q.end_color haz y (Ltilde_le_stabilizer _ hy) hgen hmove
  obtain ⟨hPgen,hHmove,hT,hZcY,hYV,hYN,hYB,hHZa,hHcard,hHCa,hcomm,
    hZaQ,hYQ,hZspanQ,hYspanQ⟩ := cfg
  refine ⟨z,q,haz,hover,hpre,y,hy,hPgen,hHmove,hT,hZcY,hYV,hYN,hYB,hHZa,?_,
    hHCa,hcomm,hZaQ,hYQ,hZspanQ,hYspanQ,?_,?_⟩
  · rw [card_map_of_injective (MulAut.conj y).injective]
    exact hline.2.1
  · have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    have hZV : Z d.radical (alpha d.radical) ≤ V d.radical (p.walk.getVert 2) :=
      le_iSup_of_le (alpha d.radical) (le_iSup_of_le
        (show (cosetGraph d.radical).dist (alpha d.radical) (p.walk.getVert 2) ≤ 2 from
          (p.dist_start (by omega)).le) le_rfl)
    rw [Z_act,inv_inv]
    exact (map_mono hZV).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (DistanceEight.V_normalized d.radical _ (Ltilde_le_stabilizer _ hy)))
  · have hcol : color d.radical (p.walk.getVert 2) = false :=
      (p.vertex_color (by have hl : p.walk.length = replacementDistance h d := p.length_eq_b; omega)).mpr
        (by decide)
    have hBm := mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (show 2 < replacementDistance h d by omega)
        _ hcol (Ltilde_le_stabilizer _ hy))
    intro hbad
    rw [Z_act,inv_inv,←hBm] at hbad
    have hstart := (map_le_map_iff_of_injective (MulAut.conj y).injective).mp hbad
    exact critical_start_not_le_second_slice s hc (by omega) p
      ((DistanceEight.U_le_Z d.radical _).trans hstart)


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
