module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardRigidity

/-!
# Nonzero backward kernels and the residual critical shift

An eligible backward seed which stays in the second predecessor core cannot
fix the full reverse critical kernel. Otherwise the seed joined with the
starting seed is normal under a generating edge and the opposite critical
actor. Residual action then puts it in the starting Baumann slice, contradicting
eligibility. This argument needs neither a point-core image nor an assumed
upper slice bound.

With point-core containment, failure of backward escape forces the original
critical index and eligible slice index to be two. The reverse-kernel
commutator is a nonzero line, noncentral at the chosen backward vertex.
Both the full kernel and its moving part are retained, including the central
line of the order-32 cover.

Failure of radius escape bounds every two-edge Baumann slice by two: move
a hypothetical larger slice to the generating edge and apply the backward
step. Vertex transitivity transports this bound to every component vertex.
The full-point application constructs the generating edge from the original
replacement, without an extra generation or numerical slice premise.

When the reverse kernel lies in the predecessor slice, its nonzero line is
preserved by the same residual transporter which moves the last edge to
the preceding edge. We construct the resulting critical walk, retaining
the prescribed first edge and all overlapping vertices. Its seed image is
at least four: an index-two image would identify its full moving commutator
with the backward line, contradicting residual displacement rigidity.
Both radius indices on this shifted critical path are consequently strictly
greater than eight in the actual known-simple application.

Source: Meierfrankenfeld--Stellmacher (1993), (5.7)--(5.8), printed
pp.919--920, with the full-cover action in (3.3)(ii), pp.866--867.
Predecessor slice placement is still explicit; the numerical upper bound
alone is not that containment. Discharging it, the other radical-image
branches, exact-four exclusion, intermediate R4/R6 noncentrality, both
terminal contradictions, largeDistance_knownSimple and the unconditional
replacementDistance = 2 remain with qt-e-ms-small-a6-exhaustion-large-distance.
Final whole-core reconstruction remains with qt-e-ms-small-a6-reconstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
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

include s in
/-- An eligible backward seed cannot fix the full reverse kernel while
remaining in the predecessor core. This does not require point-core image
containment or a bound on the eligible slice. -/
theorem eligible_backward_kernel_ne_bot
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    (hbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≠ ⊥ := by
  intro hzero
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hZV : Z d.radical c ≤ V d.radical (alpha d.radical) :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)
  have hfix : Z d.radical c ≤ centralizer
      (Z d.radical a' ⊓ Q d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
  have hmove := small_critical_predecessor_commutator s hc hb p hsmall
    (Z d.radical c) hbad hfix
  let Y := Z d.radical c ⊔ Z d.radical (alpha d.radical)
  have hYmove : ⁅Y,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
      (Z d.radical c) (Z d.radical (alpha d.radical)) (Z d.radical a')
      (Z d.radical (alpha d.radical)) (Z_normalized d.radical _)
      (hZV.trans ((replacementGeometry h d).V_local _ rfl hb))
      (Z_le_stabilizer d.radical _) hmove
      (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _))
  have hYn : stabilizer d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    apply sup_le
    · exact (le_inf
        ((show Q d.radical t ≤ stabilizer d.radical c from
          fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c))
        ((show Q d.radical t ≤ stabilizer d.radical (alpha d.radical) from
          fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Z_normalized d.radical _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hYmove.trans le_sup_right)
  exact hel ((DistanceEight.U_le_Z d.radical c).trans
    (le_sup_left.trans (normalized_radius_le_slice_of_critical_commutator s hc hb p Y
      (sup_le hZV (Z_le_VBall d.radical _ 2)) hYn hYmove)))

include s in
/-- Failure of an eligible backward escape forces index two and a nonzero
order-two reverse-kernel commutator. The order-32 cover is retained. -/
theorem eligible_backward_failure_line
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    (hbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) = 2 ∧
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical c) = 2 ∧
      Nat.card (⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅U d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≠ ⊥ := by
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by
    by_contra! hh
    exact large_image_backward_not_le s hc hb u hR p hh hat hct hgen hel hbad
  have hupper : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) ≤ 2 := by
    by_contra! hh
    exact small_image_backward_not_le s hc hb u hR p hsmall hat hct hgen hh hbad
  have hne := eligible_backward_kernel_ne_bot s hc hb p hsmall hat hct hgen hel hbad
  have hcard := small_critical_kernel_predecessor_card s hc hb u hR p hsmall
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let H := ⁅K,Z d.radical c⁆
  have hKQ : K ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end]
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-(p.walk.length-2) < replacementDistance h d
    omega
  let := finite_stabilizer d.radical (p.walk.getVert (p.walk.length-2))
  let : Finite (⁅K,Q d.radical (p.walk.getVert (p.walk.length-2))⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion ((Subgroup.commutator_le_sup _ _).trans
      ((sup_le hKQ le_rfl).trans (fun _ hx => hx.1)))) (inclusion_injective _)
  have hle : H ≤ ⁅K,Q d.radical (p.walk.getVert (p.walk.length-2))⁆ := commutator_mono le_rfl hbad
  let : Finite H := Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hHupper : Nat.card H ≤ 2 := (card_le_of_le hle).trans hcard
  have hHlower : 1 < Nat.card H := (one_lt_card_iff_ne_bot H).mpr hne
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hpos : 0 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hindexne : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) ≠ 1 := fun he => hel (relIndex_eq_one.mp he)
  refine ⟨(small_critical_indices s hc p hsmall).1,by omega,by change Nat.card H = 2; omega,?_⟩
  rwa [←(critical_kernel_predecessor_moving s hc hb p).2.2 (Z d.radical c) hbad]

include s in
/-- The backward-kernel commutator forced by eligibility is noncentral at
the selected backward vertex. The full moving cover detects any central
commutator, including in the order-32 case. -/
theorem eligible_backward_kernel_not_central
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    (hbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    ¬ ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≤
      centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
  intro hcentral
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  have hne := eligible_backward_kernel_ne_bot s hc hb p hsmall hat hct hgen hel hbad
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hKG : K ≤ stabilizer d.radical c :=
    (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc c hcol
  let A := K.comap i
  have hmA : A.map i = K := map_comap_eq_self (hKG.trans_eq hir.symm)
  have hcA : ⁅replacementMoved d,A⁆ ≤ center d.overgroup := by
    intro x hx
    apply mem_center_iff.mpr
    intro m
    apply hi
    simp only [map_mul]
    apply hcentral
    · have hh := mem_map_of_mem i hx
      rw [map_commutator,hmA,hiU,commutator_comm] at hh
      exact commutator_mono le_rfl (DistanceEight.U_le_Z d.radical c) hh
    · rw [←hir]
      exact ⟨m,rfl⟩
  have hKQ := map_mono (f := i) (cover_central_commutator_forces_core s A hcA)
  rw [hmA,hiQ] at hKQ
  apply hne
  rw [commutator_comm]
  exact le_bot_iff.mp ((commutator_mono le_rfl hKQ).trans_eq
    (Z_centralizes_Q d.radical c hcol))

include s in
/-- Failure of radius escape bounds every two-edge Baumann slice by two.
A hypothetical larger slice can be moved to the generating edge, where
the proved backward step contradicts the original radius containment.
Vertex transitivity then gives the bound at every component vertex. -/
theorem radius_failure_all_slice_indices_le_two
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' t₀ : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hat₀ : Adjacent d.radical (alpha d.radical) t₀)
    (hgen : Q d.radical t₀ ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (hbad : V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ≤ 2 := by
  have hbase {c t : Vertex d.radical}
      (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t) :
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical c) ≤ 2 := by
    by_contra! hindex
    obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hat hat₀
    have hcgt : Adjacent d.radical (act d.radical g c) t₀ := by
      rw [←hgt]
      exact (adjacent_act_iff d.radical g c t).mpr hct
    have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        hb (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
    have hindexg : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (act d.radical g c)) := by
      rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      exact hindex
    have hdist : (cosetGraph d.radical).dist (act d.radical g c) (alpha d.radical) ≤ 2 := by
      have h1 : (cosetGraph d.radical).dist (act d.radical g c) t₀ = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hcgt)
      have h2 : (cosetGraph d.radical).dist t₀ (alpha d.radical) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr
          ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat₀))
      simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
        (u := act d.radical g c) (v := t₀) (w := alpha d.radical)
    have hcQ : Z d.radical (act d.radical g c) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) :=
      ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)).trans hbad
    by_cases hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))
    · apply large_image_backward_not_le s hc hb u hR p hlarge hat₀ hcgt hgen ?_ hcQ
      intro hh
      have hi := relIndex_eq_one.mpr hh
      omega
    · exact small_image_backward_not_le s hc hb u hR p (Nat.lt_of_not_ge hlarge)
        hat₀ hcgt hgen hindexg hcQ
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical ha
  have hga : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex]
    simp only [mul_inv_cancel]
    rfl
  have hgat : Adjacent d.radical (alpha d.radical) (act d.radical g⁻¹ t) := by
    rw [←hga]
    exact (adjacent_act_iff d.radical g⁻¹ a t).mpr hat
  have hh := hbase hgat ((adjacent_act_iff d.radical g⁻¹ c t).mpr hct)
  rw [←hga,Escape.PairingControl.FirstPairing.B_act hb g⁻¹ a ha,U_act,
    relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective] at hh
  exact hh

/-- The original full-point replacement supplies the generating edge, so
failure of radius escape yields the source's uniform upper slice bound
without any assumed slice selection or index. -/
theorem radius_failure_all_slice_indices_le_two_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hbad : V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ≤ 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t₀,hat₀,hgen⟩ := full_point_generating_neighbor s hc u hfull' p
  exact radius_failure_all_slice_indices_le_two s hc hb u hfull'.le p hat₀ hgen hbad ha hat hct

include s in
/-- The same predecessor residual shift gives a genuine critical path from
the eligible backward vertex to the transported endpoint. Its first edge
and every overlapping vertex are retained. Nonvanishing is derived from
eligibility, rather than assumed. -/
theorem eligible_backward_residual_critical_path
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    (hbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hslice : U d.radical a' ⊓ Q d.radical (alpha d.radical) ≤
      B d.radical (p.walk.getVert (p.walk.length-2)) ((replacementGeometry h d).Z_normal _))
    (k : FreeAmalgam d.radical)
    (hk : k ∈ Ltilde d.radical (p.walk.getVert (p.walk.length-2)))
    (hkt : act d.radical k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3)) :
    ∃ q : CriticalPath d.radical (replacementGeometry h d) c (act d.radical k a'),
      4 ≤ (Q d.radical (act d.radical k a')).relIndex (Z d.radical c) ∧
      q.walk.getVert 1 = t ∧
      (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical (act d.radical k⁻¹ c)⁆ =
        ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ := by
  have hline := eligible_backward_failure_line s hc hb u hR p hat hct hgen hel hbad
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [hline.1]
    decide
  have hne := eligible_backward_kernel_ne_bot s hc hb p hsmall hat hct hgen hel hbad
  have hfullslice := (critical_kernel_predecessor_moving s hc hb p).2.1.mpr hslice
  have hcol : color d.radical (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have htransport :
      ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical (act d.radical k⁻¹ c)⁆ =
        ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ := by
    rw [Z_act,inv_inv]
    exact small_slice_commutator_residual_transport (h := h) hb hcol _ hfullslice
      (small_critical_kernel_predecessor_card s hc hb u hR p hsmall) _ hbad k hk
  have hescape : ¬ Z d.radical c ≤ Q d.radical (act d.radical k a') := by
    intro hh
    have hm : Z d.radical (act d.radical k⁻¹ c) ≤ Q d.radical a' := by
      calc
        _ = (Z d.radical c).map (MulAut.conj k).toMonoidHom := by rw [Z_act,inv_inv]
        _ ≤ (Q d.radical (act d.radical k a')).map (MulAut.conj k).toMonoidHom := map_mono hh
        _ = Q d.radical (act d.radical k⁻¹ (act d.radical k a')) := by
          simpa only [inv_inv] using (Q_act d.radical k⁻¹ (act d.radical k a')).symm
        _ = Q d.radical a' := by rw [←act_mul,mul_inv_cancel,act_one]
    apply hne
    rw [←htransport]
    exact le_bot_iff.mp ((commutator_mono inf_le_left hm).trans_eq
      (Z_centralizes_Q d.radical a' p.end_color))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcfalse : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hlast : Adjacent d.radical (p.walk.getVert (p.walk.length-1)) a' := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hend : (cosetGraph d.radical).Adj (p.walk.getVert (p.walk.length-3)) (act d.radical k a') := by
    rw [←hkt]
    exact (cosetGraph_adj d.radical _ _).mpr
      ((adjacent_act_iff d.radical k _ _).mpr hlast)
  let w₀ : (cosetGraph d.radical).Walk c (alpha d.radical) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  let w₁ := (p.walk.take (p.walk.length-3)).concat hend
  let w := w₀.append w₁
  have hw₀ : w₀.length = 2 := rfl
  have hw : w.length = p.walk.length := by
    simp only [w,w₁,SimpleGraph.Walk.length_append,hw₀,SimpleGraph.Walk.length_concat,
      SimpleGraph.Walk.take_length,inf_eq_left.mpr (Nat.sub_le _ _)]
    omega
  have hmin := criticalDistance_le d.radical c ((replacementGeometry h d).exists_critical c hcfalse) hescape
  rw [(replacementGeometry h d).distance_constant c hcfalse] at hmin
  have hdist : (cosetGraph d.radical).dist c (act d.radical k a') = replacementDistance h d := by
    have hh := SimpleGraph.dist_le w
    rw [hw,p.length_eq_b] at hh
    exact le_antisymm hh hmin
  let q : CriticalPath d.radical (replacementGeometry h d) c (act d.radical k a') :=
    ⟨hcfalse,w,hw.trans (p.length_eq_b.trans hdist.symm),by
      refine ⟨?_,hescape⟩
      rw [(replacementGeometry h d).distance_constant c hcfalse]
      exact hdist⟩
  have hlarge : 4 ≤ (Q d.radical (act d.radical k a')).relIndex (Z d.radical c) := by
    by_contra! hqsmall
    let qr := CriticalPath.ofPair (geometry := replacementGeometry h d) q.end_color
      (critical_reverse_pair s hc q)
    have hqrsmall : (Q d.radical c).relIndex (Z d.radical (act d.radical k a')) < 4 := by
      rw [(small_critical_indices s hc q hqsmall).2]
      decide
    let D := ⁅U d.radical a',Z d.radical (act d.radical k⁻¹ c)⁆
    have hcardD : Nat.card D = 2 := by
      dsimp only [D]
      rw [←card_map_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom)
        (MulAut.conj k⁻¹).injective,map_commutator]
      have hZ : (Z d.radical (act d.radical k⁻¹ c)).map (MulAut.conj k⁻¹).toMonoidHom =
          Z d.radical c := by
        rw [←Z_act,←act_mul,inv_mul_cancel,act_one]
      rw [←U_act,hZ,small_critical_moving_commutator_eq s hc qr hqrsmall]
      exact small_critical_commutator_card s hc qr hqrsmall
    let : Finite D := Nat.finite_of_card_ne_zero (by rw [hcardD]; decide)
    have hkQ : (Q d.radical (p.walk.getVert (p.walk.length-2))).map
        (MulAut.conj k).toMonoidHom = Q d.radical (p.walk.getVert (p.walk.length-2)) :=
      mem_normalizer_iff_map_conj_eq.mp ((Q_normalized d.radical _)
        (Ltilde_le_stabilizer _ hk))
    have hDk : Z d.radical (act d.radical k⁻¹ c) ≤
        Q d.radical (p.walk.getVert (p.walk.length-2)) := by
      rw [Z_act,inv_inv]
      exact (map_mono hbad).trans_eq hkQ
    have hle : ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≤ D := by
      rw [←htransport,(critical_kernel_predecessor_moving s hc hb p).2.2 _ hDk]
      exact commutator_mono inf_le_left le_rfl
    have heq : ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ = D :=
      eq_of_le_of_card_ge hle (by rw [hline.2.2.1,hcardD])
    have hdisp := critical_kernel_residual_displacement_ne s hc hb u hR p hsmall
      hfullslice (Z d.radical c) hbad hne k hk
    apply hdisp
    simpa only [D,Z_act,inv_inv] using heq.symm
  refine ⟨q,hlarge,?_,?_,htransport⟩
  · change (w₀.append w₁).getVert 1 = t
    simp only [SimpleGraph.Walk.getVert_append,hw₀,show 1<2 from by decide,ite_true,
      w₀,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero]
  · intro i hi
    change (w₀.append w₁).getVert (i+2) = p.walk.getVert i
    rw [SimpleGraph.Walk.getVert_append,hw₀,if_neg (by omega),Nat.add_sub_cancel]
    change ((p.walk.take (p.walk.length-3)).concat hend).getVert i = p.walk.getVert i
    rw [SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.getVert_append']
    rw [if_pos (by simpa only [SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (Nat.sub_le _ _)] using hi),SimpleGraph.Walk.take_getVert,inf_eq_right.mpr hi]

/-- In the actual full-point replacement, failure of radius escape
constructs the generating edge, eligible backward vertex, noncentral line
and residual-shifted critical path. Only predecessor slice placement remains
explicit; neither the nonzero commutator nor either index-two assertion is
an input. Both central covers and the original transporter are retained. -/
theorem radius_failure_residual_critical_shift_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hbad : V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hslice : U d.radical a' ⊓ Q d.radical (alpha d.radical) ≤
      B d.radical (p.walk.getVert (p.walk.length-2)) ((replacementGeometry h d).Z_normal _)) :
    ∃ t c, Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) = 2 ∧
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical c) = 2 ∧
      Nat.card (⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 ∧
      (¬ ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≤
        centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))) ∧
      ∃ k ∈ Ltilde d.radical (p.walk.getVert (p.walk.length-2)),
        act d.radical k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) c (act d.radical k a'),
          4 ≤ (Q d.radical (act d.radical k a')).relIndex (Z d.radical c) ∧
          8 < (Q d.radical (act d.radical k a')).relIndex (V d.radical c) ∧
          8 < (Q d.radical c).relIndex (V d.radical (act d.radical k a')) ∧
          q.walk.getVert 1 = t ∧
          (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          (∀ i, (p.act k).walk.getVert i = act d.radical k (p.walk.getVert i)) ∧
          ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical (act d.radical k⁻¹ c)⁆ =
            ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ∧
          ⁅U d.radical a',Z d.radical (act d.radical k⁻¹ c)⁆ ≠
            ⁅U d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t,hat,hgen⟩ := full_point_generating_neighbor s hc u hfull' p
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge s hc hb rfl hat
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hcQ : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) :=
    ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)).trans hbad
  have hline := eligible_backward_failure_line s hc hb u hfull'.le p hat hct hgen hel hcQ
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [hline.1]
    decide
  obtain ⟨k,hk,hkt,hdisp,hact⟩ := critical_kernel_selected_residual_shift_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull.le p hsmall hslice c hcQ hline.2.2.2
  obtain ⟨q,hlarge,hqt,hover,htransport⟩ := eligible_backward_residual_critical_path s hc hb u hfull'.le
    p hat hct hgen hel hcQ hslice k hk hkt
  exact ⟨t,c,hat,hct,hgen,hline.1,hline.2.1,hline.2.2.1,
    eligible_backward_kernel_not_central s hc hb p hsmall hat hct hgen hel hcQ,
    k,hk,hkt,q,hlarge,critical_radius_index_gt_eight s hc hb q hlarge,
    opposite_radius_index_gt_eight s hc hb q hlarge,hqt,hover,hact,htransport,hdisp⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
