module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedKernel

/-!
# Residual rotation of the mixed-plane kernel alternative

A small predecessor Baumann slice identifies the whole reverse critical
kernel with the endpoint seed's intersection with that slice. Its commutator with the selected backward seed is
preserved when the predecessor residual moves the last edge to the preceding
edge. Nonvanishing constructs a critical path with the original backward
edge and all shared vertices. Its critical image has order at least four:
otherwise its full moving displacement would equal the reverse-kernel line,
contrary to the full-cover pointwise-fixer calculation.

The same predecessor radius has intersection index at least four against
the new starting core; no containment in the new stabilizer is inferred. The actual mixed-plane selector supplies the nonzero line, and the
consumer splits on the literal predecessor slice. It returns a large slice,
the original backward shift, or the large-image residual shift and radius
growth, without any supplied nonzero commutator or residual element. Both
central covers and the literal original graph and quotient map are retained.
Under failure of starting-radius escape the ordinary backward alternative
is impossible. The final application therefore gives a large predecessor
slice or growth of this intersection index at an actual vertex two steps
behind the start.
Excluding these larger alternatives and the other Sylow and distance-four
branches remains necessary for unconditional distance two.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.8), printed pp.919--920. This applies the existing full-kernel
residual transport to the relative-normalizer mixed-plane selection.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedResidual
local notation "S" => Equiv.Perm (Fin 6)

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- Small predecessor slice placement turns a nonzero full reverse-kernel
commutator into a large critical image after the source residual rotation. -/
theorem mixed_kernel_residual_critical_path_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hslice : (B d.radical (p.walk.getVert (p.walk.length-2))
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical a') ≤ 2)
    (hne : ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≠ ⊥) :
    ∃ k ∈ Ltilde d.radical (p.walk.getVert (p.walk.length-2)),
      act d.radical k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c (act d.radical k a'),
        4 ≤ (Q d.radical (act d.radical k a')).relIndex (Z d.radical c) ∧
        4 ≤ (Q d.radical c).relIndex (V d.radical (p.walk.getVert (p.walk.length-2))) ∧
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical (act d.radical k⁻¹ c)⁆ =
          ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono (plus_le_exceptional.trans
      CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.symm.le)
  have hfullslice : Z d.radical a' ⊓ Q d.radical (alpha d.radical) ≤
      B d.radical (p.walk.getVert (p.walk.length-2)) ((replacementGeometry h d).Z_normal _) :=
    (critical_predecessor_slice_eq_kernel s hc hb p hslice).1.ge.trans inf_le_right
  have hm := (critical_kernel_predecessor_moving s hc hb p).2.2 (Z d.radical c) hbad
  have hmovene : ⁅U d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≠ ⊥ := by
    rwa [←hm]
  have hRs : d.radical.map (SourceReduction.projection h e hz hn d) ≤
      pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hR
  obtain ⟨k,hk,hkt,_,_⟩ := critical_kernel_selected_residual_shift_knownSimple
    hb u hRs p hsmall ((inf_le_inf_right _ (DistanceEight.U_le_Z d.radical a')).trans
      hfullslice) c hbad hmovene
  have hlinecard : Nat.card (⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ :
      Subgroup (FreeAmalgam d.radical)) = 2 := by
    have hh := MixedKernel.mixed_backward_kernel_line_knownSimple hb u him p hsmall hat hct hbad hne
    rw [←hh.2.1]
    exact hh.1
  refine ⟨k,hk,hkt,?_⟩
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
      eq_of_le_of_card_ge hle (by rw [hlinecard,hcardD])
    have hdisp := critical_kernel_residual_displacement_ne s hc hb u hR p hsmall
      hfullslice (Z d.radical c) hbad hne k hk
    apply hdisp
    simpa only [D,Z_act,inv_inv] using heq.symm
  have hreverse : 4 ≤ (Q d.radical c).relIndex (Z d.radical (act d.radical k a')) := by
    by_contra! hs
    let qr := CriticalPath.ofPair (geometry := replacementGeometry h d) q.end_color
      (critical_reverse_pair s hc q)
    have hh := (small_critical_indices s hc qr hs).2
    omega
  have hZeV : Z d.radical a' ≤ V d.radical (p.walk.getVert (p.walk.length-2)) := by
    have hd : (cosetGraph d.radical).dist a' (p.walk.getVert (p.walk.length-2)) ≤ 2 := by
      rw [SimpleGraph.dist_comm,p.dist_end]
      omega
    exact le_iSup_of_le a' (le_iSup_of_le hd le_rfl)
  have hVk : (V d.radical (p.walk.getVert (p.walk.length-2))).map
      (MulAut.conj k⁻¹).toMonoidHom = V d.radical (p.walk.getVert (p.walk.length-2)) :=
    mem_normalizer_iff_map_conj_eq.mp ((DistanceEight.V_normalized d.radical _)
      ((stabilizer d.radical _).inv_mem (Ltilde_le_stabilizer _ hk)))
  have hZkV : Z d.radical (act d.radical k a') ≤
      V d.radical (p.walk.getVert (p.walk.length-2)) := by
    rw [Z_act]
    exact (map_mono hZeV).trans_eq hVk
  let := finite_stabilizer d.radical (p.walk.getVert (p.walk.length-2))
  let : Finite (V d.radical (p.walk.getVert (p.walk.length-2))) :=
    Finite.of_injective (inclusion (((replacementGeometry h d).V_le_Q hb _ hcol).trans
      (fun _ hx => hx.1))) (inclusion_injective _)
  have hgrowth : 4 ≤ (Q d.radical c).relIndex
      (V d.radical (p.walk.getVert (p.walk.length-2))) :=
    hreverse.trans (relIndex_le_of_le_right hZkV index_ne_zero_of_finite)
  refine ⟨q,hlarge,hgrowth,?_,?_,htransport⟩
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

/-- Every original mixed-plane critical path has a large predecessor slice,
a backward critical shift, or a residual shift with large critical image and
predecessor-radius intersection index at least four. There is no supplied slice bound,
critical-image bound, relative generator, or nonzero-kernel premise. -/
theorem mixed_backward_or_predecessor_growth_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    : 2 < (B d.radical (p.walk.getVert (p.walk.length-2))
        ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical a') ∨
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical) ∧
      ∃ c, Adjacent d.radical c t ∧
        ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) ∧
        ((∃ q : CriticalPath d.radical (replacementGeometry h d) c
            (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∨
        (∃ k ∈ Ltilde d.radical (p.walk.getVert (p.walk.length-2)),
          act d.radical k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d) c (act d.radical k a'),
            4 ≤ (Q d.radical (act d.radical k a')).relIndex (Z d.radical c) ∧
            4 ≤ (Q d.radical c).relIndex (V d.radical (p.walk.getVert (p.walk.length-2))) ∧
            q.walk.getVert 1 = t ∧
            (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical (act d.radical k⁻¹ c)⁆ =
              ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆)) := by
  by_cases hslice : (B d.radical (p.walk.getVert (p.walk.length-2))
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical a') ≤ 2
  · right
    by_cases hp : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4
    · obtain ⟨t,hat,hgen,c,hct,hel,hout⟩ :=
        MixedSmallRadius.mixed_small_backward_or_kernel_knownSimple hb u him p hp
      refine ⟨t,hat,hgen,c,hct,hel,?_⟩
      rcases hout with hwalk | ⟨hbad,hcard,_,_⟩
      · exact Or.inl hwalk
      · right
        have hne : ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≠ ⊥ := by
          intro hh
          rw [hh,Subgroup.card_bot] at hcard
          omega
        exact mixed_kernel_residual_critical_path_knownSimple hb u him p hp hat hct hbad hslice hne
    · obtain ⟨t,hat,hgen,c,hct,q,hqt,hover,hel⟩ :=
        SylowNormalizer.mixed_large_backward_shift_knownSimple hb u him p (by omega)
      exact ⟨t,hat,hgen,c,hct,hel,Or.inl ⟨q,hqt,hover⟩⟩
  · exact Or.inl (by omega)

/-- Failure of radius escape on an original mixed-plane path forces a large
predecessor slice or intersection index at least four for that same radius
against the core at a vertex exactly two steps behind the original start. The ordinary backward
path alternative is excluded by the literal trapped-radius containment. -/
theorem mixed_trapped_radius_growth_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (htrapped : V d.radical (alpha d.radical) ≤
      Q d.radical (p.walk.getVert (p.walk.length-2))) :
    2 < (B d.radical (p.walk.getVert (p.walk.length-2))
        ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical a') ∨
      ∃ c : Vertex d.radical,
        (cosetGraph d.radical).dist c (alpha d.radical) = 2 ∧
        4 ≤ (Q d.radical c).relIndex (V d.radical (p.walk.getVert (p.walk.length-2))) := by
  rcases mixed_backward_or_predecessor_growth_knownSimple hb u him p with hlarge | hout
  · exact Or.inl hlarge
  · obtain ⟨t,hat,hgen,c,hct,hel,hout⟩ := hout
    right
    rcases hout with ⟨q,hqt,hover⟩ | ⟨k,hk,hkt,q,hlarge,hgrowth,hqt,hover,hcomm⟩
    · have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
        have h1 : (cosetGraph d.radical).dist c t = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
        have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr
            ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
        simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
          (u := c) (v := t) (w := alpha d.radical)
      have hZV : Z d.radical c ≤ V d.radical (alpha d.radical) :=
        (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)
      exact (q.critical.2 (hZV.trans htrapped)).elim
    · have hqbase : q.walk.getVert 2 = alpha d.radical := by
        simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
      have hl : 2 ≤ q.walk.length := by
        rw [q.length_eq_b]
        exact hb.le
      exact ⟨c,by simpa only [hqbase] using q.dist_start hl,hgrowth⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedResidual
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
