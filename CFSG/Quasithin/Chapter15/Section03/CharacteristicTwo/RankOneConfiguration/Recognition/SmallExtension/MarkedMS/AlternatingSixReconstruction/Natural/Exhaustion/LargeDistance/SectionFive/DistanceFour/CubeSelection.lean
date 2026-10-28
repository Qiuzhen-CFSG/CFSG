module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.NonnormalSelection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeCommonFixer

/-!
# Initial distance-four selection for the three-pair and nonsylow branches

The simultaneous edge-kernel and cubic selection in the three-pair image
only needs distance greater than two once the actual radical image is given.
The two edge kernels generate the full starting stabilizer, as do the first
kernel and the two critical seeds. The common-fixer argument therefore
excludes both trapped orientations and constructs a backward critical path
through any neighboring moving seed with slice index greater than two.

At distance four, applying this to the forward seed makes the selected
orbit span nonabelian: both endpoints of the constructed critical path
belong to that orbit. If the forward slice is small, a strict slice at any
neighbor instead constructs a path whose predecessor slice is small. The
already proved residual-rotation selection applies to that literal path.
A small predecessor of the original path is covered directly; a large one
transports to such a strict neighboring slice. This closes initial selection
for the full three-pair radical image, with both moving covers and all
central attachments retained.

The actual original-radical application uses the maximal-image theorem:
a nonsylow radical has either the full point-core image or the three-pair
image. Both now supply a nonabelian large-slice critical path. The remaining
original Sylow images, selected terminal contradiction, and unconditional
DistanceFourInput assembly are still separate obligations.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.6)(b), (5.7)--(5.8), printed pp.917--920, and the initial
selection in (5.12), p.924. The private selection proofs specialize the
existing CubeCommonFixer arguments at their distance-greater-than-two
hypotheses, preserving that module's public boundary and literal maps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

include s in
private theorem cube_small_paired_seed
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          Q d.radical t ⊔ (Q d.radical t).map (MulAut.conj x).toMonoidHom =
            stabilizer d.radical (alpha d.radical) ∧
          x^3 ∈ Q d.radical (alpha d.radical) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (alpha d.radical) (act d.radical x a'),
            (∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i)) ∧
            (Q d.radical (act d.radical x a')).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
            Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
              stabilizer d.radical (alpha d.radical) ∧
            ((¬ Z d.radical a' ≤ normalizer ((Z d.radical (act d.radical g delta) ⊔
              Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) ∨
            (¬ Z d.radical (act d.radical x a') ≤ normalizer ((Z d.radical (act d.radical g delta) ⊔
              Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))) := by
  obtain ⟨t,hat,v,hparabolic,x,hxL,hxN,hx3,hgen⟩ := small_cube_common_fixer_neighbor s hc u hfull p hsmall
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  let c := act d.radical g delta
  have hct : Adjacent d.radical c t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g delta (p.walk.getVert 1)).mpr hdelta
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have helc : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    apply hel
    change U d.radical (act d.radical g delta) ≤ _ at hh
    rw [U_act,←hB] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  have hx : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hxL
  have hfix : act d.radical x (alpha d.radical)=alpha d.radical := hx
  have hq : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (alpha d.radical) (act d.radical x a'),
      ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) := by
    have hq : ∃ q : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical x (alpha d.radical)) (act d.radical x a'),
        ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) :=
      ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hfix] at hq
  obtain ⟨q,hq⟩ := hq
  have hqsmall : (Q d.radical (act d.radical x a')).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    conv_lhs => rhs; rw [←hfix]
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hsmall
  refine ⟨t,hat,g,hg,hgt,hct,x,hxL,hxN,hx3,q,hq,hqsmall,hgen,?_⟩
  by_contra! hboth
  apply helc
  let Y := Z d.radical c ⊔ Z d.radical (alpha d.radical)
  have hYN : stabilizer d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ hboth.1) hboth.2
    apply le_trans (le_inf _ _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (show Q d.radical t ≤ stabilizer d.radical c from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c)
    · exact (show Q d.radical t ≤ stabilizer d.radical (alpha d.radical) from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Z_normalized d.radical _)
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hYV : Y ≤ V d.radical (alpha d.radical) :=
    sup_le ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist))
      (Z_le_VBall d.radical _ 2)
  exact (DistanceEight.U_le_Z d.radical c).trans (le_sup_left.trans
    (SectionFive.normal_small_radius_le_slice s hb Y hYV hYN
      ((SectionFive.cube_backward_product_index s u hfull hat hct).trans (by decide))))

include s in
private theorem cube_strict_small_backward_pair
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          Q d.radical t ⊔ (Q d.radical t).map (MulAut.conj x).toMonoidHom =
            stabilizer d.radical (alpha d.radical) ∧
          x^3 ∈ Q d.radical (alpha d.radical) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (alpha d.radical) (act d.radical x a'),
            (∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i)) ∧
            (Q d.radical (act d.radical x a')).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
            Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
              stabilizer d.radical (alpha d.radical) ∧
            let c := act d.radical g delta
            ((∃ v : CriticalPath d.radical (replacementGeometry h d) c
                (p.walk.getVert (p.walk.length-2)), v.walk.getVert 1=t ∧
                ∀ i ≤ p.walk.length-2, v.walk.getVert (i+2)=p.walk.getVert i) ∨
              (∃ v : CriticalPath d.radical (replacementGeometry h d) c
                (q.walk.getVert (q.walk.length-2)), v.walk.getVert 1=t ∧
                ∀ i ≤ q.walk.length-2, v.walk.getVert (i+2)=q.walk.getVert i)) := by
  have hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    have he := relIndex_eq_one.mpr hh
    omega
  obtain ⟨t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,q,hq,hqs,hgen,hnorm⟩ :=
    cube_small_paired_seed s hc hb u hfull p hsmall hdelta hel
  let c := act d.radical g delta
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) := by
    change 2 < (B d.radical (alpha d.radical) _).relIndex (U d.radical (act d.radical g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hindex
  refine ⟨t,hat,g,hg,hgt,hct,hstrict,x,hx,hxN,hx3,q,hq,hqs,hgen,?_⟩
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change color d.radical c ≠ color d.radical t at h2
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hpath {z : Vertex d.radical}
      (r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
      (hescape : ¬ Z d.radical c ≤ Q d.radical (r.walk.getVert (r.walk.length-2))) :
      ∃ v : CriticalPath d.radical (replacementGeometry h d) c (r.walk.getVert (r.walk.length-2)),
        v.walk.getVert 1=t ∧ ∀ i ≤ r.walk.length-2, v.walk.getVert (i+2)=r.walk.getVert i := by
    let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
      .cons ((cosetGraph_adj d.radical _ _).mpr hct)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
    have hw : w.length=2 := rfl
    let v := r.prepend_two (Nat.le_of_lt hb) hcol w hw hescape
    have hvt : v.walk.getVert 1=t := by
      simp only [v,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    exact ⟨v,hvt,fun i hi => r.prepend_two_overlap _ _ _ _ _ hi⟩
  by_cases hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
  · by_cases hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2))
    · exfalso
      have hxG : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hx
      rcases hnorm with hnp | hnq
      · exact cube_common_fixer_excludes_trapped_pair s hc hb u hfull p hsmall hat hct
          x hxG q hq hqs hgen hxN hpbad hqbad hstrict hnp
      · have hgen' : Q d.radical t ⊔ Z d.radical (act d.radical x a') ⊔ Z d.radical a' =
            stabilizer d.radical (alpha d.radical) := by
          calc
            _ = Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') := by ac_rfl
            _ = _ := hgen
        have hqback (i : ℕ) : p.walk.getVert i = act d.radical x⁻¹ (q.walk.getVert i) := by
          rw [hq,←act_mul,mul_inv_cancel,act_one]
        exact cube_common_fixer_excludes_trapped_pair s hc hb u hfull q hqs hat hct
          x⁻¹ ((stabilizer d.radical (alpha d.radical)).inv_mem hxG) p hqback hsmall hgen'
          (SectionFive.reverse_generating_pair _ _ x hxG hxN) hqbad hpbad hstrict hnq
    · exact Or.inr (hpath q hqbad)
  · exact Or.inl (hpath p hpbad)

include s in
/-- In the full three-pair image, a strict forward slice produces two
noncommuting seeds in the literal selected orbit, on either moving cover. -/
theorem cube_large_forward_span_nonabelian
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (u : S) (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,g,hg,hgt,hct,hi,x,hx,hpair,hx3,q,hq,hqs,hgen,halt⟩ :=
    cube_strict_small_backward_pair s hc hb2 u hfull p hsmall hct hstrict
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  have hseed (k : FreeAmalgam d.radical) (hk : k ∈ stabilizer d.radical (alpha d.radical)) :
      Z d.radical (act d.radical k (p.walk.getVert 2)) ≤ P := by
    rw [Z_act]
    exact (map_mono (Z_le_localZSpan d.radical _ _)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized d.radical _ _
        ((stabilizer d.radical (alpha d.radical)).inv_mem hk)))
  have hstart := hseed g hg
  intro hzero
  rcases halt with ⟨r,hr1,hover⟩ | ⟨r,hr1,hover⟩
  · have hend : Z d.radical (p.walk.getVert (p.walk.length-2)) ≤ P := by
      rw [hl]
      exact Z_le_localZSpan d.radical _ _
    exact critical_Z_commutator_ne_bot s hc r
      (le_bot_iff.mp ((commutator_mono hstart hend).trans_eq hzero))
  · have hql : q.walk.length = 4 := q.length_eq_b.trans hb
    have hend : Z d.radical (q.walk.getVert (q.walk.length-2)) ≤ P := by
      rw [hql,hq]
      exact hseed x (Ltilde_le_stabilizer _ hx)
    exact critical_Z_commutator_ne_bot s hc r
      (le_bot_iff.mp ((commutator_mono hstart hend).trans_eq hzero))

include s in
private theorem cube_initial_of_large_neighbor
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (u : S) (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {delta t : Vertex d.radical}
    (hat : Adjacent d.radical (alpha d.radical) t) (hdt : Adjacent d.radical delta t)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  by_cases hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))
  · exact exists_nonabelian_large_slice_knownSimple (e := e) (hz := hz) (hn := hn) hb p
      (large_image_selected_span_nonabelian s hc hb p hlarge)
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  by_cases hforward : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))
  · exact ⟨z,p,cube_large_forward_span_nonabelian s hc hb u hfull p hsmall hforward,hforward⟩
  have hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2 := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨k,hk,hkt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hat ha1
  have hdelta : Adjacent d.radical (act d.radical k delta) (p.walk.getVert 1) := by
    rw [←hkt]
    exact (adjacent_act_iff d.radical k _ _).mpr hdt
  have hB (j : FreeAmalgam d.radical) (hj : j ∈ stabilizer d.radical (alpha d.radical)) :
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj j⁻¹).toMonoidHom =
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hj))
  have hi : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical k delta)) := by
    rw [U_act,←hB k hk,relIndex_map_map_of_injective _ _ (MulAut.conj k⁻¹).injective]
    exact hstrict
  obtain ⟨t,hat,g,hg,hgt,hct,hi,x,hx,hpair,hx3,q,hq,hqs,hgen,halt⟩ :=
    cube_strict_small_backward_pair s hc hb2 u hfull p hsmall hdelta hi
  rcases halt with ⟨r,hr1,hover⟩ | ⟨r,hr1,hover⟩
  · have hr2 : r.walk.getVert 2 = alpha d.radical := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
    apply initial_selection_of_small_predecessor_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb r
    rw [hr2,hl]
    exact hslice
  · have hr2 : r.walk.getVert 2 = alpha d.radical := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
    have hql : q.walk.length = 4 := q.length_eq_b.trans hb
    apply initial_selection_of_small_predecessor_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb r
    rw [hr2,hql,hq,U_act,←hB x (Ltilde_le_stabilizer _ hx),
      relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hslice

include e hz hn in
/-- The three-pair radical image supplies initial nonabelian large-slice
selection at distance four. Small predecessor slices use residual rotation;
large ones transport to the paired-kernel selection on the original graph. -/
theorem cube_initial_selection_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom) :
    ∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  by_cases hs : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) ≤ 2
  · exact initial_selection_of_small_predecessor_knownSimple (e := e) (hz := hz) (hn := hn) hb p hs
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcCol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent d.radical z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical hcCol
  have hbase : act d.radical g⁻¹ (p.walk.getVert 2) = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hat : Adjacent d.radical (alpha d.radical) (act d.radical g⁻¹ (p.walk.getVert 3)) := by
    simpa only [hbase] using (adjacent_act_iff d.radical g⁻¹ _ _).mpr hct
  apply cube_initial_of_large_neighbor s hc hb u hf hat
    ((adjacent_act_iff d.radical g⁻¹ _ _).mpr hzt)
  rw [←hbase,Escape.PairingControl.FirstPairing.B_act hb2 _ _ hcCol,
    U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
  omega

include e hz hn in
/-- All nonsylow original radicals admit the required initial selection:
the maximal image is either the already selected point core or the three-pair
image handled here. This keeps the literal original relative Sylow condition. -/
theorem nonsylow_initial_selection_knownSimple
    (hb : replacementDistance h d = 4)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) :
    ∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
  rcases nonsylow_radical_image_maximal_knownSimple
    (h := h) (e := e) (hz := hz) (hn := hn) (d := d) (by omega) hns with ⟨u,hu⟩ | ⟨u,hu⟩
  · exact full_point_initial_selection_knownSimple hb u hu
  · exact cube_initial_selection_knownSimple hb u hu

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
