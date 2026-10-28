module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCritical
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePairedEdges

/-!
# Paired generating paths for elementary replacement images

Above distance four, the actual elementary radical image has been identified
with a three-pair subgroup of the full symmetric quotient. We refine the
small-image backward selection so that the old first-edge kernel and the
selected kernel generate the same component stabilizer. The cubic also
normalizes the old kernel, so the inverse orientation preserves that equation.
Together with the two earlier generation equations this gives independent
successive critical lines and a four-group centralizing the common radius.

This extends the CubePairedEdges argument to original Sylow radicals using
the proved elementary-image producers in SylowCritical. The original and
replacement radicals remain distinct. Both central covers and their complete
seeds are retained, as are the literal cubic and graph transporters. The
intentional private import reuses the existing marked finite-group selection
and the transport lemma without changing the earlier public boundary.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.6)--(5.11), printed pp.917--924; the existing CubePairedEdges
proof supplies the marked selection and the two possible path orientations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace SylowTerminal
open CubePairedEdges CubeCommonFixer CubeRadiusAction NaturalGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

include e hz hn in
/-- A prescribed eligible neighbor has two small critical seed candidates.
One component element relates the candidates; the chosen edge kernel
and its conjugate generate the starting stabilizer. At least one candidate fails to normalize the backward seed product. -/
private theorem edge_aligned_paired_seed
    (hb4 : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
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
          Q d.radical (p.walk.getVert 1) ⊔ Q d.radical t = stabilizer d.radical (alpha d.radical) ∧
          x ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ∧
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
  have hb : 2 < replacementDistance h d := by omega
  obtain ⟨u,hfull⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hEimage
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨E,w,hEm,hEi,hEk⟩ := cube_first_edge_marking s u hfull' p
  obtain ⟨t,hat,hanchor,x,hxL,hxN,hxAnchor,hx3,hgen⟩ :=
    aligned_cube_neighbor s hc u hfull' p E w hEm hEi hEk hsmall
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
  refine ⟨t,hat,g,hg,hgt,hct,x,hxL,hanchor,hxAnchor,hxN,hx3,q,hq,hqsmall,hgen,?_⟩
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
    (normal_small_radius_le_slice s hb Y hYV hYN
      ((cube_backward_product_index s u hfull' hat hct).trans (by decide))))

include e hz hn in
/-- The strict source slice on the original elementary-image replacement produces
a backward critical path. The simultaneous common-fixer selection eliminates
both orientations of the trapped line pair and retains the cubic, neighbor
transporter, strict slice, and every overlapping vertex. -/
private theorem strict_edge_aligned_shift
    (hb4 : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
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
          Q d.radical (p.walk.getVert 1) ⊔ Q d.radical t = stabilizer d.radical (alpha d.radical) ∧
          x ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ∧
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
  have hb : 2 < replacementDistance h d := by omega
  have hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    have he := relIndex_eq_one.mpr hh
    omega
  obtain ⟨t,hat,g,hg,hgt,hct,x,hx,hanchor,hxAnchor,hxN,hx3,q,hq,hqs,hgen,hnorm⟩ :=
    edge_aligned_paired_seed (e := e) (hz := hz) (hn := hn)
      hb4 hEimage p hsmall hdelta hel
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
  refine ⟨t,hat,g,hg,hgt,hct,hstrict,x,hx,hanchor,hxAnchor,hxN,hx3,q,hq,hqs,hgen,?_⟩
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
      let s := fullSymmetricAction_knownSimple h e hz hn d hb
      have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
      obtain ⟨u,hu⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
        (e := e) (hz := hz) (hn := hn) hb4 hEimage
      have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
        rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
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
          (reverse_generating_pair _ _ x hxG hxN) hqbad hpbad hstrict hnq
    · exact Or.inr (hpath q hqbad)
  · exact Or.inl (hpath p hpbad)

include e hz hn in
private theorem edge_paired_backward_shift_base
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    Nonempty (EdgePairedBackwardShift (h := h) p) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [(SylowCritical.elementary_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p).1]
    decide
  obtain ⟨t,hat,g,hg,hgt,hct,_,x,hx,hanchor,hxAnchor,hpair,hx3,q,hq,_,hgen,halt⟩ :=
    strict_edge_aligned_shift (e := e) (hz := hz) (hn := hn)
      hb hEimage p hsmall hdelta
      (SylowCritical.elementary_forward_slice_strict_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p)
  rcases halt with ⟨v,hvt,hover⟩ | ⟨v,hvt,hover⟩
  · exact ⟨⟨⟨_,t,g,hg,hgt,rfl,hat,hct,x,hx,hx3,hpair,hgen,v,hvt,hover⟩,hanchor⟩⟩
  · let y := g*x⁻¹
    have hxG : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hx
    have hy : y ∈ stabilizer d.radical (alpha d.radical) := mul_mem hg (inv_mem hxG)
    have hfix : act d.radical x⁻¹ (alpha d.radical) = alpha d.radical := inv_mem hxG
    have hat' : Adjacent d.radical (alpha d.radical) (act d.radical x⁻¹ t) := by
      rw [←hfix]
      exact (adjacent_act_iff d.radical x⁻¹ _ _).mpr hat
    have hyt : act d.radical y (p.walk.getVert 1) = act d.radical x⁻¹ t := by
      rw [show y=g*x⁻¹ from rfl,act_mul,hgt]
    have hstart : act d.radical x⁻¹ (act d.radical g (p.walk.getVert 2)) =
        act d.radical y (p.walk.getVert 2) := (act_mul d.radical g x⁻¹ _).symm
    have hct' : Adjacent d.radical (act d.radical y (p.walk.getVert 2))
        (act d.radical x⁻¹ t) := by
      rw [←hstart]
      exact (adjacent_act_iff d.radical x⁻¹ _ _).mpr hct
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    have hend : act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := by
      rw [hlen,hq,←act_mul,mul_inv_cancel,act_one]
    have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical y (p.walk.getVert 2)) (p.walk.getVert (p.walk.length-2)),
        w.walk.getVert 1=act d.radical x⁻¹ t ∧
        ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
      have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical x⁻¹ (act d.radical g (p.walk.getVert 2)))
          (act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2))),
          w.walk.getVert 1=act d.radical x⁻¹ t ∧
          ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
        refine ⟨v.act x⁻¹,?_,?_⟩
        · simp only [CriticalPath.act,actWalk_getVert,hvt]
        · intro i hi
          simp only [CriticalPath.act,actWalk_getVert,hover i (hlen.symm ▸ hi),hq,
            ←act_mul,mul_inv_cancel,act_one]
      rwa [hstart,hend] at hex
    obtain ⟨w,hw1,hwo⟩ := hex
    refine ⟨⟨⟨_,_,y,hy,hyt,rfl,hat',hct',x⁻¹,inv_mem hx,?_,?_,?_,w,hw1,hwo⟩,?_⟩⟩
    · simpa only [inv_pow] using (Q d.radical (alpha d.radical)).inv_mem hx3
    · rw [Q_act,inv_inv,map_map]
      have he : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
          MonoidHom.id (FreeAmalgam d.radical) := by
        apply MonoidHom.ext
        intro z
        change x⁻¹*(x*z*x⁻¹)*(x⁻¹)⁻¹=z
        group
      rw [he,map_id]
      exact (sup_comm _ _).trans hpair
    · have hQt : (Q d.radical t).map (MulAut.conj x).toMonoidHom =
          Q d.radical (act d.radical x⁻¹ t) := by rw [Q_act,inv_inv]
      have hZa (z : Vertex d.radical) : (Z d.radical z).map (MulAut.conj x).toMonoidHom =
          Z d.radical (act d.radical x⁻¹ z) := by rw [Z_act,inv_inv]
      have hGa : (stabilizer d.radical (alpha d.radical)).map (MulAut.conj x).toMonoidHom =
          stabilizer d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical (alpha d.radical)).le_normalizer hxG)
      have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hgen
      simp only [Subgroup.map_sup,hQt,hZa,hGa,←act_mul,mul_inv_cancel,act_one] at hh
      calc
        _ = Q d.radical (act d.radical x⁻¹ t) ⊔ Z d.radical (act d.radical x⁻¹ a') ⊔
          Z d.radical a' := by ac_rfl
        _ = _ := hh

    · have hQfirst : (Q d.radical (p.walk.getVert 1)).map (MulAut.conj x).toMonoidHom =
          Q d.radical (p.walk.getVert 1) := mem_normalizer_iff_map_conj_eq.mp hxAnchor
      have hGa : (stabilizer d.radical (alpha d.radical)).map (MulAut.conj x).toMonoidHom =
          stabilizer d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical (alpha d.radical)).le_normalizer hxG)
      have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hanchor
      simpa only [Subgroup.map_sup,hQfirst,hGa,Q_act,inv_inv] using hh

include e hz hn in
/-- Repeated selection retains the original-edge generating join and
both earlier generating pairs at every vertex, with no additional premise. -/
theorem elementary_edge_paired_backward_shift_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    Nonempty (EdgePairedBackwardShift (h := h) p) := by
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := edge_paired_backward_shift_base (e := e) (hz := hz) (hn := hn)
    hb hEimage (a' := act d.radical j⁻¹ a')
  rw [←hbase] at base
  obtain ⟨q⟩ := base (p.act j⁻¹)
  have hcancel (v : Vertex d.radical) : act d.radical j (act d.radical j⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  exact edge_paired_backward_shift_of_vertices p ((p.act j⁻¹).act j)
    (hcancel a) (hcancel a') (by
      intro i
      simp only [CriticalPath.act,actWalk_getVert,hcancel]) (q.conjugate j)

include e hz hn in
/-- The original critical line misses the selected backward edge seed.
This uses the original and selected kernels together; a single endpoint
transposition is not asserted to generate the stabilizer. -/
theorem elementary_edge_paired_critical_line_disjoint_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p) :
    ⁅Z d.radical a,Z d.radical a'⁆ ⊓ Z d.radical q.edge = ⊥ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  let H := ⁅Z d.radical a,Z d.radical a'⁆
  have hfirst : H ≤ Z d.radical (p.walk.getVert 1) :=
    cube_critical_commutator_le_first_seed s hc u hR p
  have hcard : Nat.card H = 2 :=
    (SylowCritical.elementary_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p).2.2
  have hnc : ¬ H ≤ Z d.radical q.edge := by
    intro hh
    exact critical_commutator_not_central s hc p
      ((le_inf hfirst hh).trans q.edge_seed_intersection_central)
  let := finite_Z d.radical (p.walk.getVert 1)
  let : Finite H := Finite.of_injective (inclusion hfirst) (inclusion_injective _)
  let : Finite (H ⊓ Z d.radical q.edge : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  by_contra hne
  have hp := (one_lt_card_iff_ne_bot (H ⊓ Z d.radical q.edge)).mpr hne
  have he : H ⊓ Z d.radical q.edge = H := eq_of_le_of_card_ge inf_le_left (by omega)
  exact hnc (he ▸ inf_le_right)

include e hz hn in
/-- Successive selected critical lines are independent in the same full
seed, and their join has order four on both central covers. -/
theorem elementary_edge_paired_critical_plane_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p) :
    let H := ⁅Z d.radical a,Z d.radical a'⁆
    let K := ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆
    H ⊓ K = ⊥ ∧ H ⊔ K ≤ Z d.radical a ∧ Nat.card (H ⊔ K : Subgroup (FreeAmalgam d.radical)) = 4 := by
  let H := ⁅Z d.radical a,Z d.radical a'⁆
  let K := ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆
  have hs := SylowCritical.elementary_paired_shift_commutator_knownSimple (e := e) (hz := hz) (hn := hn)
    hb hEimage p q.toPairedBackwardShift
  have hHZ : H ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans (DistanceEight.U_le_Z d.radical a)
  have hKZ : K ≤ Z d.radical a := hs.2.2.1
  have hdis : H ⊓ K = ⊥ := by
    apply bot_unique
    exact (inf_le_inf_left H hs.2.1).trans_eq
      (elementary_edge_paired_critical_line_disjoint_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p q)
  have hHK : K ≤ centralizer (H : Set (FreeAmalgam d.radical)) := by
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
    exact (hKZ.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)).trans (centralizer_le hHZ)
  have hcH : Nat.card H = 2 :=
    (SylowCritical.elementary_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p).2.2
  have hcK : Nat.card K = 2 := hs.1
  refine ⟨hdis,sup_le hHZ hKZ,?_⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint H K
    (hHK.trans (Subgroup.centralizer_le_normalizer (H : Set (FreeAmalgam d.radical)))) (disjoint_iff.mpr hdis),hcH,hcK]

include e hz hn in
/-- The source R₄/R₆ configuration now has an actual four-group in the
centralizer of the common endpoint radius, with both original-edge joins
retained. This does not assert intermediate-stabilizer noncentrality. -/
theorem elementary_edge_paired_terminal_plane_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ q : EdgePairedBackwardShift (h := h) p,
      ∃ r : EdgePairedBackwardShift (h := h) q.path,
        ∃ t : EdgePairedBackwardShift (h := h) r.path,
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          let z₆ := r.path.walk.getVert (r.path.walk.length-2)
          let R₄ := ⁅Z d.radical r.start,Z d.radical z₄⁆
          let R₆ := ⁅Z d.radical t.start,Z d.radical z₆⁆
          R₄ ⊓ R₆ = ⊥ ∧ Nat.card (R₄ ⊔ R₆ : Subgroup (FreeAmalgam d.radical)) = 4 ∧
          R₄ ⊔ R₆ ≤ Z d.radical r.start ⊓
            centralizer (V d.radical z₄ : Set (FreeAmalgam d.radical)) := by
  obtain ⟨q⟩ := elementary_edge_paired_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p
  obtain ⟨r⟩ := elementary_edge_paired_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage q.path
  obtain ⟨t⟩ := elementary_edge_paired_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage r.path
  have hp := elementary_edge_paired_critical_plane_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage r.path t
  have ht := SylowCritical.elementary_paired_shift_commutator_knownSimple (e := e) (hz := hz) (hn := hn)
    hb hEimage r.path t.toPairedBackwardShift
  have hR₄Z : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) :=
    ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans (DistanceEight.U_le_Z d.radical _)
  have hR₄V := (hR₄Z.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical _ r.path.end_color))).trans
    (centralizer_le (V_le_Q d.radical (geometry := replacementGeometry h d) r.path.end_color
      (by change 2 < replacementDistance h d; omega)))
  exact ⟨q,r,t,hp.1,hp.2.2,le_inf hp.2.1 (sup_le hR₄V ht.2.2.2.2.1)⟩


end SylowTerminal
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
