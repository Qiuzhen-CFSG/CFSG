module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowActor
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeCommonFixer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePredecessorSlice
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeCommonFixer

/-!
# Small critical shifts with a Sylow original radical

A replacement whose literal symmetric-six image is the full three-pair
group admits the simultaneous two-kernel selection at every distance above
two. The selection needs no nonsylow hypothesis on the original MS radical.
If both seed candidates were trapped in their predecessor cores, their
commutator lines would be fixed by the two selected kernels, which generate
the whole starting stabilizer. The retained nonnormalization witness
contradicts this. Reversing the auxiliary cubic when needed gives a backward
critical walk of the original path, with every common vertex preserved.

Above distance four, an elementary replacement image is necessarily this
full three-pair group. Indeed, the original-Sylow restriction forces order
at least eight, the elementary catalogue places it in a cube or a point
core of order eight, and the full point-core distance bound excludes the
second possibility. This discharges the marked image in the small shift.
Combining with SylowActor handles both critical-image sizes, retaining the
starting and edge transporters, their relative-normalizer representative,
pointwise agreement on the entire edge kernel, and the exact Baumann index.

The actual trapped-radius consumer consequently bounds every two-edge
slice by two and identifies each full predecessor kernel. Its commutator
with the predecessor core has order at most four and is centralized by the
whole predecessor stabilizer. Both moving covers, all central attachments,
the minimum characteristic replacement and the original natural graph are
retained; the original radical is never identified with its replacement.

The strict-slice premise in the backward selection, non-elementary images,
the terminal original-Sylow exclusion and the remaining distance-four
estimates still require their source arguments. This module does not prove
LargeDistanceInput or unconditional replacement distance two.

The intentional `import all` coupling reuses the internal small-section,
product-index and inverse-kernel lemmas of CubeCommonFixer in this extension,
without changing that module's public boundary.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3), (5.6)--(5.8) and Section 7, printed pp.866--867,917--920,
932--933; Aschbacher--Smith B.3.2--4 and C.1.31, printed pp.83--85,135.
The proof extends the existing CubeCommonFixer, CubeStrictBackward and
CubePredecessorSlice arguments to the actual original-Sylow branches.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace SylowSmall
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "S" => Equiv.Perm (Fin 6)

private theorem small_common_fixer_paired_seed
    (hb : 2 < replacementDistance h d) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
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
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t,hat,v,hparabolic,x,hxL,hxN,hx3,hgen⟩ := small_cube_common_fixer_neighbor s hc u hfull' p hsmall
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
    (normal_small_radius_le_slice s hb Y hYV hYN
      ((cube_backward_product_index s u hfull' hat hct).trans (by decide))))


/-- Simultaneously select the cubic, two generating edge kernels and two
critical seed candidates. A strict slice makes at least one candidate yield
an actual backward critical walk. Both full central covers are retained. -/
theorem cube_small_backward_selection_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
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
    small_common_fixer_paired_seed (e := e) (hz := hz) (hn := hn)
      hb u hfull p hsmall hdelta hel
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
      let s := fullSymmetricAction_knownSimple h e hz hn d hb
      have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
      have hf : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
        rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
      have hxG : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hx
      rcases hnorm with hnp | hnq
      · exact cube_common_fixer_excludes_trapped_pair s hc hb u hf p hsmall hat hct
          x hxG q hq hqs hgen hxN hpbad hqbad hstrict hnp
      · have hgen' : Q d.radical t ⊔ Z d.radical (act d.radical x a') ⊔ Z d.radical a' =
            stabilizer d.radical (alpha d.radical) := by
          calc
            _ = Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') := by ac_rfl
            _ = _ := hgen
        have hqback (i : ℕ) : p.walk.getVert i = act d.radical x⁻¹ (q.walk.getVert i) := by
          rw [hq,←act_mul,mul_inv_cancel,act_one]
        exact cube_common_fixer_excludes_trapped_pair s hc hb u hf q hqs hat hct
          x⁻¹ ((stabilizer d.radical (alpha d.radical)).inv_mem hxG) p hqback hsmall hgen'
          (reverse_generating_pair _ _ x hxG hxN) hqbad hpbad hstrict hnq
    · exact Or.inr (hpath q hqbad)
  · exact Or.inl (hpath p hpbad)
/-- A strict small-image backward shift for any full three-pair replacement.
The original MS radical may be Sylow. The returned walk belongs to the
original path, after reversing the auxiliary cubic if necessary. -/
theorem cube_small_backward_path_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ v : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
            (p.walk.getVert (p.walk.length-2)),
          v.walk.getVert 1=t ∧
          ∀ i ≤ p.walk.length-2, v.walk.getVert (i+2)=p.walk.getVert i := by
  have strict (g : FreeAmalgam d.radical)
      (hg : g ∈ stabilizer d.radical (alpha d.radical)) :
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (act d.radical g delta)) := by
    have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        hb (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hindex
  obtain ⟨t,hat,g,hg,hgt,_,_,x,hx,_,_,q,hq,_,_,halt⟩ :=
    cube_small_backward_selection_knownSimple (e := e) (hz := hz) (hn := hn)
      hb u hfull p hsmall hdelta hindex
  rcases halt with ⟨v,hvt,hover⟩ | ⟨v,hvt,hover⟩
  · exact ⟨t,hat,g,hg,hgt,strict g hg,v,hvt,hover⟩
  · let y := g*x⁻¹
    have hy : y ∈ stabilizer d.radical (alpha d.radical) :=
      mul_mem hg (inv_mem (Ltilde_le_stabilizer _ hx))
    have hxfix : act d.radical x⁻¹ (alpha d.radical) = alpha d.radical :=
      (stabilizer d.radical (alpha d.radical)).inv_mem (Ltilde_le_stabilizer _ hx)
    have hat' : Adjacent d.radical (alpha d.radical) (act d.radical x⁻¹ t) := by
      rw [←hxfix]
      exact (adjacent_act_iff d.radical x⁻¹ _ _).mpr hat
    have hyt : act d.radical y (p.walk.getVert 1) = act d.radical x⁻¹ t := by
      rw [show y=g*x⁻¹ from rfl,act_mul,hgt]
    refine ⟨act d.radical x⁻¹ t,hat',y,hy,hyt,strict y hy,?_⟩
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    have hend : act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := by
      rw [hlen,hq,←act_mul,mul_inv_cancel,act_one]
    have hstart : act d.radical x⁻¹ (act d.radical g delta) = act d.radical y delta :=
      (act_mul d.radical g x⁻¹ delta).symm
    have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical x⁻¹ (act d.radical g delta))
        (act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2))),
        w.walk.getVert 1=act d.radical x⁻¹ t ∧
        ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
      refine ⟨v.act x⁻¹,?_,?_⟩
      · simp only [CriticalPath.act,actWalk_getVert,hvt]
      · intro i hi
        have hiq : i ≤ q.walk.length-2 := hlen.symm ▸ hi
        simp only [CriticalPath.act,actWalk_getVert,hover i hiq,hq,
          ←act_mul,mul_inv_cancel,act_one]
    rwa [hstart,hend] at hex



/-- Transport the full three-pair small-image shift to every original vertex. -/
theorem cube_small_backward_path_at_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical a t ∧
      ∃ g ∈ stabilizer d.radical a,
        act d.radical g (p.walk.getVert 1) = t ∧
        2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ v : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
            (p.walk.getVert (p.walk.length-2)),
          v.walk.getVert 1=t ∧
          ∀ i ≤ p.walk.length-2, v.walk.getVert (i+2)=p.walk.getVert i := by
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := cube_small_backward_path_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u hfull
    (a' := act d.radical j⁻¹ a') (delta := act d.radical j⁻¹ delta)
  rw [←hbase] at base
  have hdelta0 : Adjacent d.radical (act d.radical j⁻¹ delta)
      ((p.act j⁻¹).walk.getVert 1) := by
    simpa only [CriticalPath.act,actWalk_getVert] using
      (adjacent_act_iff d.radical j⁻¹ _ _).mpr hdelta
  have hindex0 : 2 < (B d.radical (act d.radical j⁻¹ a)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical j⁻¹ delta)) := by
    rw [Escape.PairingControl.FirstPairing.B_act hb j⁻¹ a p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hindex
  have hsmall0 : (Q d.radical (act d.radical j⁻¹ a')).relIndex
      (Z d.radical (act d.radical j⁻¹ a)) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hsmall
  obtain ⟨t,hat,k,hk,hkt,_,v,hvt,hover⟩ := base (p.act j⁻¹) hsmall0 hdelta0 hindex0
  have hcancel (z : Vertex d.radical) : act d.radical j (act d.radical j⁻¹ z) = z := by
    rw [←act_mul,inv_mul_cancel,act_one]
  let y := j⁻¹*k*j
  have hact (z : Vertex d.radical) : act d.radical j (act d.radical k (act d.radical j⁻¹ z)) =
      act d.radical y z := by simp only [←act_mul,y,mul_assoc]
  have hy : y ∈ stabilizer d.radical a := by
    change act d.radical y a = a
    rw [←hact]
    rw [show act d.radical k (act d.radical j⁻¹ a)=act d.radical j⁻¹ a from hk,hcancel]
  have hB : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj y⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb a p.start_color ((stabilizer d.radical a).inv_mem hy))
  have hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical y delta)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hindex
  refine ⟨act d.radical j t,?_,y,hy,?_,hstrict,?_⟩
  · simpa only [hcancel] using (adjacent_act_iff d.radical j _ _).mpr hat
  · have he := congrArg (act d.radical j) hkt
    simpa only [CriticalPath.act,actWalk_getVert,hact] using he
  · have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical j (act d.radical k (act d.radical j⁻¹ delta)))
        (act d.radical j ((p.act j⁻¹).walk.getVert ((p.act j⁻¹).walk.length-2))),
        w.walk.getVert 1=act d.radical j t ∧
        ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
      refine ⟨v.act j,?_,?_⟩
      · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical j) hvt
      · intro i hi
        have he := congrArg (act d.radical j) (hover i (by
          simpa only [CriticalPath.act,actWalk_length] using hi))
        simpa only [CriticalPath.act,actWalk_getVert,hcancel] using he
    have hend : act d.radical j ((p.act j⁻¹).walk.getVert ((p.act j⁻¹).walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := by
      simp only [CriticalPath.act,actWalk_length,actWalk_getVert,hcancel]
    rwa [hact,hend] at hex

/-- Above distance four, an elementary replacement image is the full
three-pair group, even when the original MS radical is Sylow. The already
proved four-image and full-point exclusions remove every smaller alternative. -/
theorem four_lt_elementary_image_cube_knownSimple
    (hb : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d))) :
    ∃ u : S, d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom := by
  let A := d.radical.map (SourceReduction.projection h e hz hn d)
  have hlarge : 8 ≤ Nat.card A := by
    rcases (MixedExclusion.four_lt_original_sylow_large_image_knownSimple
      (e := e) (hz := hz) (hn := hn) hb).2 with ⟨_,h16⟩ | ⟨_,h8⟩
    · change Nat.card A = 16 at h16
      omega
    · change Nat.card A = 8 at h8
      omega
  have he : Representation.BinaryOffender.IsElementaryTwo A := ⟨by
    intro hz
    rw [hz,card_bot] at hlarge
    omega,hel⟩
  obtain ⟨B,hB,hBD | hBE,hAB⟩ := exists_conjugate_le_D_or_exceptional he
  · have hDcard : Nat.card (D 6) = 8 := card_disjointTranspositions (3 : Fin 4)
    have hBfull : B = D 6 := eq_of_le_of_card_ge hBD (by
      rw [hDcard,←hAB.card_eq]
      exact hlarge)
    obtain ⟨u,hu⟩ := hAB
    exact ⟨u,hu.trans (congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) hBfull)⟩
  · have hBfull : B = exceptional 6 (by decide) := eq_of_le_of_card_ge hBE (by
      rw [card_exceptional,←hAB.card_eq]
      exact hlarge)
    obtain ⟨u,hu⟩ := hAB
    have hf : d.radical.map (SourceReduction.projection h e hz hn d) =
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
      change A = _
      rw [hu,hBfull,CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional]
    exact (Nat.not_le_of_gt hb (full_point_distance_le_four_knownSimple u hf)).elim

/-- The actual elementary-image branch supplies the small-image shift
without either a nonsylow premise or a chosen quotient conjugator. -/
theorem elementary_small_backward_path_knownSimple
    (hb : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical a t ∧
      ∃ g ∈ stabilizer d.radical a,
        act d.radical g (p.walk.getVert 1) = t ∧
        2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  obtain ⟨u,hu⟩ := four_lt_elementary_image_cube_knownSimple hb hel
  exact cube_small_backward_path_at_knownSimple (by omega) u hu p hsmall hdelta hindex

/-- Every strict backward slice in the elementary-image branch gives a
critical shift, in both critical-image sizes. The starting and edge actors
remain separate and agree with the relative-normalizer actor on the entire
edge kernel. The exact original Baumann index is preserved. -/
theorem elementary_strict_backward_shift_knownSimple
    (hb : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical a t ∧
      ∃ x ∈ stabilizer d.radical a,
        act d.radical x (p.walk.getVert 1) = t ∧
        ∃ k ∈ stabilizer d.radical t,
          ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
              stabilizer d.radical a,
            (∀ v ∈ Q d.radical t, (MulAut.conj k⁻¹) v = (MulAut.conj g) v) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (act d.radical k (act d.radical x delta))
              (p.walk.getVert (p.walk.length-2)),
            q.walk.getVert 1 = t ∧
            (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
                (U d.radical (act d.radical k (act d.radical x delta))) =
              (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
                (U d.radical delta) := by
  have hb2 : 2 < replacementDistance h d := by omega
  by_cases hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)
  · obtain ⟨P,hP⟩ := (MixedExclusion.four_lt_original_sylow_large_image_knownSimple
      (e := e) (hz := hz) (hn := hn) hb).1
    have he : ¬ U d.radical delta ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
      intro hh
      have hi := relIndex_eq_one.mpr hh
      omega
    obtain ⟨t,hat,_,x,hx,hxt,k,hk,g,hg,hagree,q,hqt,hover,hi⟩ :=
      SylowActor.large_image_backward_shift_at_knownSimple
        (e := e) (hz := hz) (hn := hn) hb2 P hP p hlarge hdelta he
    exact ⟨t,hat,x,hx,hxt,k,hk,g,hg,hagree,q,hqt,hover,hi⟩
  · obtain ⟨t,hat,x,hx,hxt,_,q,hqt,hover⟩ :=
      elementary_small_backward_path_knownSimple hb hel p (by omega) hdelta hindex
    refine ⟨t,hat,x,hx,hxt,1,one_mem _,1,one_mem _,?_,?_⟩
    · intro v _
      simp only [inv_one,MulAut.conj_apply,one_mul,mul_one]
    · rw [act_one]
      refine ⟨q,hqt,hover,?_⟩
      have hB : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
          (MulAut.conj x⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
        mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
          hb2 a p.start_color ((stabilizer d.radical a).inv_mem hx))
      rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective,hB]

/-- A trapped radius bounds every two-edge slice by two in the elementary
replacement-image branch, including when the original radical is Sylow. -/
theorem elementary_trapped_radius_all_slices_le_two_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a₀ a₁ : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ a₁)
    (hbad : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a c t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ≤ 2 := by
  have hb : 2 < replacementDistance h d := by omega
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha₀t : Adjacent d.radical a₀ (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hbase {c t : Vertex d.radical}
      (hat : Adjacent d.radical a₀ t) (hct : Adjacent d.radical c t) :
      (B d.radical a₀ ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ≤ 2 := by
    by_contra! hindex
    obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical a₀ hat ha₀t
    have hcgt : Adjacent d.radical (act d.radical g c) (p.walk.getVert 1) := by
      rw [←hgt]
      exact (adjacent_act_iff d.radical g c t).mpr hct
    have hB : (B d.radical a₀ ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj g⁻¹).toMonoidHom = B d.radical a₀ ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        hb a₀ p.start_color ((stabilizer d.radical a₀).inv_mem hg))
    have hindexg : 2 < (B d.radical a₀ ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (act d.radical g c)) := by
      rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      exact hindex
    obtain ⟨v,hav,x,hx,hxt,k,hk,_,_,_,q,_,_⟩ :=
      elementary_strict_backward_shift_knownSimple hb4 hel p hcgt hindexg
    have hkv : Adjacent d.radical (act d.radical k (act d.radical x (act d.radical g c))) v := by
      have hfix : act d.radical k v = v := hk
      rw [←hfix]
      apply (adjacent_act_iff d.radical k _ _).mpr
      rw [←hxt]
      exact (adjacent_act_iff d.radical x _ _).mpr hcgt
    have hd : (cosetGraph d.radical).dist (act d.radical k (act d.radical x (act d.radical g c))) a₀ ≤ 2 := by
      have h1 : (cosetGraph d.radical).dist (act d.radical k (act d.radical x (act d.radical g c))) v=1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hkv)
      have h2 : (cosetGraph d.radical).dist v a₀=1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr
          (adjacent_symm d.radical hav))
      simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
        (u := act d.radical k (act d.radical x (act d.radical g c))) (v := v) (w := a₀)
    exact q.critical.2 (((Z_le_localZSpan d.radical _ _).trans
      (localZSpan_le_V d.radical hd)).trans hbad)
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical ha
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  let y := g⁻¹*j
  have hya : act d.radical y a=a₀ := by
    rw [hg,hj,act_mVertex]
    simp only [y,mul_inv_cancel_left]
  have hyt : Adjacent d.radical a₀ (act d.radical y t) := by
    rw [←hya]
    exact (adjacent_act_iff d.radical y _ _).mpr hat
  have hh := hbase hyt ((adjacent_act_iff d.radical y _ _).mpr hct)
  rw [←hya,Escape.PairingControl.FirstPairing.B_act hb y a ha,U_act,
    relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective] at hh
  exact hh

include e hz hn in
/-- A trapped elementary-image radius identifies every predecessor slice with the full reverse
critical kernel. Its core commutator is central in the entire predecessor
stabilizer, with no assumed slice bound or critical-image estimate. -/
theorem elementary_trapped_radius_predecessor_kernels_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a₀ a₁ : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ a₁)
    (hbad : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a a' : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a a') :
    let c := q.walk.getVert (q.walk.length-2)
    let K := Z d.radical a' ⊓ Q d.radical a
    let N := ⁅K,Q d.radical c⁆
    Z d.radical a' ⊓ B d.radical c ((replacementGeometry h d).Z_normal _) = K ∧
      (Q d.radical a').relIndex (Z d.radical a)=2 ∧
      (Q d.radical a).relIndex (Z d.radical a')=2 ∧
      Nat.card N ≤ 4 ∧ N ≤ Z d.radical (q.walk.getVert (q.walk.length-1)) ∧
      N ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hu⟩ := four_lt_elementary_image_cube_knownSimple hb4 hel
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hu]
  have hl : 2 < q.walk.length := q.length_eq_b ▸ hb
  have hcol : color d.radical (q.walk.getVert (q.walk.length-2))=false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  have hct : Adjacent d.radical (q.walk.getVert (q.walk.length-2))
      (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-2) (by omega)
    rw [show q.walk.length-2+1=q.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have het : Adjacent d.radical a' (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-1) (by omega)
    rw [show q.walk.length-1+1=q.walk.length by omega,q.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hindex := elementary_trapped_radius_all_slices_le_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hel p hbad hcol hct het
  have hs := critical_predecessor_slice_eq_kernel s hc hb q hindex
  exact ⟨hs.1,hs.2.1,hs.2.2,cube_predecessor_slice_commutator_central s hc hb u hR q hindex⟩


end SylowSmall
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
