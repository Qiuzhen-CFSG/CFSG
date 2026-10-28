module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel
public import Theory.GroupTheory.SmallMoverFamily

/-!
# The source small-mover groups on the same shifted edge

The maximum-order family in MS93 (5.0) uses the two literal indices
|U:C_U(E)| and |E:E intersect Q|, with the former at most q squared.
We use `Subgroup.SmallMover` for that family, retaining its unrestricted
subgroups E and its maximum-order condition. In the three-pair branch,
the entire incident radical has image order eight and fixed index at most
four on either moved cover. It is therefore the unique maximum, so the
source small-mover join equals that actual radical at both component
vertices incident to any edge. The ordinary Thompson subgroup remains a
distinct object.

Apply these equalities to the source R₃ from `CubeFullKernel`. The same
selected x and original component element y determine a two-edge path
from the shifted seed to the starting vertex. Its full kernel A₀ lies in
the actual common edge radical. The three-pair quadratic action puts R₃
in that edge's central omega subgroup; consequently both literal source
small-mover joins centralize R₃. The original forward critical path,
overlap, selected span, both centralizer spans, full-X central summands,
critical commutator and both moved covers are preserved.

This proves the source small-mover comparison and its selected-line
application. Independence from the choice of y, centrality under the whole
starting stabilizer, the remaining span comparison and strict forward
bound in (5.9) remain to be established. The terminal, Sylow and distance-four
branches and unconditional large-distance exclusion remain with this owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), definitions (5.0), printed p.912, and the two small-mover cases in
(5.9), printed p.921. All radicals and maps are those of the natural minimum
characteristic replacement; the original radical is not assumed Sylow.
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


private theorem maximal_singleton_of_radical_admissible {F : Type*} [Group F]
    (U Q T : Subgroup F) [Finite T] (n : ℕ)
    (hT : SmallMover.Admissible U Q T n T) :
    SmallMover.Maximal U Q T n = {T} := by
  ext E
  constructor
  · intro hE
    exact Set.mem_singleton_iff.mpr (eq_of_le_of_card_ge hE.1.1 (hE.2 T hT))
  · rintro rfl
    exact ⟨hT,fun F hF => card_le_of_le hF.1⟩

include s in
/-- The actual edge radical itself satisfies the source (5.0) inequalities:
its image has order eight and its fixed index on the full moving cover is
at most four. The two cover orders and all central attachments are retained. -/
theorem cube_edge_radical_small_mover
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection =
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    (Q d.radical a).relIndex (Q d.radical t) = 8 ∧
      (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ 4 ∧
      SmallMover.Admissible (U d.radical a) (Q d.radical a) (Q d.radical t) 4
        (Q d.radical t) := by
  have hbase : (Q d.radical (alpha d.radical)).relIndex
      (Q d.radical (beta d.radical)) = 8 := by
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d),Q_beta,
      relIndex_map_map_of_injective _ _ (embedM_injective d.radical),
      ←s.projection_kernel,relIndex_ker,hfull,
      card_map_of_injective (MulAut.conj u).injective]
    exact CFSG.Quasithin.ChapterB.Offenders.Six.card_disjointTranspositions 3
  have himage : (Q d.radical a).relIndex (Q d.radical t) = 8 := by
    obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
    · rcases hg with ⟨rfl,rfl⟩
      have he := relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (Q d.radical (alpha d.radical)) (Q d.radical (beta d.radical))
        (MulAut.conj g⁻¹).injective
      rw [←Q_act,←Q_act] at he
      simp only [alpha,beta,act_mVertex,act_hVertex,one_mul] at he
      exact he.trans hbase
    · rw [hg.1] at ha
      cases ha
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases he : color d.radical t <;> simp_all
  have hfixed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  have hindex : (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ 4 :=
    ((relIndex_le_of_le_left hfixed index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a) index_ne_zero_of_finite)).trans_eq
        (cube_edge_seed_index s u hfull ha hat)
  exact ⟨himage,hindex,le_rfl,by rw [himage]; omega,hindex⟩

include s in
/-- In the three-pair branch the literal source maximum-small-mover family
on every incident edge is a singleton. Its join is the full edge radical;
this is not an identification with the ordinary Thompson subgroup. -/
theorem cube_edge_small_movers
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection =
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    SmallMover.Maximal (U d.radical a) (Q d.radical a) (Q d.radical t) 4 = {Q d.radical t} ∧
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4 = Q d.radical t := by
  let : Finite (stabilizer d.radical t) := finite_stabilizer d.radical t
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion (show Q d.radical t ≤ stabilizer d.radical t from fun _ hx => hx.1))
    (inclusion_injective _)
  have hs := maximal_singleton_of_radical_admissible (U d.radical a) (Q d.radical a)
    (Q d.radical t) 4 (cube_edge_radical_small_mover s u hfull ha hat).2.2
  exact ⟨hs,by rw [SmallMover.join,hs,sSup_singleton]⟩

include e hz hn in
/-- The nonsylow replacement supplies the radical image internally. The
source small-mover joins agree at both ends of every original two-edge path. -/
theorem nonsylow_paired_small_movers_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    SmallMover.Maximal (U d.radical a) (Q d.radical a) (Q d.radical t) 4 = {Q d.radical t} ∧
      SmallMover.Maximal (U d.radical c) (Q d.radical c) (Q d.radical t) 4 = {Q d.radical t} ∧
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4 = Q d.radical t ∧
      SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 = Q d.radical t := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega : 2 < replacementDistance h d)
  obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  have hfull : d.radical.map s.projection =
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [ha] at h1
    cases he : color d.radical t <;> cases hec : color d.radical c <;> simp_all
  have hA := cube_edge_small_movers s u hfull ha hat
  have hC := cube_edge_small_movers s u hfull hcol hct
  exact ⟨hA.1,hC.1,hA.2,hC.2⟩

include s in
private theorem shifted_edge_small_movers
    (hc : DistanceTwo.CentralLayer d) (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection =
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom)
    (hb : 4 < replacementDistance h d) {a' z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (y x : FreeAmalgam d.radical)
    (hy : y ∈ stabilizer d.radical (p.walk.getVert 2))
    (hx : x ∈ stabilizer d.radical (p.walk.getVert 2)) :
    let c := p.walk.getVert 2
    let a := act d.radical y⁻¹ (alpha d.radical)
    let w := act d.radical x⁻¹ a
    let t := act d.radical x⁻¹ (act d.radical y⁻¹ (p.walk.getVert 1))
    let A₀ := X d.radical z ⊓ Q d.radical c
    Adjacent d.radical w t ∧ Adjacent d.radical c t ∧
      SmallMover.join (U d.radical w) (Q d.radical w) (Q d.radical t) 4 = Q d.radical t ∧
      SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 = Q d.radical t ∧
      A₀ ≤ SmallMover.join (U d.radical w) (Q d.radical w) (Q d.radical t) 4 ∧
      ⁅Z d.radical w,A₀⁆ ≤ Z d.radical t ∧
      ⁅Z d.radical w,A₀⁆ ≤ centralizer
        ((SmallMover.join (U d.radical w) (Q d.radical w) (Q d.radical t) 4 ⊔
          SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 :
            Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert 2
  let a := act d.radical y⁻¹ (alpha d.radical)
  let w := act d.radical x⁻¹ a
  let t := act d.radical x⁻¹ (act d.radical y⁻¹ (p.walk.getVert 1))
  have hlen : 4 < p.walk.length := p.length_eq_b ▸ hb
  have hfirst : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    have hh := p.walk.adj_getVert_succ (i := 0) (by omega)
    rw [p.walk.getVert_zero] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hsecond : Adjacent d.radical c (p.walk.getVert 1) := by
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hyfix : act d.radical y⁻¹ c = c :=
    (stabilizer d.radical c).inv_mem hy
  have hxfix : act d.radical x⁻¹ c = c := (stabilizer d.radical c).inv_mem hx
  have hwt : Adjacent d.radical w t :=
    (adjacent_act_iff d.radical x⁻¹ _ _).mpr
      ((adjacent_act_iff d.radical y⁻¹ _ _).mpr hfirst)
  have hct : Adjacent d.radical c t := by
    have hh := (adjacent_act_iff d.radical x⁻¹ _ _).mpr
      ((adjacent_act_iff d.radical y⁻¹ _ _).mpr hsecond)
    simpa only [hyfix,hxfix] using hh
  have hw : color d.radical w = false := by
    simp only [w,a,action_preserves_color]
    rfl
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hwt
    rw [hw] at hh
    cases he : color d.radical t <;> simp_all
  have hcolc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hJw := (cube_edge_small_movers s u hR hw hwt).2
  have hJc := (cube_edge_small_movers s u hR hcolc hct).2
  have hAedge : X d.radical z ⊓ Q d.radical c ≤ Q d.radical t :=
    inf_le_right.trans (Q_le_adjacent_h d.radical ht hct)
  have hlineEdge : ⁅Z d.radical w,X d.radical z ⊓ Q d.radical c⁆ ≤ Z d.radical t :=
    (commutator_mono le_rfl hAedge).trans
      (cube_edge_seed_commutator_le s hc u hR.le hw hwt)
  have hedgeFixed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro v hv
    rw [Z,if_neg (by simp [ht])] at hv
    exact (mem_omegaCenter_iff.mp hv).2.2
  exact ⟨hwt,hct,hJw,hJc,hJw.symm ▸ hAedge,hlineEdge,
    by rw [hJw,hJc,sup_idem]; exact hlineEdge.trans hedgeFixed⟩

/-- The same full-X configuration identifies the two source small-mover
joins on the selected shifted edge, contains A₀ in them, and centralizes R₃
under both. The original paths, component element, spans and line generator
are retained. Whole-starting-stabilizer centrality is a separate obligation. -/
theorem nonsylow_small_shifted_source_movers_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
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
      (Q d.radical z).relIndex (Z d.radical c) = 2 ∧
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
        ¬ Z d.radical a ≤ B d.radical c ((replacementGeometry h d).Z_normal _) ∧
        let J := ⁅conjugateSpanBy (Z d.radical a) P,Z d.radical z ⊓ Q d.radical c⁆
        Nat.card J = 2 ∧ J ≤ Z d.radical c ⊓ Z d.radical z ∧
        J ≤ Z d.radical (q.walk.getVert (q.walk.length-1)) ∧ J ≠ H₂ ∧
        let D := conjugateSpanBy (Z d.radical a) P
        let A₀ := X d.radical z ⊓ Q d.radical c
        let R₃ := ⁅D,A₀⁆
        (∀ v : Vertex d.radical, color d.radical v = false →
          X d.radical v = U d.radical v ⊔
            (X d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical)))) ∧
        A₀ = (Z d.radical z ⊓ Q d.radical c) ⊔
          (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
        R₃ = J ∧ R₃ ≤ D ⊓ A₀ ∧
        (∃ x ∈ P,
          let w := act d.radical x⁻¹ a
          let t := act d.radical x⁻¹ (act d.radical y⁻¹ (p.walk.getVert 1))
          ⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,A₀⁆ = R₃ ∧
          Adjacent d.radical w t ∧ Adjacent d.radical c t ∧
          SmallMover.join (U d.radical w) (Q d.radical w) (Q d.radical t) 4 = Q d.radical t ∧
          SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 = Q d.radical t ∧
          A₀ ≤ SmallMover.join (U d.radical w) (Q d.radical w) (Q d.radical t) 4 ∧
          R₃ ≤ Z d.radical t ∧
          R₃ ≤ centralizer
            ((SmallMover.join (U d.radical w) (Q d.radical w) (Q d.radical t) 4 ⊔
              SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 :
                Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) ∧
        ⁅D,X d.radical z⁆ = ⁅D,Z d.radical z⁆ ∧
        ¬ ⁅D,X d.radical z⁆ ≤ R₃ ⊔ ⁅Z d.radical c,Z d.radical z⁆ ∧
        R₃ ≤ ⁅Z d.radical c,Z d.radical z⁆ ⊔
          (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨z,q,hd,hover,hpre,hi,y,hy,hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,hcard,hHCa,
    hcomm,hZaQ,hYQ,hDQ,hWQ,hZaV,hZaB,hJcard,hJseed,hJedge,hJne,
    hXall,hA₀,hR₃,hRDA,⟨x,hx,hline⟩,hfull,hnot,halign⟩ :=
    nonsylow_small_shifted_full_kernel_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hns p hslice hsmall
  obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  have hR : d.radical.map s.projection =
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨hwt,hct,hJw,hJc,hAedge,hlineEdge,hedgeFixed⟩ :=
    shifted_edge_small_movers s hc u hR hb (z := z) p y x
      (Ltilde_le_stabilizer _ hy) hx.1
  have he : ⁅Z d.radical (act d.radical x⁻¹ (act d.radical y⁻¹ (alpha d.radical))),
      X d.radical z ⊓ Q d.radical (p.walk.getVert 2)⁆ =
      ⁅conjugateSpanBy (Z d.radical (act d.radical y⁻¹ (alpha d.radical)))
        (stabilizer d.radical (p.walk.getVert 2) ⊓ centralizer
          ((⁅U d.radical (p.walk.getVert 2),Q d.radical (alpha d.radical) ⊓ centralizer
            (U d.radical (p.walk.getVert 2) ⊓ B d.radical (alpha d.radical)
              ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆ :
                Subgroup (FreeAmalgam d.radical)).map (MulAut.conj y).toMonoidHom :
                  Set (FreeAmalgam d.radical))),X d.radical z ⊓ Q d.radical (p.walk.getVert 2)⁆ := by
    simpa only [Z_act,inv_inv] using hline
  exact ⟨z,q,hd,hover,hpre,hi,y,hy,hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,hcard,hHCa,
    hcomm,hZaQ,hYQ,hDQ,hWQ,hZaV,hZaB,hJcard,hJseed,hJedge,hJne,
    hXall,hA₀,hR₃,hRDA,⟨x,hx,hline,hwt,hct,hJw,hJc,hAedge,
      he.symm.le.trans hlineEdge,he.symm.le.trans hedgeFixed⟩,hfull,hnot,halign⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
