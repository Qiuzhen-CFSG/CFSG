module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementarySmallCommonKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementarySmallGenerationConsumer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.NonnormalSelection

/-!
# The second backward kernel in the cube branch

Two backward critical paths with the same midpoint give two actors normalizing
one second backward kernel.  Strict seed intersections and the first
transporters supply the central triples needed for this normalization.  The
compatible incident edge and the two actors generate the whole stabilizer,
so the normalized small section lies in the Baumann subgroup.  This contradicts
the strict slice, whether the selected seed is trapped or gives a critical path.

Source: Meierfrankenfeld--Stellmacher (1993), (5.12)(1),(3), pp.924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- Both endpoint actors normalize the same second backward kernel, which
forces the selected strict slice to be small. -/
theorem cube_paired_second_backward_strict_false
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a c v w t t' : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c v)
    (r : CriticalPath d.radical (replacementGeometry h d) c w)
    (hq2 : q.walk.getVert 2 = a) (hr2 : r.walk.getVert 2 = a)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hct' : Adjacent d.radical c t')
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (hfirst : Q d.radical t ⊔ Q d.radical t' = stabilizer d.radical c)
    (hactors : Q d.radical t' ⊔ Z d.radical v ⊔ Z d.radical w = stabilizer d.radical c)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgv : act d.radical g v = c)
    (k : FreeAmalgam d.radical) (hk : k ∈ stabilizer d.radical a)
    (hkw : act d.radical k w = c)
    (htripleV : Z d.radical c ⊓ Z d.radical a ⊓ Z d.radical v ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (htripleW : Z d.radical c ⊓ Z d.radical a ⊓ Z d.radical w ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have ha : color d.radical a = false := by
    rw [←hq2]
    exact (q.vertex_color (by omega)).mpr (by decide)
  obtain ⟨j,hj,hja⟩ := stabilizer_transitive_neighbors d.radical t
    (adjacent_symm d.radical hat) (adjacent_symm d.radical hct)
  have hjt : act d.radical j t = t := hj
  have hdelta : Adjacent d.radical (act d.radical j c) t := by
    simpa only [hjt] using (adjacent_act_iff d.radical j _ _).mpr hct
  have hdeltaStrict : 2 < (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical j c)) := by
    have hi : 2 < (B d.radical (act d.radical j a)
        ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical j c)) := by
      rw [Escape.PairingControl.FirstPairing.B_act hb2 j a ha,U_act,
        relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
      exact hstrict
    simpa only [hja] using hi
  obtain ⟨l,hl,hlt⟩ := stabilizer_transitive_neighbors d.radical c hct hct'
  let b := act d.radical l (act d.radical j c)
  have hbt' : Adjacent d.radical b t' := by
    rw [←hlt]
    exact (adjacent_act_iff d.radical l _ _).mpr hdelta
  have hbcol : color d.radical b = false := by
    simpa only [b,action_preserves_color] using q.start_color
  have hbstrict : 2 < (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical b) := by
    have hBl := Escape.PairingControl.FirstPairing.B_act
      (geometry := replacementGeometry h d) hb2 l c q.start_color
    rw [show act d.radical l c = c from hl] at hBl
    change 2 < (B d.radical c _).relIndex (U d.radical (act d.radical l _))
    rw [hBl,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hdeltaStrict
  have hbc : (cosetGraph d.radical).dist b c ≤ 2 := by
    have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hbt')
    have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hct'))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := b) (v := t') (w := c)
  have hAc := cube_strict_seed_intersection_eq_edge s hb2 u hfull ha hat hct hstrict
  have hBc := cube_strict_seed_intersection_eq_edge s hb2 u hfull q.start_color hct' hbt' hbstrict
  have hedgeCent {t₀ : Vertex d.radical} (hc₀ : Adjacent d.radical c t₀) :
      Z d.radical t₀ ≤ centralizer (Q d.radical t₀ : Set (FreeAmalgam d.radical)) := by
    have ht₀ : color d.radical t₀ = true := by
      have hh := adjacent_color_ne d.radical hc₀
      rw [q.start_color] at hh
      exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
    intro x hx
    rw [Z,if_neg (by simp [ht₀])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have htripleB : Z d.radical b ⊓ Z d.radical c ⊓ Z d.radical a ≤
      centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←hfirst]
    apply sup_le
    · apply le_centralizer_iff.mp
      exact (le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans
        (hAc.le.trans (hedgeCent hct))
    · apply le_centralizer_iff.mp
      exact (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)).trans
        (hBc.le.trans (hedgeCent hct'))
  have hnormV := cube_two_strict_triples_normalize s hc hb u hfull q hq2
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q)
    hbc hbcol g hg hgv htripleV htripleB
  have hnormW := cube_two_strict_triples_normalize s hc hb u hfull r hr2
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb r)
    hbc hbcol k hk hkw htripleW htripleB
  have hel : IsElementaryAbelian 2 (d.radical.map s.projection) := by
    let : IsElementaryAbelian 2 (D 6) := elementary_disjointTranspositions (3 : Fin 4)
    rw [hfull]
    exact IsElementaryAbelian.map _
  by_cases htrapped : Z d.radical b ≤ Q d.radical a
  · have hnorm : Z d.radical v ⊔ Z d.radical w ≤ normalizer
        ((Z d.radical b ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      simpa only [inf_eq_left.mpr htrapped] using sup_le hnormV hnormW
    have hcore : Q d.radical t' ≤ normalizer
        ((Z d.radical b ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) :=
      (le_inf
        ((show Q d.radical t' ≤ stabilizer d.radical b from
          fun _ hx => hx.2 _ (adjacent_symm d.radical hbt')).trans (Z_normalized d.radical b))
        ((show Q d.radical t' ≤ stabilizer d.radical c from
          fun _ hx => hx.2 _ (adjacent_symm d.radical hct')).trans (Z_normalized d.radical c))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hres : Ltilde d.radical c ≤ normalizer
        ((Z d.radical b ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      apply (Ltilde_le_stabilizer _).trans
      rw [←hactors,sup_assoc]
      exact sup_le hcore hnorm
    have hYV : Z d.radical b ⊔ Z d.radical c ≤ V d.radical c :=
      sup_le ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hbc))
        (Z_le_VBall d.radical _ 2)
    have hYB := residual_small_radius_le_slice_knownSimple (e := e) hb2 q.start_color
      (Z d.radical b ⊔ Z d.radical c) hYV hres
      (DistanceFour.adjacent_seed_span_index_le_eight
        (e := e) (hz := hz) (hn := hn) hb2 q.start_color hct' hbt')
    have hone := relIndex_eq_one.mpr ((DistanceEight.U_le_Z d.radical b).trans
      (le_sup_left.trans hYB))
    omega
  · obtain ⟨v',hv'1,hv'2⟩ : ∃ v' : CriticalPath d.radical (replacementGeometry h d) b a,
        v'.walk.getVert 1 = t' ∧ v'.walk.getVert 2 = c := by
      let path : (cosetGraph d.radical).Walk b c :=
        .cons ((cosetGraph_adj d.radical _ _).mpr hbt')
          (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hct')) .nil)
      have hpath : path.length = 2 := rfl
      have hescape : ¬ Z d.radical b ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
        simpa only [hql,show 4-2=2 from rfl,hq2] using htrapped
      let v' := q.prepend_two (Nat.le_of_lt hb2) hbcol path hpath hescape
      have hh : ∃ v' : CriticalPath d.radical (replacementGeometry h d) b
          (q.walk.getVert (q.walk.length-2)), v'.walk.getVert 1 = t' ∧ v'.walk.getVert 2 = c := by
        refine ⟨v',?_,?_⟩
        · simp only [v',CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
            hpath,show 1<2 from by decide,ite_true,path,SimpleGraph.Walk.getVert_cons_succ,
            SimpleGraph.Walk.getVert_zero]
        · simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
            q.prepend_two_overlap (Nat.le_of_lt hb2) hbcol path hpath hescape (i := 0) (by omega)
      rw [show q.walk.length-2=2 by omega,hq2] at hh
      exact hh
    have hres : Ltilde d.radical (v'.walk.getVert 2) ≤ Q d.radical (v'.walk.getVert 1) ⊔
        (Z d.radical v ⊔ Z d.radical w) := by
      rw [hv'1,hv'2,←sup_assoc,hactors]
      exact Ltilde_le_stabilizer _
    have hle := elementary_small_normalized_slice_le_two s hc hb hel v'
      (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb v')
      (Z d.radical v ⊔ Z d.radical w) hres (by simpa only [hv'2] using sup_le hnormV hnormW)
    rw [hv'2] at hle
    omega

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
