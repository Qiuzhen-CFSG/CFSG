module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedStrict
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeLargeShift

/-!
# Large critical images and strict slices for the mixed replacement

Two mixed four-groups in the marked six-point quotient generate S₆: their
transpositions and double transpositions yield the five star transpositions.
A large critical image fills the mixed group on its first edge. Lifting the
explicit conjugate generation through the actual quotient kernel therefore
supplies an edge kernel which generates the starting stabilizer together
with the critical endpoint. This is stronger than relative-normalizer
generation and is used only in this large-image branch.

The controlled backward shift then has small critical image. A second large
shift would contradict the three-pair quadratic-action terminal calculation,
applied on this same natural graph using containment of the mixed group in
the three-pair group. It follows that all eligible first-edge slices of a
large critical pair have index at most two. Transporting the strict slice
of its small backward pair to that edge contradicts this bound.

Consequently every critical image above distance four has order two, every
forward slice is strict, and every predecessor radius has exactly the same
image, commutator and full starting kernel as its critical endpoint. The
actual backward-path consumer discharges its critical-image premise while
preserving both transporters, relative-normalizer generation and all walk
overlaps. Both covers of orders sixteen and thirty-two and their full central
attachments are retained. The small-image terminal contradiction, larger
original-Sylow images and distance four remain necessary for LargeDistanceInput.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.7)--(5.11), printed pp.919--924. The proof reuses the checked
natural-graph two-shift calculation; it makes no identification with the
exceptional cubic graph and assumes no full point-core equation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedLarge
local notation "S" => Equiv.Perm (Fin 6)

private def crossing : S := Equiv.swap 1 2 * Equiv.swap 3 4

private theorem crossing_generates : plus ⊔ plus.map (MulAut.conj crossing).toMonoidHom = ⊤ := by
  let N := plus ⊔ plus.map (MulAut.conj crossing).toMonoidHom
  have ha : swap45 ∈ N := mem_sup_left ((mem_plus_iff _).mpr ⟨2,by decide +kernel⟩)
  have hb : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3 ∈ N :=
    mem_sup_left ((mem_plus_iff _).mpr ⟨1,by decide +kernel⟩)
  have hc : Equiv.swap (3 : Fin 6) 5 ∈ N := by
    apply mem_sup_right
    exact ⟨swap45,(mem_plus_iff _).mpr ⟨2,by decide +kernel⟩,by decide +kernel⟩
  have hd : Equiv.swap (0 : Fin 6) 2 * Equiv.swap 1 4 ∈ N := by
    apply mem_sup_right
    exact ⟨Equiv.swap 0 1 * Equiv.swap 2 3,
      (mem_plus_iff _).mpr ⟨1,by decide +kernel⟩,by decide +kernel⟩
  have h2 : Equiv.swap (2 : Fin 6) 5 ∈ N := by
    have he : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3) * Equiv.swap 3 5 *
        (Equiv.swap 0 1 * Equiv.swap 2 3) = Equiv.swap (2 : Fin 6) 5 := by decide +kernel
    rw [←he]
    exact N.mul_mem (N.mul_mem hb hc) hb
  have h1 : Equiv.swap (1 : Fin 6) 5 ∈ N := by
    have he : (Equiv.swap (0 : Fin 6) 2 * Equiv.swap 1 4) * swap45 *
        (Equiv.swap 0 2 * Equiv.swap 1 4) = Equiv.swap (1 : Fin 6) 5 := by decide +kernel
    rw [←he]
    exact N.mul_mem (N.mul_mem hd ha) hd
  have h0 : Equiv.swap (0 : Fin 6) 5 ∈ N := by
    have he : (Equiv.swap (0 : Fin 6) 2 * Equiv.swap 1 4) * Equiv.swap 2 5 *
        (Equiv.swap 0 2 * Equiv.swap 1 4) = Equiv.swap (0 : Fin 6) 5 := by decide +kernel
    rw [←he]
    exact N.mul_mem (N.mul_mem hd h2) hd
  have hs : ∀ i : Fin 5, Equiv.swap i.castSucc (5 : Fin 6) ∈ N := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact hc
    · exact ha
  apply top_unique
  rw [←Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5)]
  apply (Subgroup.closure_le _).mpr
  rintro z ⟨i,rfl⟩
  have he : ∀ i : Fin 4, Equiv.swap (i.castSucc.castSucc : Fin 6) i.castSucc.succ =
      Equiv.swap i.castSucc.castSucc 5 * Equiv.swap i.succ.castSucc 5 *
        Equiv.swap i.castSucc.castSucc 5 := by decide +kernel
  fin_cases i
  · change Equiv.swap (0 : Fin 6) 1 ∈ N
    rw [show Equiv.swap (0 : Fin 6) 1 = _ from he 0]
    exact N.mul_mem (N.mul_mem (hs 0) (hs 1)) (hs 0)
  · change Equiv.swap (1 : Fin 6) 2 ∈ N
    rw [show Equiv.swap (1 : Fin 6) 2 = _ from he 1]
    exact N.mul_mem (N.mul_mem (hs 1) (hs 2)) (hs 1)
  · change Equiv.swap (2 : Fin 6) 3 ∈ N
    rw [show Equiv.swap (2 : Fin 6) 3 = _ from he 2]
    exact N.mul_mem (N.mul_mem (hs 2) (hs 3)) (hs 2)
  · change Equiv.swap (3 : Fin 6) 4 ∈ N
    rw [show Equiv.swap (3 : Fin 6) 4 = _ from he 3]
    exact N.mul_mem (N.mul_mem (hs 3) (hs 4)) (hs 3)
  · exact ha

private theorem conjugate_generates (u v : S) :
    ∃ k : S, (plus.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k).toMonoidHom ⊔
      plus.map (MulAut.conj v).toMonoidHom = ⊤ := by
  let k := v * crossing * u⁻¹
  refine ⟨k,?_⟩
  have hm : (MulAut.conj k).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj v).toMonoidHom.comp (MulAut.conj crossing).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change (v*crossing*u⁻¹)*(u*x*u⁻¹)*(v*crossing*u⁻¹)⁻¹ = v*(crossing*x*crossing⁻¹)*v⁻¹
    group
  have hh := congrArg (Subgroup.map (MulAut.conj v).toMonoidHom) crossing_generates
  rw [Subgroup.map_sup,map_top_of_surjective _ (MulAut.conj v).surjective] at hh
  rw [map_map,hm,←map_map,sup_comm]
  exact hh


universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem graphImage_le_mixed_of_le_edge (u : S)
    (hR : d.radical.map s.projection ≤ plus.map (MulAut.conj u).toMonoidHom)
    (t : Vertex d.radical) (hat : Adjacent d.radical (alpha d.radical) t)
    (A : Subgroup (FreeAmalgam d.radical)) (hAt : A ≤ Q d.radical t) :
    ∃ v : S, graphImage s A ≤ plus.map (MulAut.conj v).toMonoidHom := by
  obtain ⟨g,hg|hg⟩ := edge_transitive d.radical hat (base_adjacent d.radical)
  · have hgM : g ∈ (embedM d.radical).range := by
      change g ∈ Mbar d.radical
      rw [← stabilizer_m_base d.radical]
      exact hg.1
    obtain ⟨m,rfl⟩ := hgM
    have hQt : (Q d.radical t).map
        (MulAut.conj ((embedM d.radical m)⁻¹)).toMonoidHom =
          d.radical.map (embedM d.radical) := by
      rw [← Q_act,hg.2]
      exact Q_beta d.radical
    have hAm (x : d.overgroup) (hx : x ∈ A.comap (embedM d.radical)) :
        m⁻¹*x*m ∈ d.radical := by
      have hh := ((map_mono hAt).trans_eq hQt) (mem_map_of_mem
        (MulAut.conj ((embedM d.radical m)⁻¹)).toMonoidHom hx)
      obtain ⟨r,hr,he⟩ := hh
      have heq : r = m⁻¹*x*m := by
        apply embedM_injective d.radical
        change embedM d.radical r = (embedM d.radical m)⁻¹ *
          embedM d.radical x * ((embedM d.radical m)⁻¹)⁻¹ at he
        simpa only [map_mul,map_inv,inv_inv] using he
      exact heq ▸ hr
    refine ⟨s.projection m * u,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨r,hr,he⟩ := hR (mem_map_of_mem s.projection (hAm x hx))
    refine ⟨r,hr,?_⟩
    change (s.projection m*u)*r*(s.projection m*u)⁻¹=s.projection x
    have he' : u*r*u⁻¹ = (s.projection m)⁻¹*s.projection x*s.projection m := by
      change u*r*u⁻¹ = s.projection (m⁻¹*x*m) at he
      simpa only [map_mul,map_inv] using he
    calc
      (s.projection m*u)*r*(s.projection m*u)⁻¹ =
          s.projection m*(u*r*u⁻¹)*(s.projection m)⁻¹ := by group
      _ = s.projection x := by rw [he']; group
  · have hh : color d.radical (beta d.radical) = false := by
      change color d.radical (hVertex d.radical 1) = false
      rw [← hg.1,action_preserves_color]
      rfl
    cases hh

/-- In the mixed-plane branch a large critical image supplies an edge
kernel that generates the whole starting stabilizer with the endpoint. -/
theorem mixed_large_generating_neighbor
    (hc : DistanceTwo.CentralLayer d) (u : S)
    (hfull : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) := by
  have hp := replacementDistance_pos h d
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hAt : Z d.radical a' ≤ Q d.radical (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(replacementGeometry h d).distance_constant _ p.end_color]
    change p.walk.length-1 < replacementDistance h d
    omega
  obtain ⟨v,hv⟩ := graphImage_le_mixed_of_le_edge s u hfull.le _ hat _ hAt
  have hcard : 4 ≤ Nat.card (graphImage s (Z d.radical a')) := by
    rw [graphImage_card s _ (hAt.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hat)))]
    exact reverse_critical_image_four_le s hc hp p hlarge
  have heq : graphImage s (Z d.radical a') = plus.map (MulAut.conj v).toMonoidHom :=
    eq_of_le_of_card_ge hv (by rw [card_map_of_injective (MulAut.conj v).injective,card_plus]; exact hcard)
  obtain ⟨k,hk⟩ := conjugate_generates u v
  rw [←heq] at hk
  obtain ⟨g,hgk⟩ := s.surjective k
  let A := (Z d.radical a').comap (embedM d.radical)
  have hm : (d.radical.map (MulAut.conj g).toMonoidHom).map s.projection =
      (d.radical.map s.projection).map (MulAut.conj k).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change s.projection (g*x*g⁻¹) = k*s.projection x*k⁻¹
    rw [map_mul,map_mul,map_inv,hgk]
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hker : s.projection.ker ≤ d.radical.map (MulAut.conj g).toMonoidHom := by
    rw [s.projection_kernel,←hQ]
    exact map_mono (replacement_core_le_radical h d)
  have hgen : d.radical.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
    apply map_injective_of_ker_le s.projection (hker.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hm,hfull,map_top_of_surjective s.projection s.surjective]
    exact hk
  let f := (embedM d.radical g)⁻¹
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act d.radical f (alpha d.radical) = alpha d.radical := hf
  refine ⟨act d.radical f (beta d.radical),?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff d.radical f (alpha d.radical) (beta d.radical)).mpr
      (base_adjacent d.radical)
  · have hmapA : A.map (embedM d.radical) = Z d.radical a' :=
      map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
        (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
          (stabilizer_m_base d.radical))
    have hh := congrArg (Subgroup.map (embedM d.radical)) hgen
    rw [Subgroup.map_sup,hmapA,←MonoidHom.range_eq_map] at hh
    rw [Q_act,Q_beta]
    change _ = stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    have hmapR : (d.radical.map (embedM d.radical)).map (MulAut.conj f⁻¹).toMonoidHom =
        (d.radical.map (MulAut.conj g).toMonoidHom).map (embedM d.radical) := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f⁻¹*embedM d.radical x*(f⁻¹)⁻¹=embedM d.radical (g*x*g⁻¹)
      simp only [f,inv_inv,map_mul,map_inv]
    rw [hmapR]
    exact hh
private theorem mixed_large_backward_step_base
    (hb : 4 < replacementDistance h d)
    (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ c t x, x ∈ stabilizer d.radical (alpha d.radical) ∧
      act d.radical x (p.walk.getVert 2) = c ∧
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom := by
    rw [hf]
    exact map_mono (plus_le_exceptional.trans
      CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.symm.le)
  have hel := critical_forward_not_le_slice_of_escape s hc hb2
    (MixedEscape.mixed_criticalEscape_knownSimple hb2 u him) p
  obtain ⟨t,hat,hgen⟩ := mixed_large_generating_neighbor s hc u hf p hlarge
  obtain ⟨x,hx,hxt,q,hqt,hover,_⟩ :=
    large_image_backward_shift s hc hb2 u hR p hlarge hdelta hel hat hgen
  refine ⟨_,t,x,hx,rfl,hat,?_,hgen,q,hqt,hover⟩
  rw [←hxt]
  exact (adjacent_act_iff d.radical x _ _).mpr hdelta

include e hz hn in
/-- A large critical image supplies a generating backward shift at every
original component vertex, retaining the same transporter and walk. -/
private theorem mixed_large_backward_step_at_knownSimple
    (hb : 4 < replacementDistance h d)
    (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ c t x, x ∈ stabilizer d.radical a ∧
      act d.radical x (p.walk.getVert 2) = c ∧
      Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical a ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := mixed_large_backward_step_base hb u him
    (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  obtain ⟨c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hover⟩ := base (p.act g⁻¹) (by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge)
  change act d.radical x ((actWalk d.radical g⁻¹ p.walk).getVert 2) = c at hxc
  rw [actWalk_getVert] at hxc
  let y := g⁻¹*x*g
  have hy (v : Vertex d.radical) :
      act d.radical y v = act d.radical g (act d.radical x (act d.radical g⁻¹ v)) := by
    simp only [y,act_mul]
  have hcancel (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hqc : ∃ r : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g c)
      (act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2))),
      r.walk.getVert 1 = act d.radical g t ∧
      ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i := by
    refine ⟨q.act g,?_,?_⟩
    · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical g) hq1
    · intro i hi
      have he := congrArg (act d.radical g) (hover i (by
        simpa only [CriticalPath.act,actWalk_length] using hi))
      simpa only [CriticalPath.act,actWalk_getVert,hcancel] using he
  have hend : act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2)) =
      p.walk.getVert (p.walk.length-2) := by
    change act d.radical g ((actWalk d.radical g⁻¹ p.walk).getVert
      ((actWalk d.radical g⁻¹ p.walk).length-2)) = _
    rw [actWalk_length,actWalk_getVert,hcancel]
  rw [hend] at hqc
  obtain ⟨r,hr1,hrover⟩ := hqc
  refine ⟨act d.radical g c,act d.radical g t,y,?_,?_,?_,?_,?_,r,hr1,hrover⟩
  · change act d.radical y a = a
    rw [hy,show act d.radical x (act d.radical g⁻¹ a) = act d.radical g⁻¹ a from hx,hcancel]
  · rw [hy,hxc]
  · simpa only [hcancel] using (adjacent_act_iff d.radical g _ _).mpr hat
  · exact (adjacent_act_iff d.radical g _ _).mpr hct
  · have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at he
    exact he


include e hz hn in
/-- A generating backward shift in the mixed-plane branch must have critical
image two. Otherwise its own large-image shift gives the forbidden pair
of successive generating shifts. -/
private theorem mixed_generating_backward_shift_indices_knownSimple
    (hb : 4 < replacementDistance h d)
    (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) :
    (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical q.start) = 2 ∧
      (Q d.radical q.start).relIndex (Z d.radical (p.walk.getVert (p.walk.length-2))) = 2 ∧
      Nat.card (⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hsmall : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex
      (Z d.radical q.start) < 4 := by
    by_contra! hlarge
    obtain ⟨c,t,x,hx,hxc,hat,hct,hgen,r,hr1,hro⟩ :=
      mixed_large_backward_step_at_knownSimple (e := e) (hz := hz) (hn := hn)
        hb u him q.path hlarge
    let r' : BackwardShift (h := h) q.path := ⟨c,t,x,hx,hxc,hat,hct,hgen,r,hr1,hro⟩
    have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
      rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
      exact map_mono plus_le_D
    exact cube_two_backward_shifts_false s hc hb u hR p q r'
  have hi := small_critical_indices s hc q.path hsmall
  exact ⟨hi.1,hi.2,small_critical_commutator_card s hc q.path hsmall⟩

include e hz hn in
/-- The actual large-image branch supplies a generating backward shift
whose two critical images and full commutator all have order two. -/
private theorem mixed_large_backward_small_knownSimple
    (hb : 4 < replacementDistance h d)
    (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ q : BackwardShift (h := h) p,
      (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical q.start) = 2 ∧
      (Q d.radical q.start).relIndex (Z d.radical (p.walk.getVert (p.walk.length-2))) = 2 ∧
      Nat.card (⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 := by
  obtain ⟨c,t,x,hx,hxc,hat,hct,hgen,v,hv1,hvo⟩ :=
    mixed_large_backward_step_at_knownSimple hb u him p hlarge
  let q : BackwardShift (h := h) p := ⟨c,t,x,hx,hxc,hat,hct,hgen,v,hv1,hvo⟩
  exact ⟨q,mixed_generating_backward_shift_indices_knownSimple
    hb u him p q⟩

include e hz hn in
private theorem generating_overlap_small
    (hb : 4 < replacementDistance h d)
    (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) c
      (p.walk.getVert (p.walk.length-2)))
    (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical a)
    (hq2 : q.walk.getVert 2 = a) :
    (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical c) < 4 := by
  by_contra! hlarge
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨r,_,_,_⟩ := mixed_large_backward_small_knownSimple
    hb u him q hlarge
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono plus_le_D
  have hlenP : p.walk.length = replacementDistance h d := p.length_eq_b
  have hlenQ : q.walk.length = replacementDistance h d := q.length_eq_b
  have hdist1 : (cosetGraph d.radical).dist (q.walk.getVert (q.walk.length-2))
      (p.walk.getVert (p.walk.length-2)) = 2 := by
    rw [q.dist_end]
    omega
  have hdist2 : (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) a' = 2 := by
    rw [p.dist_end]
    omega
  have hdist : (cosetGraph d.radical).dist (q.walk.getVert (q.walk.length-2)) a' ≤ 4 := by
    have hh := (cosetGraph_connected d.radical).dist_triangle
      (u := q.walk.getVert (q.walk.length-2)) (v := p.walk.getVert (p.walk.length-2)) (w := a')
    omega
  let H := ⁅Z d.radical r.start,Z d.radical (q.walk.getVert (q.walk.length-2))⁆
  have hHe : H ≤ Z d.radical (q.walk.getVert (q.walk.length-2)) :=
    ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  have hHend : H ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) := by
    apply (hHe.trans (Z_le_Q_of_dist_lt d.radical _
      ((replacementGeometry h d).exists_critical _ r.path.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color)))
    rw [(replacementGeometry h d).distance_constant _ r.path.end_color]
    change (cosetGraph d.radical).dist (q.walk.getVert (q.walk.length-2)) a' < replacementDistance h d
    omega
  have hnc := critical_commutator_not_central_at_shift_vertex s hc r.path
    c t a a' (by rw [r.first]; exact r.adjacent_start) hct hgen hHend
    r.transporter r.transporter_mem (by simpa only [hq2] using r.start_eq)
  exact hnc (cube_backward_commutator_central s hc hb2 u hR q r)

include e hz hn in
private theorem large_first_edge_slice_bound
    (hb : 4 < replacementDistance h d)
    (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1)) :
    (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta) ≤ 2 := by
  by_cases hel : U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)
  · rw [relIndex_eq_one.mpr hel]
    decide
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom := by
    rw [hf]
    exact map_mono (plus_le_exceptional.trans
      CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.symm.le)
  obtain ⟨t,hat,hgen⟩ := mixed_large_generating_neighbor s hc u hf p hlarge
  obtain ⟨g,hg,hgt,q,hqt,hover,hidx⟩ :=
    large_image_backward_shift s hc (by omega) u hR p hlarge hdelta hel hat hgen
  have hct : Adjacent d.radical (act d.radical g delta) t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g _ _).mpr hdelta
  have hq2 : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  exact (hidx (generating_overlap_small (e := e) (hz := hz) (hn := hn)
    hb u him p q hct hgen hq2)).le

include e hz hn in
private theorem large_critical_image_false_base
    (hb : 4 < replacementDistance h d)
    (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨q,hi,_,_⟩ := mixed_large_backward_small_knownSimple
    hb u him p hlarge
  obtain ⟨g,hgc⟩ := exists_mVertex_of_color d.radical q.path.start_color
  have hbase : act d.radical g⁻¹ q.start = alpha d.radical := by
    rw [hgc,act_mVertex,mul_inv_cancel]
    rfl
  have q₀ := q.path.act g⁻¹
  rw [hbase] at q₀
  have hsmall₀ : (Q d.radical (act d.radical g⁻¹ (p.walk.getVert (p.walk.length-2)))).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    have hZ : Z d.radical (alpha d.radical) =
        (Z d.radical q.start).map (MulAut.conj g).toMonoidHom := by
      calc
        Z d.radical (alpha d.radical) = Z d.radical (act d.radical g⁻¹ q.start) :=
          congrArg (Z d.radical) hbase.symm
        _ = _ := by rw [Z_act,inv_inv]
    rw [hZ,Q_act,inv_inv,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,hi]
    decide
  have hstrict := MixedStrict.mixed_small_forward_slice_strict_knownSimple
    hb u him q₀ hsmall₀
  have hlp : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hlq : 2 < q₀.walk.length := q₀.length_eq_b ▸ hb2
  have hatp : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hatq : Adjacent d.radical (alpha d.radical) (q₀.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q₀.walk.adj_getVert_succ (i := 0) (by omega)
  have hδq : Adjacent d.radical (q₀.walk.getVert 2) (q₀.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (q₀.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hatq hatp
  have hδ : Adjacent d.radical (act d.radical x (q₀.walk.getVert 2)) (p.walk.getVert 1) := by
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hδq
  have hbound := large_first_edge_slice_bound hb u him p hlarge hδ
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective] at hbound
  omega

include e hz hn in
/-- Large critical images are impossible above distance four for the mixed-plane
replacement radical. The controlled shift accepts every eligible first-edge
neighbor; its small critical image bounds all these slices by two. Transport
of the resulting small path supplies a strict slice on that very edge. -/
theorem mixed_large_critical_image_false_knownSimple
    (hb : 4 < replacementDistance h d)
    (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) : False := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hga,act_mVertex,mul_inv_cancel]
    rfl
  have base := large_critical_image_false_base (e := e) (hz := hz) (hn := hn)
    hb u him (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  apply base (p.act g⁻¹)
  rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
  exact hlarge

include e hz hn in
/-- Every critical pair above distance four has both critical images and its
full critical commutator of order two in the mixed-plane branch. -/
theorem mixed_critical_indices_two_knownSimple
    (hb : 4 < replacementDistance h d)
    (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
      (Q d.radical a).relIndex (Z d.radical a') = 2 ∧
      Nat.card (⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4 := by
    by_contra! hlarge
    exact mixed_large_critical_image_false_knownSimple
      hb u him p hlarge
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := small_critical_indices s hc p hsmall
  exact ⟨hi.1,hi.2,small_critical_commutator_card s hc p hsmall⟩

include e hz hn in
/-- The strict forward-slice conclusion now holds for every critical path
above distance four in the mixed-plane branch. -/
theorem mixed_forward_slice_strict_knownSimple
    (hb : 4 < replacementDistance h d)
    (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  apply MixedStrict.mixed_small_forward_slice_strict_at_knownSimple
    hb u him p
  rw [(mixed_critical_indices_two_knownSimple hb u him p).1]
  decide


/-- In the mixed-plane branch, every predecessor radius has exactly the
same order-two image and full starting kernel as its critical endpoint.
No separate radius-index assumption remains. -/
theorem mixed_predecessor_radius_data_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    let W := V d.radical (p.walk.getVert (p.walk.length-2))
    (Q d.radical a).relIndex W = 2 ∧
      Q d.radical a ⊔ W = Q d.radical a ⊔ Z d.radical a' ∧
      ⁅Z d.radical a,W⁆ = ⁅Z d.radical a,Z d.radical a'⁆ ∧
      Z d.radical a ⊓ centralizer (W : Set (FreeAmalgam d.radical)) =
        Z d.radical a ⊓ Q d.radical a' := by
  have hp : (Q d.radical a').relIndex (Z d.radical a) < 4 := by
    rw [(mixed_critical_indices_two_knownSimple hb u him p).1]
    decide
  have hr : (Q d.radical a).relIndex
      (V d.radical (p.walk.getVert (p.walk.length-2))) ≤ 2 := by
    by_contra! hlarge
    obtain ⟨c,_,q,hq,_,_⟩ := MixedSmallSeeds.mixed_predecessor_radius_large_seed_knownSimple
      (by omega) u him p hp hlarge
    exact mixed_large_critical_image_false_knownSimple hb u him q hq
  exact MixedSmallRadius.small_predecessor_radius_data
    (fullSymmetricAction_knownSimple h e hz hn d (by omega))
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) (by omega) p hp hr

/-- Every mixed-plane critical path above distance four has the actual
strict backward shift. Both transporters, relative-normalizer generation,
the slice index and all overlapping vertices are retained. -/
theorem mixed_backward_path_of_four_lt_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
 :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ x ∈ stabilizer d.radical (alpha d.radical),
        act d.radical x (p.walk.getVert 1) = t ∧
        ∃ k ∈ stabilizer d.radical t,
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (act d.radical k (act d.radical x (p.walk.getVert 2)))
              (p.walk.getVert (p.walk.length-2)),
            q.walk.getVert 1 = t ∧
            (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
              (U d.radical (act d.radical k (act d.radical x (p.walk.getVert 2)))) =
            (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
              (U d.radical (p.walk.getVert 2)) ∧
            2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
              (U d.radical (act d.radical k (act d.radical x (p.walk.getVert 2)))) := by
  apply MixedStrict.mixed_small_backward_path_of_four_lt_knownSimple hb u him p
  rw [(mixed_critical_indices_two_knownSimple hb u him p).1]
  decide

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedLarge
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
