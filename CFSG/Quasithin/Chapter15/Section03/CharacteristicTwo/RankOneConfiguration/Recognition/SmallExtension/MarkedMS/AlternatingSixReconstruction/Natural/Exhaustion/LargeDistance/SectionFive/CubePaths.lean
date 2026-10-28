module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.NonsylowImage
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardSlice

/-!
# Controlled critical shifts for the original nonsylow radical

The full three-pair subgroup of S₆ and an appropriate even involution
 generate S₆: conjugating its three swaps supplies a connected set of
transpositions. Involution fusion in A₆ preserves the specified six-letter
marking. Together with the existing point-core calculation, this covers
both possible images of an original nonsylow radical.

For a large critical image, the previously constructed restricted endpoint
actor contains an even involution and controls the radius intersection.
Lift the generating conjugator through the actual replacement component.
One incident edge and that same controlled actor generate the starting
stabilizer. The normal-product argument therefore makes an eligible
neighbor critical with the old predecessor. This retains the possible
central attachment and includes the exceptional two-transposition actor;
no full-seed endpoint estimate is assumed.

The resulting backward path retains every shared vertex. Its small-image
case has slice index exactly two. Conjugation gives the result at every
original component vertex; reversal constructs the forward extension and
the whole-radius escape. The prescribed-neighbor version retains one
actual stabilizer conjugator, for the coherent shifted chains in (5.10).

These results discharge the large-critical-image shift in the nonsylow
branch. The small critical-image shift, strict slice argument and terminal
three-pair contradiction are still required, as are the original Sylow
branches and distance-four estimates. Neither the natural graph nor its
kernel is identified with the exceptional reconstruction graph.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.2)(i), (5.5)--(5.10), printed pp.913--923, and characteristic
reduction, pp.932--933; Aschbacher--Smith C.1.31 (MS2)(a), p.135.
The graph lifting and normal-product proofs adapt `BackwardSlice` while
using the actual restricted actor from `ChiefFactor` and `RestrictedActor`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace CubeGeneration
local notation "S" => Equiv.Perm (Fin 6)
private def actor : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by decide +kernel⟩

private theorem actor_generates : D 6 ⊔ zpowers (actor : S) = ⊤ := by
  let N := D 6 ⊔ zpowers (actor : S)
  have ha : (actor : S) ∈ N := mem_sup_right (mem_zpowers _)
  have hpair (i : Fin 3) : pairSwap 6 i ∈ N :=
    mem_sup_left (pairSwap_mem (n := 6) (m := 3) i (by omega))
  have hconj (i : Fin 3) : actor.val * pairSwap 6 i * actor.val⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem ha (hpair i)) (N.inv_mem ha)
  have h01 : Equiv.swap (0 : Fin 6) 1 ∈ N := hpair 0
  have h23 : Equiv.swap (2 : Fin 6) 3 ∈ N := hpair 1
  have h45 : Equiv.swap (4 : Fin 6) 5 ∈ N := hpair 2
  have h02 : Equiv.swap (0 : Fin 6) 2 ∈ N :=
    (by decide +kernel : actor.val * pairSwap 6 0 * actor.val⁻¹ = Equiv.swap 0 2) ▸ hconj 0
  have h14 : Equiv.swap (1 : Fin 6) 4 ∈ N :=
    (by decide +kernel : actor.val * pairSwap 6 1 * actor.val⁻¹ = Equiv.swap 1 4) ▸ hconj 1
  have h12 : Equiv.swap (1 : Fin 6) 2 ∈ N :=
    SubmonoidClass.swap_mem_trans N (by simpa only [Equiv.swap_comm] using h01) h02
  have h24 : Equiv.swap (2 : Fin 6) 4 ∈ N :=
    SubmonoidClass.swap_mem_trans N (by simpa only [Equiv.swap_comm] using h12) h14
  have h34 : Equiv.swap (3 : Fin 6) 4 ∈ N :=
    SubmonoidClass.swap_mem_trans N (by simpa only [Equiv.swap_comm] using h23) h24
  apply top_unique
  rw [←Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5)]
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact h01
  · exact h12
  · exact h23
  · exact h34
  · exact h45

private theorem even_generator (a : alternatingGroup (Fin 6)) (ha : orderOf a = 2) :
    ∃ g : alternatingGroup (Fin 6),
      (D 6).map (MulAut.conj g.val).toMonoidHom ⊔ zpowers a.val = ⊤ := by
  have hao : orderOf actor = 2 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (AlternatingSix.ShadowLocal.involutions_isConj actor a hao ha)
  refine ⟨g,?_⟩
  have he : (MulAut.conj g.val).toMonoidHom actor.val = a.val := congrArg Subtype.val hg
  have hh := congrArg (Subgroup.map (MulAut.conj g.val).toMonoidHom) actor_generates
  simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,he,
    map_top_of_surjective (MulAut.conj g.val).toMonoidHom (MulAut.conj g.val).surjective] using hh

private theorem marked_even_generator (u : S) (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 2) :
    ∃ g : alternatingGroup (Fin 6),
      ((D 6).map (MulAut.conj u).toMonoidHom).map
        (MulAut.conj g.val).toMonoidHom ⊔ zpowers a.val = ⊤ := by
  let c : MulAut (alternatingGroup (Fin 6)) := MulAut.conjNormal u⁻¹
  let b : alternatingGroup (Fin 6) := c a
  have hb : orderOf b = 2 := (c.orderOf_eq a).trans ha
  obtain ⟨k,hk⟩ := even_generator b hb
  let g : alternatingGroup (Fin 6) := MulAut.conjNormal u k
  refine ⟨g,?_⟩
  have hh := congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) hk
  have hback : (MulAut.conj u).toMonoidHom b.val = a.val := by
    change u*(u⁻¹*a.val*u)*u⁻¹=a.val
    group
  have hcomp : ((MulAut.conj g.val).toMonoidHom.comp (MulAut.conj u).toMonoidHom) =
      ((MulAut.conj u).toMonoidHom.comp (MulAut.conj k.val).toMonoidHom) := by
    apply MonoidHom.ext
    intro x
    change (u*k.val*u⁻¹)*(u*x*u⁻¹)*(u*k.val*u⁻¹)⁻¹ = u*(k.val*x*k.val⁻¹)*u⁻¹
    group
  rw [Subgroup.map_sup,MonoidHom.map_zpowers,hback,
    map_top_of_surjective (MulAut.conj u).toMonoidHom (MulAut.conj u).surjective,map_map] at hh
  rw [map_map,hcomp]
  exact hh

end CubeGeneration

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
include s in
private theorem generating_neighbor_of_even_actor
    (himages : (∃ u : Equiv.Perm (Fin 6), d.radical.map s.projection =
      BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom) ∨
      (∃ u : Equiv.Perm (Fin 6), d.radical.map s.projection =
        (D 6).map (MulAut.conj u).toMonoidHom))
    (W : Subgroup (FreeAmalgam d.radical))
    (hWG : W ≤ stabilizer d.radical (alpha d.radical))
    (a : Equiv.Perm (Fin 6)) (ha : a ∈ (W.comap (embedM d.radical)).map s.projection)
    (hao : orderOf a = 2) (haeven : a ∈ alternatingGroup (Fin 6)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) := by
  have hkex : ∃ k : alternatingGroup (Fin 6),
      (d.radical.map s.projection).map (MulAut.conj k.val).toMonoidHom ⊔ zpowers a = ⊤ := by
    rcases himages with ⟨u,hu⟩ | ⟨u,hu⟩
    · rw [hu]
      exact PointCoreEvenGeneration.exists_even_conjugate_pointCore_generates
        u ⟨a,haeven⟩ ((Subgroup.orderOf_coe ⟨a,haeven⟩).symm.trans hao)
    · rw [hu]
      exact CubeGeneration.marked_even_generator
        u ⟨a,haeven⟩ ((Subgroup.orderOf_coe ⟨a,haeven⟩).symm.trans hao)
  obtain ⟨k,hk⟩ := hkex
  have hkL : k.val ∈ (replacementComponent d).map s.projection := by
    rw [s.component_image]
    exact k.property
  obtain ⟨g,hg,hgk⟩ := hkL
  let A := W.comap (embedM d.radical)
  have hm : (d.radical.map (MulAut.conj g).toMonoidHom).map s.projection =
      (d.radical.map s.projection).map (MulAut.conj k.val).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change s.projection (g*x*g⁻¹) = k.val*s.projection x*k.val⁻¹
    rw [map_mul,map_mul,map_inv,hgk]
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hker : s.projection.ker ≤ d.radical.map (MulAut.conj g).toMonoidHom := by
    rw [s.projection_kernel,←hQ]
    exact map_mono (replacement_core_le_radical h d)
  have hgen : d.radical.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
    apply map_injective_of_ker_le s.projection (hker.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hm,map_top_of_surjective s.projection s.surjective]
    apply top_unique
    rw [←hk]
    exact sup_le_sup_left (zpowers_le.mpr ha) _
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
  · have hmapA : A.map (embedM d.radical) = W :=
      map_comap_eq_self (hWG.trans_eq (stabilizer_m_base d.radical))
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

include e hz hn in
/-- The source restricted endpoint actor and one incident edge generate the
whole starting stabilizer. The actor has its actual radius commutator bound;
both nonsylow radical images and both central covers are included. -/
theorem nonsylow_large_image_controlled_neighbor_knownSimple
    (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤
        Z d.radical (alpha d.radical) ∧
      (¬ W ≤ Q d.radical (alpha d.radical)) ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hWU,hbound,a,ha,hao,haeven⟩ := critical_radius_even_actor s hc hb p hlarge
  have hWG : W ≤ stabilizer d.radical (alpha d.radical) :=
    (hWU.trans (DistanceEight.U_le_Z d.radical a')).trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
        (replacementDistance_pos h d) p.critical)
  have himages := nonsylow_radical_image_maximal_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at himages
  refine ⟨W,hWU,hbound,?_,generating_neighbor_of_even_actor s himages W hWG a ha hao haeven⟩
  intro hWQ
  have hWker : W.comap (embedM d.radical) ≤ s.projection.ker := by
    rw [s.projection_kernel]
    have hh := comap_mono (f := embedM d.radical) hWQ
    rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hh
  have hbot := (Subgroup.map_eq_bot_iff (W.comap (embedM d.radical))).mpr hWker
  have hone : a=1 := by
    have hh : a ∈ (⊥ : Subgroup (Equiv.Perm (Fin 6))) := hbot ▸ ha
    exact hh
  rw [hone,orderOf_one] at hao
  omega

include s in
private theorem backward_kernel_le_slice_of_controlled_actor
    (hb : 2 < replacementDistance h d)
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (W : Subgroup (FreeAmalgam d.radical)) (hWU : W ≤ U d.radical a')
    (hWne : ¬ W ≤ Q d.radical a)
    (hbound : ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤
      Z d.radical a)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ W = stabilizer d.radical a)
    (A : Subgroup (FreeAmalgam d.radical))
    (hAc : A ≤ Z d.radical c)
    (hAQ : A ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hAn : Q d.radical t ≤ normalizer (A : Set (FreeAmalgam d.radical))) :
    A ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
  have hdist : (cosetGraph d.radical).dist c a ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t a = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := a)
  have hAV : A ≤ V d.radical a :=
    hAc.trans ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist))
  have hAG := hAV.trans ((replacementGeometry h d).V_local a p.start_color (by
    rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb))
  have hmove : ⁅A,W⁆ ≤ Z d.radical a :=
    (commutator_mono (le_inf hAV hAQ) le_rfl).trans hbound
  have hZmove : ⁅Z d.radical a,W⁆ ≤ Z d.radical a :=
    (commutator_mono le_rfl (hWU.trans (DistanceEight.U_le_Z d.radical a'))).trans
      (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _))
  let Y := A ⊔ Z d.radical a
  have hYmove : ⁅Y,W⁆ ≤ Z d.radical a :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      A (Z d.radical a) W
      (Z d.radical a) (Z_normalized d.radical _) hAG
      (Z_le_stabilizer d.radical _) hmove hZmove
  have hYn : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    apply sup_le
    · exact (le_inf hAn ((show Q d.radical t ≤ stabilizer d.radical a from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans
        (Z_normalized d.radical a))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hYmove.trans le_sup_right)
  have hpos : 0 < criticalDistance d.radical a
      ((replacementGeometry h d).exists_critical a p.start_color) := by
    rw [(replacementGeometry h d).distance_constant a p.start_color]
    exact replacementDistance_pos h d
  exact le_sup_left.trans (normalized_radius_le_slice_of_actor_at s hb p.start_color
    Y W (sup_le hAV (Z_le_VBall d.radical _ 2)) hYn
    ((hWU.trans (DistanceEight.U_le_Z d.radical a')).trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color hpos p.critical))
    hWne hYmove)

include e hz hn in
/-- Every large critical image for an original nonsylow radical supplies a
backward critical path, preserving the generating edge and every shared vertex.
The restricted actor is constructed internally, including the two-swap case. -/
theorem nonsylow_large_image_backward_path_knownSimple
    (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ c t, Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ k ≤ p.walk.length-2, q.walk.getVert (k+2) = p.walk.getVert k) ∧
        2 ≤ (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        ((Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical c) < 4 →
          (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical c) = 2) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hWU,hbound,hWne,t,hat,hgen⟩ := nonsylow_large_image_controlled_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p hlarge
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge s hc hb rfl hat
  have hbad : ¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    intro hbad
    apply hel
    apply (DistanceEight.U_le_Z d.radical c).trans
    apply backward_kernel_le_slice_of_controlled_actor s hb p W hWU hWne hbound hat hct hgen
      (Z d.radical c) le_rfl hbad
    exact (show Q d.radical t ≤ stabilizer d.radical c from
      fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c)
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  have hover (k : ℕ) (hk : k ≤ p.walk.length-2) :
      q.walk.getVert (k+2) = p.walk.getVert k := p.prepend_two_overlap _ _ _ _ _ hk
  have hqa : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hlo := critical_start_slice_index_two_le s hc hb q
  rw [hqa] at hlo
  have hgenZ : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) := by
    apply le_antisymm
    · exact sup_le (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
        (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
          (replacementDistance_pos h d) p.critical)
    · rw [←hgen]
      exact sup_le_sup_left (hWU.trans (DistanceEight.U_le_Z d.radical a')) _
  refine ⟨c,t,hat,hct,hgenZ,q,hqt,hover,hlo,?_⟩
  intro hsmall
  have hE := nonsylow_radical_image_elementary_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hE
  let := hE
  have hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hAn := (small_critical_end_kernels_normalized_of_abelian_image s hc hab q hsmall).1
  rw [hqt] at hAn
  have hB := backward_kernel_le_slice_of_controlled_actor s hb p W hWU hWne hbound hat hct hgen
    (Z d.radical c ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)))
    inf_le_left inf_le_right hAn
  let := finite_Z d.radical c
  have hidx := relIndex_le_of_le_left hB
    (index_ne_zero_of_finite (H := (Z d.radical c ⊓
      Q d.radical (p.walk.getVert (p.walk.length-2))).subgroupOf (Z d.radical c)))
  rw [inf_relIndex_left] at hidx
  exact Nat.le_antisymm (((relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c)
    index_ne_zero_of_finite).trans hidx).trans_eq (small_critical_indices s hc q hsmall).1) hlo

include e hz hn in
/-- The backward shift at every original component vertex, with the same
transported generating edge and the full overlap of the critical walks. -/
theorem nonsylow_large_image_backward_path_at_knownSimple
    (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ c t, Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical a ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ k ≤ p.walk.length-2, q.walk.getVert (k+2) = p.walk.getVert k) ∧
        2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ∧
        ((Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical c) < 4 →
          (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) = 2) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := nonsylow_large_image_backward_path_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  have hl : 4 ≤ (Q d.radical (act d.radical g⁻¹ a')).relIndex
      (Z d.radical (act d.radical g⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  obtain ⟨c,t,hat,hct,hgen,q,hqt,hover,hindex,hsmall⟩ := base (p.act g⁻¹) hl
  have hcancel (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hB : (B d.radical (act d.radical g⁻¹ a) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) := by
    rw [←Escape.PairingControl.FirstPairing.B_act hb g _ (p.act g⁻¹).start_color,hcancel]
  have hidx : (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical g c)) =
      (B d.radical (act d.radical g⁻¹ a) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical c) := by
    rw [←hB,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
  have hex : ∃ r : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g c)
      (act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2))),
      r.walk.getVert 1 = act d.radical g t ∧
      (∀ k ≤ p.walk.length-2, r.walk.getVert (k+2) = p.walk.getVert k) ∧
      2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (act d.radical g c)) ∧
      ((Q d.radical (act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2)))).relIndex
          (Z d.radical (act d.radical g c)) < 4 →
        (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g c)) = 2) := by
    refine ⟨q.act g,?_,?_,hidx.symm ▸ hindex,?_⟩
    · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical g) hqt
    · intro k hk
      have hh := congrArg (act d.radical g) (hover k (by
        simpa only [CriticalPath.act,actWalk_length] using hk))
      simpa only [CriticalPath.act,actWalk_getVert,hcancel] using hh
    · intro hh
      rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hh
      rw [hidx]
      exact hsmall hh
  have hend : act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2)) =
      p.walk.getVert (p.walk.length-2) := by
    change act d.radical g ((actWalk d.radical g⁻¹ p.walk).getVert
      ((actWalk d.radical g⁻¹ p.walk).length-2)) = _
    rw [actWalk_length,actWalk_getVert,hcancel]
  rw [hend] at hex
  refine ⟨act d.radical g c,act d.radical g t,?_,?_,?_,hex⟩
  · simpa only [hcancel] using (adjacent_act_iff d.radical g _ _).mpr hat
  · exact (adjacent_act_iff d.radical g _ _).mpr hct
  · have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at he
    exact he

include e hz hn in
/-- The whole radius escapes the predecessor core for every large critical
pair in the original nonsylow branch. A constructed backward seed witnesses it. -/
theorem nonsylow_large_image_radius_escape_knownSimple
    (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ¬ V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  obtain ⟨c,t,hat,hct,_,q,_⟩ := nonsylow_large_image_backward_path_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p hlarge
  have hdist : (cosetGraph d.radical).dist c a ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t a = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := a)
  intro hbad
  exact q.critical.2 (((Z_le_localZSpan d.radical _ _).trans
    (localZSpan_le_V d.radical hdist)).trans hbad)

include e hz hn in
/-- The same large critical path extends forward by two edges and drops
its first two edges. Its original endpoint is the new predecessor; no
full point-core or universal critical-escape hypothesis is added. -/
theorem nonsylow_large_image_forward_extension_knownSimple
    (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z,
      (cosetGraph d.radical).dist a' z = 2 ∧
      (∀ k ≤ p.walk.length-2, q.walk.getVert k = p.walk.getVert (k+2)) ∧
      q.walk.getVert (q.walk.length-2) = a' := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hec : (cosetGraph d.radical).dist a' (p.walk.getVert 2) + 2 =
      (replacementGeometry h d).b d.radical := by
    rw [SimpleGraph.dist_comm,p.dist_end,p.length_eq_b]
    change replacementDistance h d - 2 + 2 = replacementDistance h d
    omega
  let r : CriticalPath d.radical (replacementGeometry h d) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc p⟩
  have hlarge' : 4 ≤ (Q d.radical a).relIndex (Z d.radical a') :=
    reverse_critical_image_four_le s hc (replacementDistance_pos h d) p hlarge
  have hescape := nonsylow_large_image_radius_escape_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns r hlarge'
  have hpre : r.walk.getVert (r.walk.length-2) = p.walk.getVert 2 := by
    change p.walk.reverse.getVert (p.walk.reverse.length-2) = _
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse]
    congr 1
    omega
  rw [hpre] at hescape
  obtain ⟨z,hz,hze,hcrit⟩ := exists_critical_shift d.radical p.end_color hec hescape
  have hrev : CriticalPair d.radical (p.walk.getVert 2) z
      ((replacementGeometry h d).exists_critical _ hcol) := by
    apply critical_reverse d.radical (replacementGeometry h d) (edgeCentralizerCondition s hc)
      z hz _ _ hcol hcrit
    rw [(replacementGeometry h d).distance_constant z hz]
    exact replacementDistance_pos h d
  obtain ⟨v,hv⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist a' z
  have hvlen : v.length = 2 := hv.trans (SimpleGraph.dist_comm.trans hze)
  let w := (p.walk.drop 2).append v
  have hwlen : w.length = p.walk.length := by
    simp only [w,SimpleGraph.Walk.length_append,SimpleGraph.Walk.drop_length,hvlen]
    omega
  let q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z :=
    ⟨hcol,w,by rw [hwlen,p.length_eq_b,hrev.1,
      (replacementGeometry h d).distance_constant _ hcol]; rfl,hrev⟩
  have hover (i : ℕ) (hi : i ≤ p.walk.length-2) :
      q.walk.getVert i = p.walk.getVert (i+2) := by
    change w.getVert i = _
    rw [SimpleGraph.Walk.getVert_append',SimpleGraph.Walk.drop_length,if_pos hi,
      SimpleGraph.Walk.drop_getVert,Nat.add_comm 2 i]
  refine ⟨z,q,by simpa only [SimpleGraph.dist_comm] using hze,hover,?_⟩
  change w.getVert (w.length-2) = a'
  rw [hwlen]
  change q.walk.getVert (p.walk.length-2) = a'
  rw [hover _ le_rfl,show p.walk.length-2+2 = p.walk.length by omega,p.walk.getVert_length]


include e hz hn in
/-- The source large-image shift preserves a prescribed eligible neighbor
and one actual stabilizer conjugator. No point-core assumption is needed. -/
theorem nonsylow_large_image_backward_shift_knownSimple
    (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
          (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          (∀ k ≤ p.walk.length-2, q.walk.getVert (k+2) = p.walk.getVert k) ∧
          ((Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex
              (Z d.radical (act d.radical g delta)) < 4 →
            (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
              (U d.radical delta) = 2) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hWU,hbound,hWne,t,hat,hgen⟩ := nonsylow_large_image_controlled_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p hlarge
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  let c := act d.radical g delta
  have hct : Adjacent d.radical c t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g delta (p.walk.getVert 1)).mpr hdelta
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
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
  have hbad : ¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    intro hbad
    apply helc
    apply (DistanceEight.U_le_Z d.radical c).trans
    apply backward_kernel_le_slice_of_controlled_actor s hb p W hWU hWne hbound hat hct hgen
      (Z d.radical c) le_rfl hbad
    exact (show Q d.radical t ≤ stabilizer d.radical c from
      fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c)
  let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (by exact Nat.le_of_lt hb) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  have hgenZ : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) := by
    apply le_antisymm
    · exact sup_le (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
        (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
          (replacementDistance_pos h d) p.critical)
    · rw [←hgen]
      exact sup_le_sup_left (hWU.trans (DistanceEight.U_le_Z d.radical a')) _
  refine ⟨t,hat,hgenZ,g,hg,hgt,q,hqt,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi,?_⟩
  intro hsmall
  have hE := nonsylow_radical_image_elementary_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hE
  let := hE
  have hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hAn := (small_critical_end_kernels_normalized_of_abelian_image s hc hab q hsmall).1
  rw [hqt] at hAn
  have hkernel := backward_kernel_le_slice_of_controlled_actor s hb p W hWU hWne hbound hat hct hgen
    (Z d.radical c ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)))
    inf_le_left inf_le_right hAn
  let := finite_Z d.radical c
  have hidx := relIndex_le_of_le_left hkernel
    (index_ne_zero_of_finite (H := (Z d.radical c ⊓
      Q d.radical (p.walk.getVert (p.walk.length-2))).subgroupOf (Z d.radical c)))
  rw [inf_relIndex_left] at hidx
  have hbound := ((relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c)
    index_ne_zero_of_finite).trans hidx).trans_eq (small_critical_indices s hc q hsmall).1
  change (B d.radical (alpha d.radical) _).relIndex (U d.radical (act d.radical g delta)) ≤ 2 at hbound
  rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hbound
  let := finite_Z d.radical delta
  let : Finite (U d.radical delta) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical delta)) (inclusion_injective _)
  have hp : 0 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta) := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hn : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta) ≠ 1 := fun he => hel (relIndex_eq_one.mp he)
  omega

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
