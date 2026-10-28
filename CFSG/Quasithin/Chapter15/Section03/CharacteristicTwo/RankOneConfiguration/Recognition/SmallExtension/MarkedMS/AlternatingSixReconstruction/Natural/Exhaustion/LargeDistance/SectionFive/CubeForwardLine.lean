module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeShiftedSpan

/-!
# The shifted reverse-kernel line in the nonsylow three-pair branch

A noncentral cover line has a component conjugate whose centralizer generates
with any actor escaping the local two-core. Apply this to the restricted
actor of a putative large forward critical image. The shifted centralizer
span lies in the predecessor kernel, so the actor controls its commutator.
Normal generation then puts the span in the Baumann subgroup, contradicting
the retained shifted seed. Thus that same forward path has image order two.

For its centralizer span D and full reverse kernel K, [D,K] is nonzero by
the small critical fixer theorem. If its order exceeded two, the checked
three-pair fixed-hyperplane comparison would control [D,Z_endpoint] by
[D,K] and the original critical commutator. Both lie in the starting seed;
normal generation would again force D into the Baumann subgroup. Therefore
[D,K] is an order-two line. It lies in both endpoint seeds and the last edge
seed, and differs from the retained forward line, which moves the endpoint.

The actual nonsylow consumer supplies the three-pair image, eligibility and
all actors internally, retaining both moved covers, the full central kernels,
one forward extension and the same component conjugator. Centrality of the
new line under the entire starting stabilizer is not concluded here; that
comparison, source (5.9)'s strict slice estimate and the terminal exclusions
remain with the original assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3), (5.2)(i), (5.9), printed
pp.866--867,913--914,920--922. The graph is the actual characteristic replacement,
not the exceptional cubic reconstruction graph.
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

include s in
private theorem exists_cover_line_actor_generator (hc : DistanceTwo.CentralLayer d)
    {a : Vertex d.radical} (ha : color d.radical a = false)
    (A : Subgroup (FreeAmalgam d.radical)) (hAG : A ≤ stabilizer d.radical a)
    (hne : ¬ A ≤ Q d.radical a)
    (H : Subgroup (FreeAmalgam d.radical)) (hHU : H ≤ U d.radical a)
    (hcard : Nat.card H = 2)
    (hcentral : ¬ H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    ∃ g ∈ Ltilde d.radical a,
      (stabilizer d.radical a ⊓ centralizer
        (H.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊔
          A = stabilizer d.radical a ∧
      ¬ H.map (MulAut.conj g).toMonoidHom ≤ centralizer
        (A : Set (FreeAmalgam d.radical)) := by
  classical
  obtain ⟨z,hzn,hunique⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hcard
  have hznot : (z : FreeAmalgam d.radical) ∉ centralizer
      (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    intro hz
    apply hcentral
    intro x hx
    by_cases hx1 : x = 1
    · exact hx1 ▸ one_mem _
    · have he : (⟨x,hx⟩ : H) = z := hunique _ (fun he => hx1 (congrArg Subtype.val he))
      have hxz : x = (z : FreeAmalgam d.radical) := congrArg Subtype.val he
      rw [hxz]
      exact hz
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a ha
  obtain ⟨v,hv,hvz⟩ := (show (z : FreeAmalgam d.radical) ∈ (replacementMoved d).map i from
    hiU.symm ▸ hHU z.property)
  have hvnot : v ∉ center d.overgroup := by
    intro hv
    apply hznot
    intro m hm
    obtain ⟨m,rfl⟩ := hir.symm ▸ hm
    rw [←hvz,←map_mul,←map_mul]
    exact congrArg i (mem_center_iff.mp hv m)
  have hA : A ≤ i.range := hAG.trans_eq hir.symm
  let A₀ := A.comap i
  have hmA : A₀.map i = A := map_comap_eq_self hA
  have hnA : ¬ A₀ ≤ pCore 2 d.overgroup := by
    intro hle
    have hh := map_mono (f := i) hle
    rw [hmA,hiQ] at hh
    exact hne hh
  obtain ⟨g,hg,hgen,hmove⟩ := exists_cover_conjugate_generator s ⟨v,hv⟩ hvnot A₀ hnA
  let j : d.overgroup →* stabilizer d.radical a :=
    i.codRestrict _ (fun x => hir ▸ (show i x ∈ i.range from ⟨x,rfl⟩))
  have hgL : i g ∈ Ltilde d.radical a := by
    have hg' : g ∈ pResidual 2 d.overgroup := (replacement_residual h d).symm ▸ hg
    exact mem_map_of_mem (stabilizer d.radical a).subtype
      ((map_pResidual_le 2 j) (mem_map_of_mem j hg'))
  let C := centralizer ({g * v * g⁻¹} : Set d.overgroup)
  let HC := H.map (MulAut.conj (i g)).toMonoidHom
  have hC : C.map i ≤ stabilizer d.radical a ⊓
      centralizer (HC : Set (FreeAmalgam d.radical)) := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨hir ▸ (show i x ∈ i.range from ⟨x,rfl⟩),?_⟩
    rintro y ⟨w,hw,rfl⟩
    by_cases hw1 : w = 1
    · simp only [hw1,map_one,one_mul,mul_one]
    · have he : (⟨w,hw⟩ : H) = z := hunique _ (fun he => hw1 (congrArg Subtype.val he))
      have hwz : w = (z : FreeAmalgam d.radical) := congrArg Subtype.val he
      rw [hwz,←hvz]
      change (i g * i v * (i g)⁻¹) * i x = i x * (i g * i v * (i g)⁻¹)
      simpa only [map_mul,map_inv] using congrArg i
        (mem_centralizer_singleton_iff.mp hx).symm
  refine ⟨i g,hgL,?_,?_⟩
  · apply le_antisymm (sup_le inf_le_left (hA.trans_eq hir))
    have hm := congrArg (Subgroup.map i) hgen
    rw [Subgroup.map_sup,hmA,←MonoidHom.range_eq_map,hir] at hm
    calc
      stabilizer d.radical a = C.map i ⊔ A := hm.symm
      _ ≤ _ := sup_le_sup_right hC _
  · intro hfix
    apply hmove
    intro x hx
    have hzH : i (g * v * g⁻¹) ∈ HC := by
      have hh := mem_map_of_mem (MulAut.conj (i g)).toMonoidHom z.property
      change (i g * (z : FreeAmalgam d.radical) * (i g)⁻¹) ∈ HC at hh
      simpa only [←hvz,map_mul,map_inv] using hh
    apply hi
    simpa only [map_mul] using hfix hzH (i x) hx

include s in
private theorem controlled_actor_at (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical z ∧
      ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤ Z d.radical a ∧
      W ≤ stabilizer d.radical a ∧ ¬ W ≤ Q d.radical a := by
  have base {z : Vertex d.radical}
      (q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
      (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
      ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical z ∧
        ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (q.walk.getVert (q.walk.length-2)),W⁆ ≤
          Z d.radical (alpha d.radical) ∧
        W ≤ stabilizer d.radical (alpha d.radical) ∧ ¬ W ≤ Q d.radical (alpha d.radical) := by
    obtain ⟨W,hWU,hbound,w,hw,hwo,_⟩ := critical_radius_even_actor s hc hb q hlarge
    refine ⟨W,hWU,hbound,(hWU.trans (DistanceEight.U_le_Z d.radical z)).trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
        (replacementDistance_pos h d) q.critical),?_⟩
    intro hWQ
    have hker : W.comap (embedM d.radical) ≤ s.projection.ker := by
      rw [s.projection_kernel]
      have hh := comap_mono (f := embedM d.radical) hWQ
      rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
        (replacement_core_le_radical h d)] at hh
    have hbot := (Subgroup.map_eq_bot_iff _).mpr hker
    have hone : w = 1 := by
      have hh : w ∈ (⊥ : Subgroup (Equiv.Perm (Fin 6))) := hbot ▸ hw
      exact hh
    rw [hone,orderOf_one] at hwo
    omega
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have hbq := base (z := act d.radical j⁻¹ z)
  rw [←hbase] at hbq
  have hlarge₀ : 4 ≤ (Q d.radical (act d.radical j⁻¹ z)).relIndex
      (Z d.radical (act d.radical j⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  obtain ⟨W,hWU,hbound,hWG,hWne⟩ := hbq (p.act j⁻¹) hlarge₀
  let f := (MulAut.conj j⁻¹).toMonoidHom
  have hcancel (v : Vertex d.radical) : act d.radical j (act d.radical j⁻¹ v)=v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  refine ⟨W.map f,?_,?_,?_,?_⟩
  · have hm := map_mono (f := f) hWU
    simpa only [f,←U_act,hcancel] using hm
  · have hm := map_mono (f := f) hbound
    simp only [CriticalPath.act,actWalk_length,actWalk_getVert] at hm
    simpa only [map_commutator,map_inf _ _ f (MulAut.conj j⁻¹).injective,
      f,←V_act,←Q_act,←Z_act,hcancel] using hm
  · have hm := map_mono (f := f) hWG
    simpa only [f,←stabilizer_act,hcancel] using hm
  · intro hh
    apply hWne
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj j⁻¹).injective).mp
    simpa only [f,←Q_act,hcancel] using hh

include s in
private theorem generated_radius_le_slice
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (D P A : Subgroup (FreeAmalgam d.radical))
    (hDV : D ≤ V d.radical a) (hPG : P ≤ stabilizer d.radical a)
    (hAG : A ≤ stabilizer d.radical a) (hne : ¬ A ≤ Q d.radical a)
    (hPN : P ≤ normalizer (D : Set (FreeAmalgam d.radical)))
    (hgen : P ⊔ A = stabilizer d.radical a) (hcomm : ⁅D,A⁆ ≤ Z d.radical a) :
    D ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
  let N := D ⊔ Z d.radical a
  have hNV : N ≤ V d.radical a := sup_le hDV (Z_le_VBall d.radical a 2)
  have hNG : N ≤ stabilizer d.radical a := hNV.trans
    ((replacementGeometry h d).V_local a ha (by
      rw [(replacementGeometry h d).distance_constant a ha]; exact hb))
  have hNA : ⁅N,A⁆ ≤ Z d.radical a :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical a) D (Z d.radical a)
      A (Z d.radical a) (Z_normalized d.radical a) (le_sup_left.trans hNG)
      (Z_le_stabilizer d.radical a) hcomm
      (le_normalizer_iff_commutator_le_left.mp (hAG.trans (Z_normalized d.radical a)))
  have hGN : stabilizer d.radical a ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    refine sup_le ?_ (le_normalizer_iff_commutator_le_left.mpr (hNA.trans le_sup_right))
    exact (le_inf hPN (hPG.trans (Z_normalized d.radical a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact le_sup_left.trans (normalized_radius_le_slice_of_actor_at s hb ha N A
    hNV hGN hAG hne hNA)

include s in
/-- In a small forward slice, every overlapping forward critical extension
has critical image of order two. The restricted large-image actor is used
with its own generating line conjugator, so no point-radical premise is needed. -/
theorem small_slice_forward_extension_index_two
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    {a' z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hel : ¬ U d.radical (p.walk.getVert 2) ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    (q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z)
    (hd : (cosetGraph d.radical).dist a' z = 2)
    (hpre : q.walk.getVert (q.walk.length-2) = a') :
    (Q d.radical z).relIndex (Z d.radical (p.walk.getVert 2)) = 2 := by
  have hb2 : 2 < replacementDistance h d := by omega
  apply (small_critical_indices s hc q ?_).1
  by_contra! hlarge
  let c := p.walk.getVert 2
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  have hline := small_forward_slice_line_knownSimple (e := e) (hz := hz) (hn := hn)
    hb2 p hslice hsmall hel
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical (p.walk.getVert 1)=true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical (p.walk.getVert 1) at hh
    cases he : color d.radical (p.walk.getVert 1) <;> simp_all
  have hTG : T ≤ stabilizer d.radical c :=
    (inf_le_left.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hHU : H ≤ U d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  obtain ⟨A,hAU,hbound,hAG,hne⟩ := controlled_actor_at s hc hb2 q hlarge
  obtain ⟨y,hy,hgen,hmove⟩ := exists_cover_line_actor_generator s hc q.start_color
    A hAG hne H hHU hline.2.1 hline.2.2.2.2
  have hAZ : A ≤ Z d.radical z := hAU.trans (DistanceEight.U_le_Z d.radical z)
  have hmoveZ : ¬ H.map (MulAut.conj y).toMonoidHom ≤
      centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    fun hh => hmove (hh.trans (centralizer_le hAZ))
  have hgenZ : (stabilizer d.radical c ⊓ centralizer
      (H.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam d.radical))) ⊔
      Z d.radical z = stabilizer d.radical c := by
    apply le_antisymm (sup_le inf_le_left (critical_Z_le_stabilizer d.radical
      (replacementGeometry h d) c q.start_color (by
        rw [(replacementGeometry h d).distance_constant c q.start_color]
        exact replacementDistance_pos h d) q.critical))
    exact hgen.ge.trans (sup_le_sup_left hAZ _)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hDQ,_⟩ :=
    cover_small_shifted_forward_configuration_of_choice s hc hb p hsmall hline.1
      z q.end_color hd y (Ltilde_le_stabilizer _ hy) hgenZ hmoveZ
  let a := act d.radical y⁻¹ (alpha d.radical)
  let P := stabilizer d.radical c ⊓ centralizer
    (H.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam d.radical))
  let D := conjugateSpanBy (Z d.radical a) P
  have haV : Z d.radical a ≤ V d.radical c := by
    have hh : Z d.radical (alpha d.radical) ≤ V d.radical c :=
      le_iSup_of_le (alpha d.radical) (le_iSup_of_le
        (show (cosetGraph d.radical).dist (alpha d.radical) c ≤ 2 from
          (p.dist_start (by omega)).le) le_rfl)
    rw [Z_act,inv_inv]
    exact (map_mono hh).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (DistanceEight.V_normalized d.radical _ (Ltilde_le_stabilizer _ hy)))
  have hDV : D ≤ V d.radical c := conjugateSpanBy_le haV
    (inf_le_left.trans (DistanceEight.V_normalized d.radical c))
  have hDN : P ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    le_normalizer_conjugateSpanBy _ _
  have hDpre : D ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
    rw [hpre]
    exact hDQ
  have hDB := generated_radius_le_slice s hb2 q.start_color D P A hDV inf_le_left hAG hne
    hDN hgen ((commutator_mono (le_inf hDV hDpre) le_rfl).trans hbound)
  have haB : Z d.radical a ≤ B d.radical c ((replacementGeometry h d).Z_normal _) :=
    (le_conjugateSpanBy _ _).trans hDB
  have hBm := mem_normalizer_iff_map_conj_eq.mp
    (Escape.Propagation.Rigidity.B_normalized hb2 c q.start_color (Ltilde_le_stabilizer _ hy))
  rw [Z_act,inv_inv,←hBm] at haB
  have hstart := (map_le_map_iff_of_injective (MulAut.conj y).injective).mp haB
  exact critical_start_not_le_second_slice s hc hb2 p
    ((DistanceEight.U_le_Z d.radical _).trans hstart)

include s in
/-- A radius span in the predecessor kernel, normalized by a generating
centralizer, has exactly one nonzero reverse-kernel displacement line in the
three-pair branch. No common edge kernel or full point-core image is assumed. -/
theorem cube_generated_span_kernel_line
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ (CFSG.Quasithin.ChapterB.Offenders.D 6).map
      (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (D P : Subgroup (FreeAmalgam d.radical)) (hDV : D ≤ V d.radical a)
    (hDpre : D ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hPG : P ≤ stabilizer d.radical a)
    (hDN : P ≤ normalizer (D : Set (FreeAmalgam d.radical)))
    (hgen : P ⊔ Z d.radical z = stabilizer d.radical a)
    (hDB : ¬ D ≤ B d.radical a ((replacementGeometry h d).Z_normal _)) :
    let J := ⁅D,Z d.radical z ⊓ Q d.radical a⁆
    Nat.card J = 2 ∧ J ≤ Z d.radical a ⊓ Z d.radical z ∧
      J ≤ Z d.radical (q.walk.getVert (q.walk.length-1)) := by
  let K := Z d.radical z ⊓ Q d.radical a
  let J := ⁅D,K⁆
  have hZG : Z d.radical z ≤ stabilizer d.radical a :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) a q.start_color (by
      rw [(replacementGeometry h d).distance_constant a q.start_color]
      exact replacementDistance_pos h d) q.critical
  have hne := (critical_reverse_pair s hc q).2
  have hnot (hh : ⁅D,Z d.radical z⁆ ≤ Z d.radical a) : False :=
    hDB (generated_radius_le_slice s hb q.start_color D P (Z d.radical z)
      hDV hPG hZG hne hDN hgen hh)
  have hJne : J ≠ ⊥ := by
    intro he
    exact hnot (small_critical_predecessor_commutator s hc hb q hsmall D hDpre
      (commutator_eq_bot_iff_le_centralizer.mp he))
  have hedge := critical_last_edge_inputs (h := h) hb q
  have hDedge := hDpre.trans hedge.2.1
  have hDGz : D ≤ stabilizer d.radical z :=
    hDedge.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hedge.1))
  have hJZa : J ≤ Z d.radical a :=
    (commutator_mono hDV inf_le_right).trans
      (cube_radius_core_commutator_le_seed s hc hb u hR a q.start_color)
  have hJZz : J ≤ Z d.radical z :=
    (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hDGz.trans (Z_normalized d.radical z)))
  have hJedge : J ≤ Z d.radical (q.walk.getVert (q.walk.length-1)) := by
    dsimp only [J,K]
    rw [commutator_comm]
    exact (commutator_mono inf_le_left hDedge).trans
      (cube_edge_seed_commutator_le s hc u hR q.end_color hedge.1)
  let := finite_Z d.radical z
  let : Finite J := Finite.of_injective (inclusion hJZz) (inclusion_injective _)
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
  have hfixed : K = Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    dsimp only [K]
    rw [←C_eq_Q s hc a q.start_color]
    apply le_antisymm (inf_le_inf_left _ inf_le_right)
    exact le_inf inf_le_left (le_inf (inf_le_left.trans hZG) inf_le_right)
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ 2 := by
    have hC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a q.start_color))
    exact ((relIndex_le_of_le_left hC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc q hsmall).2
  have hcard : Nat.card J ≤ 2 := by
    by_contra! hlarge
    have hlarge' : 2 < Nat.card (⁅Z d.radical z ⊓
        centralizer (Z d.radical a : Set (FreeAmalgam d.radical)),D⁆ :
        Subgroup (FreeAmalgam d.radical)) := by
      rw [←hfixed,commutator_comm]
      exact hlarge
    have hh := cube_edge_large_fixed_commutator s hc u hR q.end_color hedge.1
      (Z d.radical a) D hedge.2.2 hDedge q.critical.2 hindex hlarge'
    rw [←hfixed,commutator_comm K D] at hh
    have hcrit : ⁅Z d.radical z,Z d.radical a⁆ ≤ Z d.radical a :=
      le_normalizer_iff_commutator_le_right.mp (hZG.trans (Z_normalized d.radical a))
    apply hnot
    rw [commutator_comm]
    exact hh.trans (sup_le hJZa hcrit)
  have hpos := (one_lt_card_iff_ne_bot J).mpr hJne
  exact ⟨(show Nat.card J = 2 by omega),le_inf hJZa hJZz,hJedge⟩

/-- The actual nonsylow small-slice configuration has a small shifted critical
image and a nonzero reverse-kernel line distinct from the retained forward line.
Every path, subgroup, central attachment and conjugator is the same witness. -/
theorem nonsylow_small_shifted_kernel_line_knownSimple
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
        J ≤ Z d.radical (q.walk.getVert (q.walk.length-1)) ∧ J ≠ H₂ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨z,q,hd,hover,hpre,y,hy,hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,hcard,hHCa,
    hcomm,hZaQ,hYQ,hDQ,hWQ,hZaV,hZaB⟩ :=
    nonsylow_small_shifted_spans_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p hslice hsmall
  have hi := small_slice_forward_extension_index_two s hc hb p hsmall hslice
    (critical_forward_not_le_slice_of_escape s hc hb2
      (nonsylow_criticalEscape_knownSimple (e := e) (hz := hz) (hn := hn) hb hns) p)
      q hd hpre
  refine ⟨z,q,hd,hover,hpre,hi,y,hy,hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,hcard,hHCa,
    hcomm,hZaQ,hYQ,hDQ,hWQ,hZaV,hZaB,?_⟩
  let c := p.walk.getVert 2
  let a := act d.radical y⁻¹ (alpha d.radical)
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H₂ := (⁅U d.radical c,T⁆ : Subgroup (FreeAmalgam d.radical)).map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  let D := conjugateSpanBy (Z d.radical a) P
  obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  have hR : d.radical.map s.projection ≤ (CFSG.Quasithin.ChapterB.Offenders.D 6).map
      (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hu]
  have hDV : D ≤ V d.radical c := conjugateSpanBy_le hZaV
    (inf_le_left.trans (DistanceEight.V_normalized d.radical c))
  have hDpre : D ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
    rw [hpre]
    exact hDQ
  have hj := cube_generated_span_kernel_line s hc hb2 u hR q (by rw [hi]; decide)
    D P hDV hDpre inf_le_left (le_normalizer_conjugateSpanBy _ _) hgen
    (fun hh => hZaB ((le_conjugateSpanBy _ _).trans hh))
  refine ⟨hj.1,hj.2.1,hj.2.2,?_⟩
  intro he
  apply hmove
  have hHZ : H₂ ≤ Z d.radical z := by
    change ⁅D,Z d.radical z ⊓ Q d.radical c⁆ = H₂ at he
    rw [←he]
    exact hj.2.1.trans inf_le_right
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) z q.end_color
  exact hHZ.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
