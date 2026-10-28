module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeStrictBackward
public import Theory.GroupAction.SymmetricSixSmallSection

/-!
# Full predecessor kernels in the three-pair branch

A predecessor moving-slice index at most two identifies the full reverse
critical kernel with that slice. Its commutator with the predecessor core
has order at most four and lies in the last edge seed. The predecessor
residual normalizes the commutator because it fixes the slice modulo the
predecessor seed. The last edge kernel centralizes the commutator; together
these groups give normality in the entire predecessor stabilizer. The
actual symmetric-six small-section theorem then forces residual fixedness,
and hence centrality in that whole stabilizer. This does not infer centrality
from the order-four bound alone.

If any whole radius is trapped in its critical path's predecessor core,
the strict nonsylow backward shift bounds every two-edge slice by two.
The literal replacement consumer consequently supplies the full predecessor
kernel identity and centrality for every critical path, without an assumed
radical image or numerical slice estimate. Each predecessor residual element
preserves the commutator while conjugating an arbitrary actor in that core;
the same conjugator and the full kernel are retained in the transport identity.
Both moved covers and all central attachments remain allowed.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.7)--(5.8), printed pp.919--920, and (3.3), pp.866--867.
Excluding the remaining uniformly small slices, the strict forward-slice
argument, terminal contradictions, original Sylow branches and distance-four
exclusions remain with the large-distance assembly owner.
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
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

private theorem fixed_mod_seed_normalizes_commutator {F : Type*} [Group F]
    (A Q D : Subgroup F) (hAQ : A ≤ normalizer (Q : Set F))
    (hDQ : D ≤ normalizer (Q : Set F))
    (hDA : ⁅D,A⁆ ≤ centralizer (Q : Set F)) :
    D ≤ normalizer ((⁅A,Q⁆ : Subgroup F) : Set F) := by
  apply le_normalizer_closure_iff.mpr
  rintro d hd _ ⟨a,ha,q,hq,rfl⟩
  have hq' : d*q*d⁻¹ ∈ Q := (mem_normalizer_iff.mp (hDQ hd) q).mp hq
  have hk : ⁅d,a⁆ ∈ centralizer (Q : Set F) := hDA (commutator_mem_commutator hd ha)
  have hcomm : ⁅a,d*q*d⁻¹⁆ ∈ Q :=
    le_normalizer_iff_commutator_le_right.mp hAQ (commutator_mem_commutator ha hq')
  have hzero : ⁅⁅d,a⁆,d*q*d⁻¹⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hk _ hq').symm
  rw [conjugate_commutatorElement,show d*a*d⁻¹ = ⁅d,a⁆*a by
    simp [commutatorElement_def,mul_assoc],commutatorElement_mul_left_eq_conj_mul,
    hzero,mul_one,←hk _ hcomm,mul_inv_cancel_right]
  exact commutator_mem_commutator ha hq'

include h in
private theorem core_residual_edge_generation {a t : Vertex d.radical}
    (ha : color d.radical a = false) (hat : Adjacent d.radical a t) :
    Ltilde d.radical a ⊔ Q d.radical t = stabilizer d.radical a := by
  have hsup : replacementComponent d ⊔ d.radical = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨k,hk,r,hr,rfl⟩ := replacement_product h d g
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hbase : Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (beta d.radical) =
      stabilizer d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d,Q_beta,←Subgroup.map_sup,hsup]
    exact (MonoidHom.range_eq_map (embedM d.radical)).symm.trans (stabilizer_m_base d.radical).symm
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act] at he
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
  · rw [hg.1] at ha
    cases ha

include s in
private theorem small_normal_core_fixed
    {c : Vertex d.radical} (hcol : color d.radical c = false)
    (N : Subgroup (FreeAmalgam d.radical)) (hNQ : N ≤ Q d.radical c)
    (hNn : stabilizer d.radical c ≤ normalizer (N : Set (FreeAmalgam d.radical)))
    (hcard : Nat.card N ≤ 8) : N ≤ centralizer (Ltilde d.radical c : Set (FreeAmalgam d.radical)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical hcol
  let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
  have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical)
  have hact : act d.radical g (alpha d.radical) = c := by
    rw [hg]
    simp only [alpha,act_mVertex,one_mul]
  have hir : i.range = stabilizer d.radical c := by
    rw [←hact,stabilizer_act]
    change ((MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)).range = _
    rw [MonoidHom.range_comp]
    exact congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) (stabilizer_m_base d.radical).symm
  have hiQ : (pCore 2 d.overgroup).map i = Q d.radical c := by
    rw [←hact,Q_act,Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d),map_map]
  have hiL : (pResidual 2 d.overgroup).map i = Ltilde d.radical c := by
    rw [←hact,Ltilde_act,Ltilde_alpha,map_map]
  let N₀ := N.comap i
  have hNm : N₀.map i=N := map_comap_eq_self
    ((hNQ.trans (fun _ hx => hx.1)).trans_eq hir.symm)
  let : N₀.Normal := ⟨by
    intro z hz m
    change i (m*z*m⁻¹) ∈ N
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hNn (hir ▸ (show i m ∈ i.range from ⟨m,rfl⟩))) _).mp hz⟩
  have hNker : N₀ ≤ s.projection.ker := by
    rw [s.projection_kernel]
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hNm,hiQ]
  have hk : IsPGroup 2 s.projection.ker := by
    rw [s.projection_kernel]
    exact pCore_isPGroup
  have hidx : (⊥ : Subgroup d.overgroup).relIndex N₀ ≤ 8 := by
    rw [relIndex_bot_left,←card_map_of_injective hi,hNm]
    exact hcard
  have hh := map_mono (f := i) (commutator_pResidual_le_of_symmetricSix_small_section
    s.projection s.surjective hk N₀ ⊥ hNker hidx)
  rw [map_commutator,hNm,hiL,Subgroup.map_bot] at hh
  exact commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hh)

include s in
/-- A small predecessor slice makes the full reverse-kernel core commutator
central at the predecessor. Its order can be four in the three-pair cover. -/
theorem cube_predecessor_slice_commutator_central
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hindex : (B d.radical (p.walk.getVert (p.walk.length-2))
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical a') ≤ 2) :
    let K := Z d.radical a' ⊓ Q d.radical a
    let N := ⁅K,Q d.radical (p.walk.getVert (p.walk.length-2))⁆
    Nat.card N ≤ 4 ∧ N ≤ Z d.radical (p.walk.getVert (p.walk.length-1)) ∧
      N ≤ centralizer (stabilizer d.radical (p.walk.getVert (p.walk.length-2)) :
        Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert (p.walk.length-2)
  let t := p.walk.getVert (p.walk.length-1)
  let K := Z d.radical a' ⊓ Q d.radical a
  let N := ⁅K,Q d.radical c⁆
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c=false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have hct : Adjacent d.radical c t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have het : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t=true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcol] at hh
    cases he : color d.radical t <;> simp_all
  have hslice := critical_predecessor_slice_eq_kernel s hc hb p hindex
  have hKB : K ≤ B d.radical c ((replacementGeometry h d).Z_normal _) :=
    hslice.1.ge.trans inf_le_right
  have hcard : Nat.card N ≤ 4 := cube_small_critical_kernel_predecessor_card s hc hb u hR p
    (by rw [hslice.2.1]; decide)
  have hNedge : N ≤ Z d.radical t :=
    (commutator_mono inf_le_left (Q_le_adjacent_h d.radical ht hct)).trans
      (cube_edge_seed_commutator_le s hc u hR p.end_color het)
  have hVG := ((replacementGeometry h d).V_le_Q hb c hcol).trans
    (show Q d.radical c ≤ stabilizer d.radical c from fun _ hx => hx.1)
  have hKQ : K ≤ Q d.radical c := by
    intro z hz
    exact (replacementGeometry h d).V_le_Q hb c hcol
      (((mem_B_iff d.radical c _ hVG z).mp (hKB hz)).1)
  have hNQ : N ≤ Q d.radical c := (Subgroup.commutator_le_sup _ _).trans (sup_le hKQ le_rfl)
  have hfix : ⁅Ltilde d.radical c,K⁆ ≤ centralizer (Q d.radical c : Set (FreeAmalgam d.radical)) := by
    apply le_trans _ (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c hcol))
    apply commutator_le.mpr
    intro l hl z hz
    exact ((mem_B_iff d.radical c _ hVG z).mp (hKB hz)).2 l hl
  have hLn : Ltilde d.radical c ≤ normalizer (N : Set (FreeAmalgam d.radical)) :=
    fixed_mod_seed_normalizes_commutator K (Q d.radical c) (Ltilde d.radical c)
      (hKQ.trans (Q d.radical c).le_normalizer)
      ((Ltilde_le_stabilizer c).trans (Q_normalized d.radical c)) hfix
  have hedgefix : N ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro z hz
    have hh := hNedge hz
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  have hNn : stabilizer d.radical c ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    rw [←core_residual_edge_generation (h := h) hcol hct]
    exact sup_le hLn ((le_centralizer_iff.mp hedgefix).trans (Subgroup.centralizer_le_normalizer _))
  have hres := small_normal_core_fixed s hcol N hNQ hNn (hcard.trans (by decide))
  refine ⟨hcard,hNedge,?_⟩
  apply le_centralizer_iff.mp
  rw [←core_residual_edge_generation (h := h) hcol hct]
  exact sup_le (le_centralizer_iff.mp hres) (le_centralizer_iff.mp hedgefix)

include e hz hn in
/-- If one whole radius is trapped, the strict backward shift bounds every
two-edge slice, at every component vertex, by two. -/
theorem nonsylow_trapped_radius_all_slices_le_two_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
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
    obtain ⟨v,hav,k,hk,hkt,_,q,_,_⟩ := nonsylow_strict_backward_path_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb4 hns p hcgt hindexg
    have hkv : Adjacent d.radical (act d.radical k (act d.radical g c)) v := by
      rw [←hkt]
      exact (adjacent_act_iff d.radical k _ _).mpr hcgt
    have hd : (cosetGraph d.radical).dist (act d.radical k (act d.radical g c)) a₀ ≤ 2 := by
      have h1 : (cosetGraph d.radical).dist (act d.radical k (act d.radical g c)) v=1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hkv)
      have h2 : (cosetGraph d.radical).dist v a₀=1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr
          (adjacent_symm d.radical hav))
      simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
        (u := act d.radical k (act d.radical g c)) (v := v) (w := a₀)
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
/-- A trapped radius identifies every predecessor slice with the full reverse
critical kernel. Its core commutator is central in the entire predecessor
stabilizer, with no assumed slice, critical-image or radical-image estimate. -/
theorem nonsylow_trapped_radius_predecessor_kernels_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
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
  obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns
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
  have hindex := nonsylow_trapped_radius_all_slices_le_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns p hbad hcol hct het
  have hs := critical_predecessor_slice_eq_kernel s hc hb q hindex
  exact ⟨hs.1,hs.2.1,hs.2.2,cube_predecessor_slice_commutator_central s hc hb u hR q hindex⟩

include h in
private theorem slice_commutator_transport_of_fixed
    (hb : 2 < replacementDistance h d) {c : Vertex d.radical}
    (hcol : color d.radical c = false)
    (A : Subgroup (FreeAmalgam d.radical))
    (hAB : A ≤ B d.radical c ((replacementGeometry h d).Z_normal _))
    (hfixed : ⁅A,Q d.radical c⁆ ≤ centralizer (Ltilde d.radical c : Set (FreeAmalgam d.radical)))
    (D : Subgroup (FreeAmalgam d.radical)) (hD : D ≤ Q d.radical c)
    (k : FreeAmalgam d.radical) (hk : k ∈ Ltilde d.radical c) :
    ⁅A,D.map (MulAut.conj k).toMonoidHom⁆ = ⁅A,D⁆ := by
  have hVQ := (replacementGeometry h d).V_le_Q hb c hcol
  have hVG := hVQ.trans (show Q d.radical c ≤ stabilizer d.radical c from fun _ hx => hx.1)
  have hAQ : A ≤ Q d.radical c := by
    intro a ha
    exact hVQ (((mem_B_iff d.radical c _ hVG a).mp (hAB ha)).1)
  have hZQ : Z d.radical c ≤ centralizer (Q d.radical c : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c hcol)
  have he (a : FreeAmalgam d.radical) (ha : a ∈ A)
      (x : FreeAmalgam d.radical) (hx : x ∈ Q d.radical c) :
      ⁅a,k*x*k⁻¹⁆ = ⁅a,x⁆ := by
    have hx' : k*x*k⁻¹ ∈ Q d.radical c :=
      (mem_normalizer_iff.mp ((Q_normalized d.radical c) (Ltilde_le_stabilizer _ hk)) x).mp hx
    have hka : ⁅k,a⁆ ∈ Z d.radical c :=
      ((mem_B_iff d.radical c _ hVG a).mp (hAB ha)).2 k hk
    have hax' : ⁅a,k*x*k⁻¹⁆ ∈ Q d.radical c :=
      (Subgroup.commutator_le_sup _ _).trans (sup_le hAQ le_rfl)
        (commutator_mem_commutator ha hx')
    have hzero : ⁅⁅k,a⁆,k*x*k⁻¹⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hZQ hka _ hx').symm
    have hfix : k*⁅a,x⁆*k⁻¹ = ⁅a,x⁆ := by
      have hh := hfixed (commutator_mem_commutator ha hx) k hk
      rw [hh,mul_inv_cancel_right]
    have hh := conjugate_commutatorElement a x k
    rw [show k*a*k⁻¹ = ⁅k,a⁆*a by simp [commutatorElement_def,mul_assoc],
      commutatorElement_mul_left_eq_conj_mul,hzero,mul_one,
      ←hZQ hka _ hax',mul_inv_cancel_right,hfix] at hh
    exact hh.symm
  apply le_antisymm
  · apply commutator_le.mpr
    intro a ha x hx
    obtain ⟨y,hy,rfl⟩ := hx
    change ⁅a,k*y*k⁻¹⁆ ∈ ⁅A,D⁆
    rw [he a ha y (hD hy)]
    exact commutator_mem_commutator ha hy
  · apply commutator_le.mpr
    intro a ha x hx
    rw [←he a ha x (hD hx)]
    exact commutator_mem_commutator ha (mem_map_of_mem (MulAut.conj k).toMonoidHom hx)
include e hz hn in
/-- For a trapped original nonsylow radius, every predecessor residual acts
trivially on the full reverse-kernel commutator, using the same conjugator
on its arbitrary core actor. The order-four possibility is retained. -/
theorem nonsylow_trapped_radius_residual_transport_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a₀ a₁ : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ a₁)
    (hbad : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a a' : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a a')
    (D : Subgroup (FreeAmalgam d.radical))
    (hD : D ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (k : FreeAmalgam d.radical)
    (hk : k ∈ Ltilde d.radical (q.walk.getVert (q.walk.length-2))) :
    ⁅Z d.radical a' ⊓ Q d.radical a,D.map (MulAut.conj k).toMonoidHom⁆ =
      ⁅Z d.radical a' ⊓ Q d.radical a,D⁆ := by
  have hh := nonsylow_trapped_radius_predecessor_kernels_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns p hbad q
  have hcol : color d.radical (q.walk.getVert (q.walk.length-2))=false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hl : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  exact slice_commutator_transport_of_fixed (h := h) (by omega) hcol _
    (hh.1.ge.trans inf_le_right)
    (hh.2.2.2.2.2.trans (centralizer_le (Ltilde_le_stabilizer _))) D hD k hk

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
