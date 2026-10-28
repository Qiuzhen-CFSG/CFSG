module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSpanControl
public import Theory.GroupTheory.ConjugateSpanNilpotent

/-!
# Strict nonsylow forward slices from the actual span comparison

In the small critical-image branch, the full reverse seed maps to a
transposition in the original S₆ quotient. A normal section fixed by that
seed and by the actual two-core is therefore fixed by the whole starting
stabilizer: the normal kernel of its action contains every transposition.
This supplies the whole-stabilizer displacement bound needed to collapse
W = ⟨Y^P⟩ to Y by nilpotent commutator saturation. The component alone is
not asserted to generate that stabilizer modulo its two-core.

Apply the collapse to the exact Y, P, endpoint and overlapping critical path
from CubeSpanControl. The original shifted forward commutator H₂ has order
two and equals [U_c,T₂], so T₂ escapes Q_c. The common first edge puts the
full shifted starting seed Z_a in Y. Since Y is now invariant under G_c,
the G_c-span of Z_a lies in Y and in V_c. Its T₂-displacement lies in
H₂ ≤ Z_c, so the normal-section control theorem puts Z_a in B_c, contrary
to the retained source escape. This proves the strict forward index in the
nonsylow small-critical-image branch without another reverse-witness choice
or a separate claim that R₃ is centralized by all of G_c.

The same critical walk transports this inequality to every original vertex.
Its application to CubeStrictBackward discharges the strict numerical
premise of source (5.7), retaining the actual conjugator and every overlapping
walk vertex. Both cover orders, all central attachments, the original
nonsylow radical and its literal quotient maps remain unchanged.

The large-critical-image strict slice, terminal (5.10)--(5.12), original
Sylow and distance-four branches, and unconditional replacement distance two
remain with the large-distance assembly owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3), (5.7) and (5.9), printed pp.866--867,919--922. The full-seed
inclusion adapts the checked general common-neighbor argument in
Sp4Four/DistanceReduction/StrictIndex/Seed; no other graph is identified
with the natural characteristic-replacement graph.
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


private theorem section_control_of_swap
    (D N A : Subgroup d.overgroup) [D.Normal] [N.Normal]
    (hQ : ⁅D,pCore 2 d.overgroup⁆ ≤ N) (hA : ⁅D,A⁆ ≤ N)
    (hswap : ∃ t ∈ A.map s.projection, t.IsSwap) :
    ⁅D,⊤⁆ ≤ N := by
  let C := commutatorPreimage ⊤ D N
  have hCN : (⊤ : Subgroup d.overgroup) ≤ normalizer (C : Set d.overgroup) :=
    commutatorPreimage_normalized ⊤ D N ⊤ le_normalizer_of_normal
      le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal
  let : C.Normal := ⟨by
    intro x hx g
    exact (mem_normalizer_iff.mp (hCN (mem_top g)) x).mp hx⟩
  have hQC : pCore 2 d.overgroup ≤ C :=
    le_commutatorPreimage le_top (by rwa [commutator_comm])
  have hAC : A ≤ C := le_commutatorPreimage le_top (by rwa [commutator_comm])
  let : (C.map s.projection).Normal := Subgroup.Normal.map inferInstance _ s.surjective
  obtain ⟨t,ht,hs⟩ := hswap
  have htC : t ∈ C.map s.projection := map_mono hAC ht
  have htop : C.map s.projection = ⊤ := by
    apply top_unique
    rw [← Equiv.Perm.closure_isSwap]
    apply (closure_le _).mpr
    rintro v hv
    obtain ⟨a,b,hab,rfl⟩ := hs
    obtain ⟨c,e,hce,rfl⟩ := hv
    obtain ⟨g,hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hab hce)
    exact hg ▸ Subgroup.Normal.conj_mem inferInstance _ htC g
  have hC : C = ⊤ := by
    have he := comap_map_eq_self (f := s.projection) (H := C)
      (s.projection_kernel ▸ hQC)
    rw [htop,comap_top] at he
    exact he.symm
  rw [commutator_comm,←hC]
  exact commutator_commutatorPreimage_le ⊤ D N le_normalizer_of_normal

include s in
private theorem small_critical_section_control_base
    (hc : DistanceTwo.CentralLayer d) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (W N : Subgroup (FreeAmalgam d.radical))
    (hWG : W ≤ stabilizer d.radical (alpha d.radical))
    (hWN : stabilizer d.radical (alpha d.radical) ≤ normalizer (W : Set (FreeAmalgam d.radical)))
    (hNN : stabilizer d.radical (alpha d.radical) ≤ normalizer (N : Set (FreeAmalgam d.radical)))
    (hQ : ⁅W,Q d.radical (alpha d.radical)⁆ ≤ N)
    (hA : ⁅W,Z d.radical z⁆ ≤ N) :
    ⁅W,stabilizer d.radical (alpha d.radical)⁆ ≤ N := by
  let W₀ := W.comap (embedM d.radical)
  let N₀ := N.comap (embedM d.radical)
  let A := (Z d.radical z).comap (embedM d.radical)
  have hWm : W₀.map (embedM d.radical) = W :=
    map_comap_eq_self (hWG.trans_eq (stabilizer_m_base d.radical))
  have hAm : A.map (embedM d.radical) = Z d.radical z := map_comap_eq_self
    ((critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical)
      rfl (replacementDistance_pos h d) p.critical).trans_eq (stabilizer_m_base d.radical))
  have hg (m : d.overgroup) : embedM d.radical m ∈ stabilizer d.radical (alpha d.radical) := by
    change embedM d.radical m ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : W₀.Normal := ⟨by
    intro w hw m
    change embedM d.radical (m*w*m⁻¹) ∈ W
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hWN (hg m)) _).mp hw⟩
  let : N₀.Normal := ⟨by
    intro n hn m
    change embedM d.radical (m*n*m⁻¹) ∈ N
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hNN (hg m)) _).mp hn⟩
  have hQ₀ : ⁅W₀,pCore 2 d.overgroup⁆ ≤ N₀ := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,hWm,
      ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    exact hQ
  have hA₀ : ⁅W₀,A⁆ ≤ N₀ := by
    apply map_le_iff_le_comap.mp
    rwa [map_commutator,hWm,hAm]
  have hh := map_mono (f := embedM d.radical)
    (section_control_of_swap s W₀ N₀ A hQ₀ hA₀ (small_critical_image_swap s hc p hsmall))
  rw [map_commutator,hWm,←MonoidHom.range_eq_map] at hh
  have hstab : stabilizer d.radical (alpha d.radical) = (embedM d.radical).range :=
    stabilizer_m_base d.radical
  rw [←hstab] at hh
  exact hh.trans (map_comap_le _ _)

include s in
/-- The full critical transposition controls every local displacement on a
normal section already fixed by the two-core. This retains the full S₆ actor. -/
theorem small_critical_section_control
    (hc : DistanceTwo.CentralLayer d) {c z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (W N : Subgroup (FreeAmalgam d.radical))
    (hWG : W ≤ stabilizer d.radical c)
    (hWN : stabilizer d.radical c ≤ normalizer (W : Set (FreeAmalgam d.radical)))
    (hNN : stabilizer d.radical c ≤ normalizer (N : Set (FreeAmalgam d.radical)))
    (hQ : ⁅W,Q d.radical c⁆ ≤ N) (hA : ⁅W,Z d.radical z⁆ ≤ N) :
    ⁅W,stabilizer d.radical c⁆ ≤ N := by
  obtain ⟨g,hgc⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ c = alpha d.radical := by
    rw [hgc,act_mVertex,mul_inv_cancel]
    rfl
  let f := (MulAut.conj g).toMonoidHom
  have base := small_critical_section_control_base s hc
    (z := act d.radical g⁻¹ z)
  rw [←hbase] at base
  have hh := base (p.act g⁻¹)
    (by simpa only [Q_act,Z_act,inv_inv,relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) _ _ (MulAut.conj g).injective] using hsmall)
    (W.map f) (N.map f)
    (by simpa only [stabilizer_act,inv_inv] using map_mono (f := f) hWG)
    (by rw [stabilizer_act,inv_inv]; exact (map_mono hWN).trans (W.le_normalizer_map f))
    (by rw [stabilizer_act,inv_inv]; exact (map_mono hNN).trans (N.le_normalizer_map f))
    (by simpa only [Q_act,inv_inv,f,map_commutator] using map_mono (f := f) hQ)
    (by simpa only [Z_act,inv_inv,f,map_commutator] using map_mono (f := f) hA)
  rw [stabilizer_act,inv_inv,←map_commutator] at hh
  exact (map_le_map_iff_of_injective (MulAut.conj g).injective).mp hh

include s in
/-- In the actual small critical branch, the endpoint comparison collapses
an escaping local span's centralizer orbit once that orbit is invariant. -/
theorem small_critical_span_collapse
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    {c z a : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (ha : color d.radical a = false) (hca : (cosetGraph d.radical).dist c a ≤ 2)
    (Y P : Subgroup (FreeAmalgam d.radical))
    (hYV : Y ≤ V d.radical a)
    (hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hZY : Z d.radical c ≤ Y) (hPG : P ≤ stabilizer d.radical c)
    (hWN : stabilizer d.radical c ≤ normalizer (conjugateSpanBy Y P : Set (FreeAmalgam d.radical)))
    (hcontrol : ⁅conjugateSpanBy Y P,Z d.radical z⁆ ≤
      ⁅conjugateSpanBy Y P,Z d.radical z ⊓ Q d.radical c⁆ ⊔ ⁅Z d.radical c,Z d.radical z⁆) :
    conjugateSpanBy Y P = Y := by
  let W := conjugateSpanBy Y P
  let N := ⁅W,Q d.radical c⁆ ⊔ Z d.radical c
  have hYQ : Y ≤ Q d.radical c := hYV.trans
    (V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) ha (by
      change (cosetGraph d.radical).dist a c + 2 < replacementDistance h d
      rw [SimpleGraph.dist_comm]
      omega))
  have hWQ : W ≤ Q d.radical c := conjugateSpanBy_le hYQ (hPG.trans (Q_normalized d.radical c))
  have hNN : stabilizer d.radical c ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [N]
    rw [Subgroup.map_sup,map_commutator,mem_normalizer_iff_map_conj_eq.mp (hWN hg),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical c hg),
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical c hg)]
  have hcrit : ⁅Z d.radical c,Z d.radical z⁆ ≤ Z d.radical c :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical c)
  have hcomm : ⁅W,stabilizer d.radical c⁆ ≤ N :=
    small_critical_section_control s hc p hsmall W N
      (hWQ.trans (fun _ hx => hx.1)) hWN hNN le_sup_left
      (hcontrol.trans (sup_le_sup (commutator_mono le_rfl inf_le_right) hcrit))
  let := finite_stabilizer d.radical c
  let : Finite (Q d.radical c) := Finite.of_injective
    (inclusion (show Q d.radical c ≤ stabilizer d.radical c from fun _ hx => hx.1))
    (inclusion_injective _)
  exact conjugateSpanBy_eq_of_nilpotent_commutator_bound Y P (Q d.radical c) (Z d.radical c)
    (Q_isPGroup d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d) c p.start_color).isNilpotent hWQ
    ((Q_le_stabilizer_of_dist_le_two c a p.start_color ha hca).trans hYN) hZY
    ((commutator_mono le_rfl hPG).trans hcomm)

private theorem acting_seed_le_local_span
    {c a t : Vertex d.radical} (hc : color d.radical c = false)
    (ha : color d.radical a = false)
    (hct : Adjacent d.radical c t) (hat : Adjacent d.radical a t) :
    Z d.radical a ≤ localZSpan d.radical c a := by
  conv_lhs => rw [Z,if_pos ha]
  apply iSup_le
  intro v
  apply iSup_le
  intro hav
  have hv : color d.radical v ≠ false := by
    simpa only [ha] using (adjacent_color_ne d.radical hav).symm
  obtain ⟨g,hg,hgv⟩ := stabilizer_transitive_neighbors d.radical a hat hav
  have hseed : Z d.radical t ≤ localZSpan d.radical c a :=
    (adjacent_Z_le d.radical hc hct).trans (Z_le_localZSpan d.radical c a)
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hseed
  have he : (localZSpan d.radical c a).map (MulAut.conj g⁻¹).toMonoidHom =
      localZSpan d.radical c a := mem_normalizer_iff_map_conj_eq.mp
    (localZSpan_normalized d.radical c a ((stabilizer d.radical a).inv_mem hg))
  rw [he,←Z_act,hgv] at hh
  simpa only [Z,if_neg hv] using hh

/-- The source (5.9) strict forward slice in the original nonsylow,
small-critical-image branch. The full endpoint comparison collapses W to Y;
the original nonzero forward commutator then supplies the noncore actor. -/
theorem nonsylow_small_forward_slice_strict_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  by_contra! hslice
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨z,q,hd,hover,hpre,hi,y,hy,hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,hcard,hHCa,
    hcomm,hZaQ,hYQ,hDQ,hWQ,hZaV,hZaB,hJcard,hJseed,hJedge,hJne,
    hXall,hA₀,hR₃,hRDA,hxdata,hfull,hnot,halign,hYdisp,hYker,hWdisp,hWker,
    hNcard,hWnot,hWspan,hWcontrol,hWN,hchoices⟩ :=
    nonsylow_small_shifted_span_control_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hns p hslice hsmall
  let c := p.walk.getVert 2
  let a := act d.radical y⁻¹ (alpha d.radical)
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let T₂ := T.map (MulAut.conj y).toMonoidHom
  let H₂ := (⁅U d.radical c,T⁆ : Subgroup (FreeAmalgam d.radical)).map (MulAut.conj y).toMonoidHom
  let Y := (localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  have hyG : y ∈ stabilizer d.radical c := Ltilde_le_stabilizer c hy
  have ha : color d.radical a = false := by rw [action_preserves_color]; rfl
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hca : (cosetGraph d.radical).dist c a = 2 := by
    have hfix : act d.radical y⁻¹ c = c := (stabilizer d.radical c).inv_mem hyG
    have hh := dist_act d.radical y⁻¹ c (alpha d.radical)
    rw [hfix,SimpleGraph.dist_comm (u := c) (v := alpha d.radical)] at hh
    exact hh.trans (p.dist_start (by omega))
  have hcollapse : conjugateSpanBy Y P = Y :=
    small_critical_span_collapse s hc hb q (by rw [hi]; decide) ha hca.le
      Y P hYV hYN hZcY inf_le_left hWN (by rwa [hWker] at hWcontrol)
  have hYG : stabilizer d.radical c ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rwa [hcollapse] at hWN
  have hT₂G : T₂ ≤ stabilizer d.radical c :=
    (show T₂ ≤ Q d.radical a by
      change T₂ = Q d.radical a ⊓ _ at hT
      rw [hT]
      exact inf_le_left).trans
      (Q_le_stabilizer_of_dist_le_two a c ha q.start_color (by rw [SimpleGraph.dist_comm]; exact hca.le))
  have hcommU : ⁅U d.radical c,T₂⁆ = H₂ := by
    have hUm : (U d.radical c).map (MulAut.conj y).toMonoidHom = U d.radical c :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized c hyG)
    dsimp only [H₂]
    rw [map_commutator,hUm]
  have hHc : H₂ ≤ Z d.radical c :=
    (hcommU.symm.le.trans (le_normalizer_iff_commutator_le_left.mp
      (hT₂G.trans (U_normalized c)))).trans (DistanceEight.U_le_Z d.radical c)
  have hT₂ne : ¬ T₂ ≤ Q d.radical c := by
    intro hle
    have he : ⁅U d.radical c,T₂⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono (DistanceEight.U_le_Z d.radical c) hle).trans_eq
        (Z_centralizes_Q d.radical c q.start_color))
    rw [hcommU] at he
    change Nat.card H₂ = 2 at hcard
    rw [he,card_bot] at hcard
    omega
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c (p.walk.getVert 1) := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hZaY : Z d.radical a ≤ Y := by
    have hh := map_mono (f := (MulAut.conj y).toMonoidHom)
      (acting_seed_le_local_span (d := d) q.start_color rfl hct hat)
    simpa only [a,Y,c,Z_act,inv_inv] using hh
  let E := conjugateSpanBy (Z d.radical a) (stabilizer d.radical c)
  have hEY : E ≤ Y := conjugateSpanBy_le hZaY hYG
  have hEV : E ≤ V d.radical c :=
    conjugateSpanBy_le hZaV (DistanceEight.V_normalized d.radical c)
  have hEB := normalized_radius_le_slice_of_actor_at s hb2 q.start_color E T₂ hEV
    (le_normalizer_conjugateSpanBy _ _) hT₂G hT₂ne
    (((commutator_mono hEY le_rfl).trans hcomm).trans hHc)
  exact hZaB ((le_conjugateSpanBy _ _).trans hEB)

/-- Vertex-transitive transport of the strict forward slice uses the same
critical walk, second vertex and Baumann subgroup. -/
theorem nonsylow_small_forward_slice_strict_at_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g⁻¹ a) (act d.radical g⁻¹ a'),
      p₀.walk.getVert 2 = act d.radical g⁻¹ (p.walk.getVert 2) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hvert⟩ := hpact
  have hsmall₀ : (Q d.radical (act d.radical g⁻¹ a')).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
    exact hsmall
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := replacementGeometry h d) (by change 2 < replacementDistance h d; omega)
    g⁻¹ a p.start_color
  rw [hbase,inv_inv] at hB
  have hi := nonsylow_small_forward_slice_strict_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p₀ hsmall₀
  rw [hvert,U_act,inv_inv,hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  exact hi

include e hz hn in
/-- The literal source (5.7) backward shift now has its strict-slice
premise discharged in the nonsylow small-critical branch, at every vertex. -/
theorem nonsylow_small_backward_path_of_four_lt_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    ∃ t, Adjacent d.radical a t ∧
      ∃ g ∈ stabilizer d.radical a,
        act d.radical g (p.walk.getVert 1) = t ∧
        2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g (p.walk.getVert 2))) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g (p.walk.getVert 2)) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1=t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2)=p.walk.getVert i := by
  apply nonsylow_strict_backward_path_at_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p
  · exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by
        have hl : p.walk.length = replacementDistance h d := p.length_eq_b
        omega)))
  · exact nonsylow_small_forward_slice_strict_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns p hsmall

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
