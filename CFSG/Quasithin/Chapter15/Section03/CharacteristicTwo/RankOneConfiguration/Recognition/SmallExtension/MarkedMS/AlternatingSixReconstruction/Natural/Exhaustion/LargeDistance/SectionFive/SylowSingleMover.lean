module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelMovement

public import Theory.GroupTheory.NormalizedSupConsequences
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelMovement
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent

/-!
# One mover for the critical line and the common full kernel

In the order-sixteen radical-image branch above distance four, unequal
neighboring small movers give fixed index eight for the edge core on the
whole starting seed. The moved-cover calculation transfers to this full
seed because the central edge attachment is fixed by the edge core.

When the edge core moves the small critical line, an unequal neighboring
mover group moves both that line and the orbit-fixed critical kernel.
A group cannot be covered by two proper subgroups, so one element moves
both. Its displacement on the common kernel is the whole edge displacement,
of order two. The corresponding commutator homomorphism has kernel of index
two. Comparing indices four and eight identifies this element's fixed
subgroup on the common kernel with the fixed subgroup of the whole edge core.

At the second vertex the same element transports the critical path while
fixing its first three vertices. Both full path kernels, their join and their
common kernel are retained. The final application uses the literal restricted
original radical and its embedding; the two possible moved covers and their
central attachments are preserved. Small critical index, unequal movers and
movement of the critical line remain explicit branch hypotheses. The source's
new-neighbor selection and terminal distance exclusion remain to be proved.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the local small-mover argument of (5.4)--(5.5), printed pp.915--917,
and the critical-kernel comparisons in (5.7)--(5.9), printed pp.919--921.
-/

public noncomputable section
open Theory.GroupTheory
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped commutatorElement Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSingleMover
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Unequal neighboring movers force the whole edge core to have fixed index
exactly eight on the full starting seed, including its central attachment. -/
theorem sixteen_unequal_edge_fixed_index_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical a) = 8 := by
  let T := Q d.radical t
  let E := SmallMover.join (U d.radical c) (Q d.radical c) T 4
  have hET : E ≤ T := SmallMover.join_le _ _ _ _
  have hiE := SylowKernelMovement.sixteen_unequal_neighbor_fixed_index_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat hct hne
  change (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 8 at hiE
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  have hlarge : 4 < (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    have hh := relIndex_le_of_le_left (centralizer_le hET)
      (index_ne_zero_of_finite : (centralizer (T : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≠ 0)
    omega
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨i,hinj,hir,hiR,_,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc ha hat
  have hTS : T ≤ stabilizer d.radical a := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hm : (T.comap i).map i = T := map_comap_eq_self (hTS.trans_eq hir.symm)
  have hTR : T.comap i ≤ d.radical := by
    have hh := comap_mono (f := i) (show T ≤ Q d.radical t from le_rfl)
    rwa [←hiR,comap_map_eq_self_of_injective hinj] at hh
  have hidx := SmallMover.centralizer_index_map i hinj (replacementMoved d) (T.comap i)
  rw [hiU,hm] at hidx
  have hiT : (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 8 := by
    rw [hidx]
    exact SylowKernelMovement.cover_two_group_fixed_index_eight s _
      ((replacement_radical_isPGroup h d).of_injective (inclusion hTR)
        (inclusion_injective hTR)) (by rwa [←hidx])
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all
  have hedge : Z d.radical t ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
    intro z hz
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  let C := Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))
  have hCZ : C ≤ Z d.radical a := inf_le_left
  let : Finite C := Finite.of_injective (inclusion hCZ) (inclusion_injective _)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a ha
  have hn : C ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans (Z_le_stabilizer d.radical a)).trans (U_normalized a)
  have hjoin : U d.radical a ⊔ C = Z d.radical a := by
    apply le_antisymm (sup_le (DistanceEight.U_le_Z d.radical a) hCZ)
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d ha hat]
    exact sup_le le_sup_left (le_sup_right.trans' (le_inf
      (adjacent_Z_le d.radical ha hat) hedge))
  have hindex := relIndex_sup_of_normalizes (U d.radical a) C hn
  rw [hjoin] at hindex
  change (Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))).relIndex
    (Z d.radical a) = C.relIndex (U d.radical a) at hindex
  rw [inf_relIndex_left] at hindex
  have hCU : C ⊓ U d.radical a = centralizer (T : Set (FreeAmalgam d.radical)) ⊓ U d.radical a := by
    ext z
    exact ⟨fun hz => ⟨hz.1.2,hz.2⟩,fun hz => ⟨⟨DistanceEight.U_le_Z d.radical a hz.2,hz.1⟩,hz.2⟩⟩
  have heq : C.relIndex (U d.radical a) =
      (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [←inf_relIndex_right C, hCU,inf_relIndex_right]
  exact hindex.trans (heq.trans hiT)

include e hz hn in
/-- A single element of the unequal neighboring mover moves both the critical
line and the common orbit-fixed kernel, and generates its entire edge
commutator of order two. -/
theorem sixteen_unequal_single_mover_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hct : Adjacent d.radical c (p.walk.getVert 1))
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical (p.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (p.walk.getVert 1)) 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let E := SmallMover.join (U d.radical c) (Q d.radical c) T 4
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    ∃ x ∈ E, x ∈ T ∧
      x ∉ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      x ∉ centralizer (F : Set (FreeAmalgam d.radical)) ∧
      ⁅F,zpowers x⁆ = ⁅F,E⁆ ∧ ⁅F,zpowers x⁆ = ⁅F,T⁆ ∧
      Nat.card (⁅F,zpowers x⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅F,zpowers x⁆ ≤ Z d.radical (p.walk.getVert 1) ∧
      ⁅F,zpowers x⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
  classical
  let T := Q d.radical (p.walk.getVert 1)
  let E := SmallMover.join (U d.radical c) (Q d.radical c) T 4
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
  have hd := SylowKernelMovement.sixteen_unequal_common_kernel_displacement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hct hne hmove
  change ⁅F,E⁆ = ⁅F,T⁆ ∧ Nat.card (⁅F,E⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
    ⁅F,E⁆ ≤ Z d.radical (p.walk.getVert 1) ∧ ⁅F,E⁆ ≤ centralizer (T : Set _) at hd
  let := finite_Z d.radical (p.walk.getVert 1)
  let : Finite (⁅F,E⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hd.2.2.1) (inclusion_injective _)
  have hEC : ¬ E ≤ centralizer (D : Set (FreeAmalgam d.radical)) := by
    obtain ⟨y,hy,_,hyD,_⟩ := SylowAdjacent.sixteen_unequal_neighbor_moves_line_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hct hne hmove
    intro hh
    exact hyD (hh hy)
  have hEF : ¬ E ≤ centralizer (F : Set (FreeAmalgam d.radical)) := by
    intro hh
    have hzFE : ⁅F,E⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hh
    exact ((one_lt_card_iff_ne_bot (⁅F,E⁆ : Subgroup (FreeAmalgam d.radical))).mp
      (by omega)) hzFE
  have hex : ∃ x ∈ E, x ∉ centralizer (D : Set (FreeAmalgam d.radical)) ∧
      x ∉ centralizer (F : Set (FreeAmalgam d.radical)) := by
    by_contra! hh
    have hcover : (E : Set (FreeAmalgam d.radical)) ⊆
        (centralizer (D : Set (FreeAmalgam d.radical)) : Set _) ∪
          (centralizer (F : Set (FreeAmalgam d.radical)) : Set _) := by
      intro x hx
      by_cases hc : x ∈ centralizer (D : Set (FreeAmalgam d.radical))
      · exact Or.inl hc
      · exact Or.inr (hh x hx hc)
    rcases SubgroupClass.subset_union.mp hcover with hD | hF
    · exact hEC hD
    · exact hEF hF
  obtain ⟨x,hx,hxD,hxF⟩ := hex
  have hET : E ≤ T := SmallMover.join_le _ _ _ _
  have hle : ⁅F,zpowers x⁆ ≤ ⁅F,E⁆ := commutator_mono le_rfl (zpowers_le.mpr hx)
  let : Finite (⁅F,zpowers x⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hle) (inclusion_injective _)
  have hnz : ⁅F,zpowers x⁆ ≠ ⊥ := by
    intro hh
    have hc : zpowers x ≤ centralizer (F : Set (FreeAmalgam d.radical)) :=
      commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm])
    exact hxF (hc (mem_zpowers x))
  have hpos := (one_lt_card_iff_ne_bot
    (⁅F,zpowers x⁆ : Subgroup (FreeAmalgam d.radical))).mpr hnz
  have hbound := card_le_of_le hle
  have heq : ⁅F,zpowers x⁆ = ⁅F,E⁆ := eq_of_le_of_card_ge hle (by omega)
  exact ⟨x,hx,hET hx,hxD,hxF,heq,heq.trans hd.1,heq ▸ hd.2.1,
    heq ▸ hd.2.2.1,heq ▸ hd.2.2.2⟩

private theorem single_mover_fixed_index {H : Type*} [Group H]
    (F D : Subgroup H) [Finite D] (x : H)
    (hc : ⁅F,zpowers x⁆ ≤ D) (hDF : D ≤ centralizer (F : Set H))
    (hcard : Nat.card D = 2) (hx : x ∉ centralizer (F : Set H)) :
    (centralizer ({x} : Set H)).relIndex F = 2 := by
  have hvalue (a : F) : ⁅x,(a : H)⁆ ∈ D := by
    apply hc
    rw [commutator_comm]
    exact commutator_mem_commutator (mem_zpowers x) a.property
  let f : F →* D := {
    toFun a := ⟨⁅x,(a : H)⁆,hvalue a⟩
    map_one' := Subtype.ext (by simp)
    map_mul' a b := by
      apply Subtype.ext
      change ⁅x,(a : H)*(b : H)⁆ = ⁅x,(a : H)⁆ * ⁅x,(b : H)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hh := mem_centralizer_iff.mp (hDF (hvalue b)) a a.property
      calc
        _ = ⁅x,(a : H)⁆ * ((a : H)*⁅x,(b : H)⁆) * (a : H)⁻¹ := by group
        _ = _ := by rw [hh]; group }
  have hk : f.ker = (centralizer ({x} : Set H)).subgroupOf F := by
    ext a
    change (⟨⁅x,(a : H)⁆,_⟩ : D) = 1 ↔ _
    rw [Subtype.ext_iff]
    change ⁅x,(a : H)⁆ = 1 ↔ (a : H) ∈ centralizer ({x} : Set H)
    rw [commutatorElement_eq_one_iff_mul_comm,mem_centralizer_singleton_iff,eq_comm]
  have hnz : f.range ≠ ⊥ := by
    intro hbot
    apply hx
    intro a ha
    have hh : f ⟨a,ha⟩ = 1 := by
      have hm : f ⟨a,ha⟩ ∈ f.range := ⟨⟨a,ha⟩,rfl⟩
      simpa only [hbot,mem_bot] using hm
    have hz : ⁅x,a⁆ = 1 := congrArg Subtype.val hh
    exact (commutatorElement_eq_one_iff_mul_comm.mp hz).symm
  have hpos := (one_lt_card_iff_ne_bot f.range).mpr hnz
  have hbound := Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
  change ((centralizer ({x} : Set H)).subgroupOf F).index = 2
  rw [←hk,index_ker]
  omega

include e hz hn in
/-- The second mover transports the critical path and retains both full
kernels. On their intersection, its fixed subgroup is exactly the subgroup
fixed by the whole first edge core. -/
theorem sixteen_second_single_mover_path_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hne : SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
      (Q d.radical (p.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (p.walk.getVert 1)) 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let E := SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2)) T 4
    ∃ x ∈ E, x ∈ T ∧
      x ∉ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical x⁻¹ a'),
        (∀ i, q.walk.getVert i = act d.radical x⁻¹ (p.walk.getVert i)) ∧
        q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = p.walk.getVert 2 ∧
        (Q d.radical (act d.radical x⁻¹ a')).relIndex (Z d.radical a) = 2 ∧
        let K := Z d.radical a ⊓ Q d.radical a'
        let K' := Z d.radical a ⊓ Q d.radical (act d.radical x⁻¹ a')
        let F := K ⊓ K'
        K ⊔ K' = Z d.radical a ∧ F.relIndex (Z d.radical a) = 4 ∧
          F = Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _) ∧
          T ≤ normalizer (F : Set (FreeAmalgam d.radical)) ∧
          (centralizer ({x} : Set (FreeAmalgam d.radical))).relIndex F = 2 ∧
          F ⊓ centralizer ({x} : Set (FreeAmalgam d.radical)) =
            Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical)) ∧
          ⁅F,zpowers x⁆ = ⁅F,E⁆ ∧ ⁅F,zpowers x⁆ = ⁅F,T⁆ ∧
          Nat.card (⁅F,zpowers x⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
          ⁅F,zpowers x⁆ ≤ Z d.radical (p.walk.getVert 1) ∧
          ⁅F,zpowers x⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)) ∧
          (Q d.radical a ⊔ Z d.radical a') ⊓
            (Q d.radical a ⊔ Z d.radical (act d.radical x⁻¹ a')) = Q d.radical a := by
  let T := Q d.radical (p.walk.getVert 1)
  let E := SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2)) T 4
  let F₀ := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
  have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨x,hx,hxt,hxD,hxF,hxE,hxT,hxcard,hxseed,hxcent⟩ :=
    sixteen_unequal_single_mover_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hcard p hsmall hct hne hmove
  have hxnorm : x ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a := ⟨(Q d.radical _).le_normalizer hxt,
        hxt.2 a (adjacent_symm d.radical hat)⟩
  obtain ⟨q,hq,_,hi,hjoin,hindex,hnorm,hcore⟩ :=
    SylowKernelPair.small_moving_kernel_path_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall x hxnorm hxD
  let K := Z d.radical a ⊓ Q d.radical a'
  let K' := Z d.radical a ⊓ Q d.radical (act d.radical x⁻¹ a')
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat
  rw [hT] at hnorm
  have hcontrol := SylowCommonKernel.moving_common_kernel_edge_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall (hT.symm ▸ hmove)
  dsimp only at hcontrol
  rw [hT] at hcontrol
  have hF : F₀ = ⨅ t : T, K.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom := hcontrol.1
  have hFK : F₀ ≤ K := by
    rw [hF]
    have hh := iInf_le (fun t : T => K.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom) 1
    have he : (MulAut.conj ((1 : T) : FreeAmalgam d.radical)).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro y
      change (1 : FreeAmalgam d.radical) * y * (1 : FreeAmalgam d.radical)⁻¹ = y
      simp only [one_mul,inv_one,mul_one]
    rwa [he,Subgroup.map_id] at hh
  have hFK' : F₀ ≤ K' := by
    rw [hF]
    have hh := iInf_le (fun t : T => K.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom) ⟨x,hxt⟩
    have hxZ : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a hxnorm.2)
    have hkm : K.map (MulAut.conj x).toMonoidHom = K' := by
      dsimp only [K,K']
      rw [map_inf _ _ _ (MulAut.conj x).injective,hxZ,Q_act,inv_inv]
    exact hh.trans_eq hkm
  have hFpair : F₀ = K ⊓ K' := by
    have hle : F₀ ≤ K ⊓ K' := le_inf hFK hFK'
    have hi := relIndex_mul_relIndex F₀ (K ⊓ K') (Z d.radical a) hle
      (inf_le_left.trans (show K ≤ Z d.radical a from inf_le_left))
    rw [hindex,hcontrol.2.1] at hi
    exact le_antisymm hle (relIndex_eq_one.mp (by omega))
  have hfnorm : T ≤ normalizer (F₀ : Set (FreeAmalgam d.radical)) := by
    rwa [hFpair]
  have hFZ : F₀ ≤ Z d.radical a := inf_le_left
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hDC : ⁅F₀,zpowers x⁆ ≤ centralizer (F₀ : Set (FreeAmalgam d.radical)) :=
    ((commutator_mono le_rfl (zpowers_le.mpr hxt)).trans
      (le_normalizer_iff_commutator_le_left.mp hfnorm)).trans
        (hFZ.trans ((le_centralizer (Z d.radical a)).trans (centralizer_le hFZ)))
  let := finite_Z d.radical (p.walk.getVert 1)
  let : Finite (⁅F₀,zpowers x⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hxseed) (inclusion_injective _)
  have hfixed := single_mover_fixed_index F₀ ⁅F₀,zpowers x⁆ x le_rfl hDC hxcard hxF
  have hfull := sixteen_unequal_edge_fixed_index_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat hct hne
  have horbit := SylowKernelPair.small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  dsimp only at horbit
  rw [hT] at horbit
  let C := Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))
  have hCF : C ≤ F₀ := inf_le_inf_left _ (centralizer_le horbit.1)
  have hfullC : C.relIndex (Z d.radical a) = 8 := by
    change (Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical a) = 8
    rw [inf_relIndex_left]
    exact hfull
  have hFindex : F₀.relIndex (Z d.radical a) = 4 := hcontrol.2.1
  have hmul := relIndex_mul_relIndex C F₀ (Z d.radical a) hCF inf_le_left
  rw [hFindex,hfullC] at hmul
  have hidxC : C.relIndex F₀ = 2 := by omega
  have hCx : C ≤ F₀ ⊓ centralizer ({x} : Set (FreeAmalgam d.radical)) := by
    refine le_inf hCF ?_
    intro z hz
    exact mem_centralizer_singleton_iff.mpr ((hz.2 x hxt).symm)
  have hmulx := relIndex_mul_relIndex C
    (F₀ ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))) F₀ hCx inf_le_left
  have hxf : (F₀ ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))).relIndex F₀ = 2 := by
    rw [inf_relIndex_left]
    exact hfixed
  rw [hxf,hidxC] at hmulx
  have hfixedKernel : F₀ ⊓ centralizer ({x} : Set (FreeAmalgam d.radical)) = C :=
    le_antisymm (relIndex_eq_one.mp (by omega)) hCx
  change ⁅F₀,zpowers x⁆ = ⁅F₀,E⁆ at hxE
  change ⁅F₀,zpowers x⁆ = ⁅F₀,T⁆ at hxT
  change Nat.card (⁅F₀,zpowers x⁆ : Subgroup (FreeAmalgam d.radical)) = 2 at hxcard
  change ⁅F₀,zpowers x⁆ ≤ Z d.radical (p.walk.getVert 1) at hxseed
  change ⁅F₀,zpowers x⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)) at hxcent
  rw [hFpair] at hfixed hfixedKernel hxE hxT hxcard hxseed hxcent
  refine ⟨x,hx,hxt,hxD,q,hq,?_,?_,hi,hjoin,hindex,hFpair.symm,hnorm,
    hfixed,hfixedKernel,hxE,hxT,hxcard,hxseed,hxcent,hcore⟩
  · rw [hq]
    exact (stabilizer d.radical (p.walk.getVert 1)).inv_mem hxt.1
  · rw [hq]
    exact (stabilizer d.radical (p.walk.getVert 2)).inv_mem
      (hxt.2 _ (adjacent_symm d.radical hct))

include e hz hn in
/-- Application to the literal restricted original radical and its embedding.
In this order-sixteen branch the two full path kernels have a nontrivial
common displacement, and the second mover has fixed index eight on either
permitted moved cover. No Sylow hypothesis on the original input is added. -/
theorem original_sylow_second_single_mover_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hne : SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
        (((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)) 4 ≠
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)) 4)
    (hmove : ¬ ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) ≤
      centralizer ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let E := SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2)) T 4
    (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical (alpha d.radical)) = 8 ∧
      ∃ x ∈ E, x ∈ T ∧
        x ∉ centralizer ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
          Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) (act d.radical x⁻¹ a'),
          (∀ i, q.walk.getVert i = act d.radical x⁻¹ (p.walk.getVert i)) ∧
          q.walk.getVert 1 = beta d.radical ∧ q.walk.getVert 2 = p.walk.getVert 2 ∧
          (Q d.radical (act d.radical x⁻¹ a')).relIndex (Z d.radical (alpha d.radical)) = 2 ∧
          let K := Z d.radical (alpha d.radical) ⊓ Q d.radical a'
          let K' := Z d.radical (alpha d.radical) ⊓ Q d.radical (act d.radical x⁻¹ a')
          let F := K ⊓ K'
          K ⊔ K' = Z d.radical (alpha d.radical) ∧ F.relIndex (Z d.radical (alpha d.radical)) = 4 ∧
            F = Z d.radical (alpha d.radical) ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _) ∧
            T ≤ normalizer (F : Set (FreeAmalgam d.radical)) ∧
            (centralizer ({x} : Set (FreeAmalgam d.radical))).relIndex F = 2 ∧
            F ⊓ centralizer ({x} : Set (FreeAmalgam d.radical)) =
              Z d.radical (alpha d.radical) ⊓ centralizer (T : Set (FreeAmalgam d.radical)) ∧
            ⁅F,zpowers x⁆ = ⁅F,E⁆ ∧ ⁅F,zpowers x⁆ = ⁅F,T⁆ ∧
            Nat.card (⁅F,zpowers x⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
            ⁅F,zpowers x⁆ ≤ Z d.radical (beta d.radical) ∧
            ⁅F,zpowers x⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)) ∧
            (Q d.radical (alpha d.radical) ⊔ Z d.radical a') ⊓
              (Q d.radical (alpha d.radical) ⊔ Z d.radical (act d.radical x⁻¹ a')) =
                Q d.radical (alpha d.radical) := by
  have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat
  rw [hfirst,SylowSmallNormalizer.four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb] at hT
  have hne' : SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
      (Q d.radical (p.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4 := by rwa [hfirst,←hT]
  have hm : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [hfirst,←hT]
  have hi := SylowKernelMovement.sixteen_unequal_neighbor_fixed_index_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat hct hne'
  have hp := sixteen_second_single_mover_path_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hne' hm
  dsimp only at hi hp ⊢
  rw [hfirst,←hT] at hi hp
  exact ⟨hi,hp⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSingleMover
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
