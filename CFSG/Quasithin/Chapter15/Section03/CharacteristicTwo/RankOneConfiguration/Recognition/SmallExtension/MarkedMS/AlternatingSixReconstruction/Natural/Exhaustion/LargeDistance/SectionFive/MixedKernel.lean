module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedSmallRadius
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MidpointCoreLine

/-!
# The nonzero reverse-kernel alternative for a mixed-plane replacement

The order-two reverse-kernel commutator is fixed by the entire relative
normalizer at the selected backward vertex, but is noncentral in that
vertex stabilizer and in the endpoint stabilizer. It lies in both the selected and last edge seeds, hence
in the original starting and predecessor seeds. All kernels and central
attachments are retained.

Nonvanishing also forces the predecessor core to fill the last edge
kernel modulo the endpoint core. Indeed the original starting seed gives
an index-two subgroup of the order-four edge image. If the predecessor
core had that same image it would fix the full reverse kernel. A larger
image must fill the mixed plane. This is a conclusion about the actual
predecessor core, not an inference from a selected span.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii) and (5.7)--(5.8), printed pp.866--867 and 919--920.
The final consumer applies these estimates to the previously constructed
backward alternative in the literal replacement graph. Eliminating its
nonzero branch, the larger Sylow branches, and the distance-four residual
exclusions remain necessary for LargeDistanceInput.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedKernel
local notation "S" => Equiv.Perm (Fin 6)

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem fixed_mod_central_normalizes {H : Type*} [Group H]
    (A Q D : Subgroup H) (hAQ : A ≤ normalizer (Q : Set H))
    (hDQ : D ≤ normalizer (Q : Set H))
    (hDA : ⁅D,A⁆ ≤ centralizer (Q : Set H)) :
    D ≤ normalizer ((⁅A,Q⁆ : Subgroup H) : Set H) := by
  apply le_normalizer_closure_iff.mpr
  rintro d hd _ ⟨a,ha,q,hq,rfl⟩
  have hq' : d*q*d⁻¹ ∈ Q := (mem_normalizer_iff.mp (hDQ hd) q).mp hq
  have hk : ⁅d,a⁆ ∈ centralizer (Q : Set H) := hDA (commutator_mem_commutator hd ha)
  have hcomm : ⁅a,d*q*d⁻¹⁆ ∈ Q :=
    le_normalizer_iff_commutator_le_right.mp hAQ (commutator_mem_commutator ha hq')
  have hzero : ⁅⁅d,a⁆,d*q*d⁻¹⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hk _ hq').symm
  rw [conjugate_commutatorElement,show d*a*d⁻¹ = ⁅d,a⁆*a by
    simp [commutatorElement_def,mul_assoc],commutatorElement_mul_left_eq_conj_mul,
    hzero,mul_one,←hk _ hcomm,mul_inv_cancel_right]
  exact commutator_mem_commutator ha hq'

private theorem kernel_line_not_central
    (s : FullSymmetricAction h e hz hn d)
    (hc : DistanceTwo.CentralLayer d)
    {a' c t : Vertex d.radical}
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hne : ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≠ ⊥) :
    ¬ ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≤
      centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
  intro hcentral
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hKG : K ≤ stabilizer d.radical c :=
    (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc c hcol
  let A := K.comap i
  have hmA : A.map i = K := map_comap_eq_self (hKG.trans_eq hir.symm)
  have hcA : ⁅replacementMoved d,A⁆ ≤ center d.overgroup := by
    intro x hx
    apply mem_center_iff.mpr
    intro m
    apply hi
    simp only [map_mul]
    apply hcentral
    · have hh := mem_map_of_mem i hx
      rw [map_commutator,hmA,hiU,commutator_comm] at hh
      exact commutator_mono le_rfl (DistanceEight.U_le_Z d.radical c) hh
    · rw [←hir]
      exact ⟨m,rfl⟩
  have hKQ := map_mono (f := i) (cover_central_commutator_forces_core s A hcA)
  rw [hmA,hiQ] at hKQ
  apply hne
  rw [commutator_comm]
  exact le_bot_iff.mp ((commutator_mono le_rfl hKQ).trans_eq
    (Z_centralizes_Q d.radical c hcol))


/-- An order-two commutator with an actor in the mixed edge kernel is
fixed by the whole relative normalizer at the original vertex. It lies in
the common edge seed, with no removal of a central attachment. -/
theorem mixed_small_edge_commutator_fixed_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t)
    (hcard : Nat.card (⁅A,Z d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) = 2) :
    ⁅A,Z d.radical c⁆ ≤ Z d.radical t ∧
      ⁅A,Z d.radical c⁆ ≤ centralizer
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
  let N := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical c
  let D := ⁅A,Z d.radical c⁆
  have htG : Q d.radical t ≤ stabilizer d.radical c :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hAN := (hA.trans htG).trans (Z_normalized d.radical c)
  have hmove : ⁅N,A⁆ ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    ((commutator_mono le_rfl hA).trans
      (SylowNormalizer.mixed_relative_normalizer_commutator_knownSimple hb u him hcol hct)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical c hcol)))
  have hDN : N ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    fixed_mod_central_normalizes A (Z d.radical c) N hAN
      (inf_le_right.trans (Z_normalized d.radical c)) hmove
  have hfix : D ≤ centralizer (N : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (hDN.trans (normalizer_le_centralizer_of_card_two D hcard))
  have hDZ : D ≤ Z d.radical c := le_normalizer_iff_commutator_le_right.mp hAN
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcol] at hh
    cases he : color d.radical t <;> simp_all
  have hZQ : Z d.radical c ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c hcol)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant c hcol]
    exact replacementDistance_pos h d
  have htN : Q d.radical t ≤ N := le_inf (Q d.radical t).le_normalizer htG
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c hcol
  refine ⟨?_,hfix⟩
  intro x hx
  rw [Z,if_neg (by simp [ht])]
  exact mem_omegaCenter_iff.mpr
    ⟨(hDZ.trans (hZQ.trans (Q_le_adjacent_h d.radical ht hct))) hx,
      elemPow_eq_one_of_isElementaryAbelian x (hDZ hx),
      (hfix.trans (centralizer_le htN)) hx⟩

/-- A nonzero reverse-kernel commutator forces the entire predecessor
core to fill the last edge image. Its image has order four and the join
with the endpoint core is exactly the original last edge kernel. -/
theorem mixed_nonzero_kernel_predecessor_fills_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hne : ⁅Z d.radical a' ⊓ Q d.radical a,
      Q d.radical (p.walk.getVert (p.walk.length-2))⁆ ≠ ⊥) :
    Q d.radical a' ⊔ Q d.radical (p.walk.getVert (p.walk.length-2)) =
      Q d.radical (p.walk.getVert (p.walk.length-1)) ∧
    (Q d.radical a').relIndex (Q d.radical (p.walk.getVert (p.walk.length-2))) = 4 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let c := p.walk.getVert (p.walk.length-2)
  let t := p.walk.getVert (p.walk.length-1)
  let K := Z d.radical a' ⊓ Q d.radical a
  let A := Q d.radical a'
  let B := A ⊔ Z d.radical a
  let E := A ⊔ Q d.radical c
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hct : Adjacent d.radical c t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have het : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical het
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have hZa : Z d.radical a ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    change p.walk.length-2 < replacementDistance h d
    omega
  have hAt : A ≤ Q d.radical t := Q_le_adjacent_h d.radical ht het
  have hctQ : Q d.radical c ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hct
  have hEt : E ≤ Q d.radical t := sup_le hAt hctQ
  have hBE : B ≤ E := sup_le_sup_left hZa A
  have hneB : ¬ E ≤ B := by
    intro he
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    apply (le_sup_right.trans he).trans
    apply sup_le
    · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color))).trans (centralizer_le inf_le_left)
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)).trans (centralizer_le inf_le_right)
  have hAG : Z d.radical a ≤ stabilizer d.radical a' :=
    (hZa.trans hctQ).trans (fun _ hx => hx.2 _ (adjacent_symm d.radical het))
  have hAB : A.relIndex B = 2 := by
    let J := A ⊔ Z d.radical a
    let : (A.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
      (sup_le A.le_normalizer (hAG.trans (Q_normalized d.radical a')))
    have hh := relIndex_sup_left ((Z d.radical a).subgroupOf J) (A.subgroupOf J)
    rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
      relIndex_subgroupOf le_sup_right] at hh
    exact hh.trans (small_critical_indices s hc p hp).1
  have hAtIndex : A.relIndex (Q d.radical t) = 4 := by
    rw [edge_kernel_index s a' t p.end_color het,
      SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him,
      card_map_of_injective (MulAut.conj u).injective,card_plus]
  let := finite_stabilizer d.radical t
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion (show Q d.radical t ≤ stabilizer d.radical t from fun _ hx => hx.1))
      (inclusion_injective _)
  let : Finite E := Finite.of_injective (inclusion hEt) (inclusion_injective _)
  have hBEpos : 0 < B.relIndex E := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hBEne : B.relIndex E ≠ 1 := fun he => hneB (relIndex_eq_one.mp he)
  have hprod := relIndex_mul_relIndex A B E le_sup_left hBE
  rw [hAB] at hprod
  have hfour : 4 ≤ A.relIndex E := by omega
  have hprod' := relIndex_mul_relIndex A E (Q d.radical t) le_sup_left hEt
  rw [hAtIndex] at hprod'
  have hEtpos : 0 < E.relIndex (Q d.radical t) := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hi : E.relIndex (Q d.radical t) = 1 := by nlinarith
  have heq : E = Q d.radical t := le_antisymm hEt (relIndex_eq_one.mp hi)
  refine ⟨heq,?_⟩
  let J := A ⊔ Q d.radical c
  let : (A.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le A.le_normalizer ((hctQ.trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical het))).trans (Q_normalized d.radical a')))
  have hh := relIndex_sup_left ((Q d.radical c).subgroupOf J) (A.subgroupOf J)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at hh
  exact hh.symm.trans (by change A.relIndex E = 4; rw [heq]; exact hAtIndex)

/-- A nonzero full reverse-kernel commutator with the predecessor core
cannot be absorbed into the endpoint center. This includes the order-32
cover and every distance greater than two. -/
theorem kernel_predecessor_noncentral
    (s : FullSymmetricAction h e hz hn d)
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hne : ⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical (p.walk.getVert (p.walk.length-2))⁆ ≠ ⊥) :
    ¬ ⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) := by
  intro hcentral
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  let c := p.walk.getVert (p.walk.length-2)
  have hcol : color d.radical c = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    omega
  have hdist : (cosetGraph d.radical).dist c a' = 2 := by rw [p.dist_end]; omega
  have hQG : Q d.radical c ≤ stabilizer d.radical a' :=
    Q_le_stabilizer_of_dist_two d.radical c a' hcol hdist
  have hZaQ : Z d.radical a ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (by omega)]
    change p.walk.length-2 < replacementDistance h d
    omega
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a' p.end_color
  let A := (Z d.radical a).comap i
  let B := (Q d.radical c).comap i
  have hmA : A.map i = Z d.radical a :=
    map_comap_eq_self ((hZaQ.trans hQG).trans_eq hir.symm)
  have hmB : B.map i = Q d.radical c := map_comap_eq_self (hQG.trans_eq hir.symm)
  have hAB : A ≤ B := comap_mono hZaQ
  have hnA : ¬ A ≤ pCore 2 d.overgroup := by
    intro hh
    have he := map_mono (f := i) hh
    rw [hmA,hiQ] at he
    exact p.critical.2 he
  have hfix : U d.radical a' ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical a' ⊓ Q d.radical a := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←C_eq_Q s hc a p.start_color]
      exact ⟨critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
        (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
            exact replacementDistance_pos h d) p.critical
          (DistanceEight.U_le_Z d.radical a' hx.1),hx.2⟩
    · exact inf_le_inf_left _ (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a p.start_color)))
  have hmF : (replacementMoved d ⊓ centralizer (A : Set d.overgroup)).map i =
      U d.radical a' ⊓ Q d.radical a := by
    rw [←map_inf_centralizer_of_injective i hi,hiU,hmA,hfix]
  have hcF : ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),B⁆ ≤ center d.overgroup := by
    intro x hx
    apply mem_center_iff.mpr
    intro m
    apply hi
    simp only [map_mul]
    apply hcentral
    · have hh := mem_map_of_mem i hx
      rw [map_commutator,hmF,hmB] at hh
      exact commutator_mono (inf_le_inf_right _ (DistanceEight.U_le_Z d.radical a')) le_rfl hh
    · rw [←hir]
      exact ⟨m,rfl⟩
  let := finite_Z d.radical a'
  let : Finite (U d.radical a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a')) (inclusion_injective _)
  have hidx : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,hmF,hiU,
      inf_relIndex_left]
    exact (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a')
      index_ne_zero_of_finite).trans_eq (small_critical_indices s hc p hsmall).2
  have hz := congrArg (Subgroup.map i) (cover_fixed_central_commutator_eq_bot s A B hAB hnA hidx hcF)
  rw [map_commutator,hmF,hmB,Subgroup.map_bot] at hz
  have hm := (critical_kernel_predecessor_moving s hc hb p).2.2 (Q d.radical c)
    le_rfl
  exact hne (hm.trans hz)


/-- The nonzero alternative gives one full line in both edge seeds and in
both starting and predecessor seeds. Its relative-normalizer fixedness does
not imply centrality in the backward stabilizer: that centrality is false. -/
theorem mixed_backward_kernel_line_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hp : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≠ ⊥) :
    let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
    let D := ⁅K,Q d.radical (p.walk.getVert (p.walk.length-2))⁆
    Nat.card D = 2 ∧ D = ⁅K,Z d.radical c⁆ ∧
      D ≤ Z d.radical t ⊓ Z d.radical (p.walk.getVert (p.walk.length-1)) ∧
      D ≤ Z d.radical (alpha d.radical) ⊓ Z d.radical (p.walk.getVert (p.walk.length-2)) ∧
      D ≤ Z d.radical c ⊓ Z d.radical a' ∧
      D ≤ centralizer (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical c : Set (FreeAmalgam d.radical)) ∧
      (¬ D ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))) ∧
      ¬ D ≤ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono (plus_le_exceptional.trans
      CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.symm.le)
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let D := ⁅K,Q d.radical (p.walk.getVert (p.walk.length-2))⁆
  let H := ⁅K,Z d.radical c⁆
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hKt : K ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)
  have hKG : K ≤ stabilizer d.radical c :=
    hKt.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hHZ : H ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_right.mp (hKG.trans (Z_normalized d.radical c))
  have hpreG : Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ stabilizer d.radical a' := by
    apply Q_le_stabilizer_of_dist_two d.radical _ _
    · apply (p.vertex_color (Nat.sub_le _ _)).mpr
      have he := replacementDistance_even h d
      rw [Nat.even_iff] at he ⊢
      omega
    · rw [p.dist_end]
      omega
  have hDe : D ≤ Z d.radical a' :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hpreG.trans (Z_normalized d.radical a')))
  let := finite_Z d.radical a'
  let : Finite D := Finite.of_injective (inclusion hDe) (inclusion_injective _)
  have hHD : H ≤ D := commutator_mono le_rfl hbad
  let : Finite H := Finite.of_injective (inclusion hHD) (inclusion_injective _)
  have hbound : Nat.card D ≤ 2 := small_critical_kernel_predecessor_card s hc hb u hR p hp
  have hlo : 1 < Nat.card H := (one_lt_card_iff_ne_bot H).mpr hne
  have hupper := (card_le_of_le hHD).trans hbound
  have hcard : Nat.card H = 2 := by omega
  have heq : D = H := (eq_of_le_of_card_ge hHD (by rw [hcard]; exact hbound)).symm
  have hline := mixed_small_edge_commutator_fixed_knownSimple hb u him hcol hct K hKt hcard
  have hlast : D ≤ Z d.radical (p.walk.getVert (p.walk.length-1)) :=
    small_critical_predecessor_commutator_le_last_seed s hc hb u hR p hp
  have hpcol : color d.radical (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    omega
  have hpedge : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hDt := heq.le.trans hline.1
  refine ⟨by change Nat.card D = 2; rw [heq]; exact hcard,heq,le_inf hDt hlast,
    le_inf (hDt.trans (adjacent_Z_le d.radical rfl hat))
      (hlast.trans (adjacent_Z_le d.radical hpcol hpedge)),
    le_inf (heq.le.trans hHZ) hDe,heq.le.trans hline.2,?_,?_⟩
  · intro hcentral
    exact kernel_line_not_central s hc hat hct hne (heq.ge.trans hcentral)
  · exact kernel_predecessor_noncentral s hc hb p hp (by change D ≠ ⊥; rwa [heq])

/-- The actual mixed-plane backward selector yields a critical walk, or a
noncentral line with both edge placements and the full predecessor-core
image. All the hypotheses of the local estimates are supplied by the
original selected alternative. -/
theorem mixed_backward_or_full_core_line_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hp : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical) ∧
      ∃ c, Adjacent d.radical c t ∧
        ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) ∧
        ((∃ q : CriticalPath d.radical (replacementGeometry h d) c
            (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∨
        (let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
         let D := ⁅K,Q d.radical (p.walk.getVert (p.walk.length-2))⁆
         Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) ∧
         Nat.card D = 2 ∧ D = ⁅K,Z d.radical c⁆ ∧
         D ≤ Z d.radical t ⊓ Z d.radical (p.walk.getVert (p.walk.length-1)) ∧
         D ≤ Z d.radical (alpha d.radical) ⊓ Z d.radical (p.walk.getVert (p.walk.length-2)) ∧
         D ≤ Z d.radical c ⊓ Z d.radical a' ∧
         D ≤ centralizer (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
           stabilizer d.radical c : Set (FreeAmalgam d.radical)) ∧
         (¬ D ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))) ∧
         (¬ D ≤ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical))) ∧
         Q d.radical a' ⊔ Q d.radical (p.walk.getVert (p.walk.length-2)) =
           Q d.radical (p.walk.getVert (p.walk.length-1)) ∧
         (Q d.radical a').relIndex (Q d.radical (p.walk.getVert (p.walk.length-2))) = 4)) := by
  obtain ⟨t,hat,hgen,c,hct,hel,hout⟩ :=
    MixedSmallRadius.mixed_small_backward_or_kernel_knownSimple hb u him p hp
  refine ⟨t,hat,hgen,c,hct,hel,?_⟩
  rcases hout with hwalk | ⟨hbad,hcard,heq,_⟩
  · exact Or.inl hwalk
  · right
    have hne : ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≠ ⊥ := by
      intro hh
      rw [hh,Subgroup.card_bot] at hcard
      omega
    have hDne : ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),
        Q d.radical (p.walk.getVert (p.walk.length-2))⁆ ≠ ⊥ := by
      rwa [←heq]
    obtain ⟨hcD,hDc,hDe,hDz,hDE,hfix,hnon,hnonend⟩ :=
      mixed_backward_kernel_line_knownSimple hb u him p hp hat hct hbad hne
    exact ⟨hbad,hcD,hDc,hDe,hDz,hDE,hfix,hnon,hnonend,
      mixed_nonzero_kernel_predecessor_fills_knownSimple hb u him p hp hDne⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedKernel
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
