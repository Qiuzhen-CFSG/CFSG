module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SmallBackward

/-!
# Fixed core commutators of full backward kernels

A subgroup of a Baumann slice is fixed modulo the local seed by the
residual. Since that seed centralizes the two-core, the residual normalizes
the subgroup's core commutator. If this commutator has order at most two,
it is fixed pointwise. Invariance under an incident edge kernel strengthens
this to centrality in the whole vertex stabilizer.

For a small critical pair, the last-edge calculation bounds the commutator
of the full reverse critical kernel with the second predecessor core by
two. This uses the fixed-seed bound on both central covers, retaining the
augmentation displacement line instead of identifying it with the critical
commutator. A predecessor Baumann slice therefore supplies the precise
fixed-core placement in MS93 (5.8).

At distance four the existing midpoint-orbit and slice-index hypotheses
identify both full critical kernels. They supply the needed slice placement
and small critical index, so their midpoint-core commutators are central
at the midpoint. The original midpoint transporter identifies those two
commutators, which lie in both end-edge seeds. The known-simple application
retains the literal quotient,
both full kernels, the chosen conjugator and all transported walk vertices.

Source: Meierfrankenfeld--Stellmacher (1993), (5.8), printed pp.919--920,
and the kernel comparison in (5.12), pp.925--927. The fixed-core argument
adapts SymplecticSetup.BackwardFixedLine to the original full central covers;
SmallBackward supplies its order bound and MidpointSlice its actual application.

The source choices of midpoint orbit and upper slice bound remain explicit.
Their discharge, exact-four radius exclusion, intermediate R4/R6 noncentrality,
both terminal contradictions, largeDistance_knownSimple and the unconditional
replacementDistance = 2 application remain with
qt-e-ms-small-a6-exhaustion-large-distance. Final whole-core reconstruction
remains with qt-e-ms-small-a6-reconstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

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

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include h in
/-- A commutator of order at most two from a Baumann slice is fixed by the
original residual. The slice itself need not be normal. -/
theorem small_slice_core_commutator_le_fixedCore
    (hb : 2 < replacementDistance h d) {c : Vertex d.radical}
    (hcol : color d.radical c = false)
    (A : Subgroup (FreeAmalgam d.radical))
    (hAB : A ≤ B d.radical c ((replacementGeometry h d).Z_normal _))
    (hcard : Nat.card (⁅A,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2) :
    ⁅A,Q d.radical c⁆ ≤ fixedCore d.radical c := by
  have hVQ := (replacementGeometry h d).V_le_Q hb c hcol
  have hVG := hVQ.trans (show Q d.radical c ≤ stabilizer d.radical c from fun _ hx => hx.1)
  have hAQ : A ≤ Q d.radical c := by
    intro a ha
    exact hVQ (((mem_B_iff d.radical c _ hVG a).mp (hAB ha)).1)
  have hNQ : ⁅A,Q d.radical c⁆ ≤ Q d.radical c :=
    le_normalizer_iff_commutator_le_right.mp (hAQ.trans (Q d.radical c).le_normalizer)
  have hLA : ⁅Ltilde d.radical c,A⁆ ≤ centralizer
      (Q d.radical c : Set (FreeAmalgam d.radical)) := by
    apply le_trans _ (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c hcol))
    apply commutator_le.mpr
    intro l hl a ha
    exact ((mem_B_iff d.radical c _ hVG a).mp (hAB ha)).2 l hl
  have hnorm := fixed_mod_seed_normalizes_commutator A (Q d.radical c) (Ltilde d.radical c)
    (hAQ.trans (Q d.radical c).le_normalizer)
    ((Ltilde_le_stabilizer c).trans (Q_normalized d.radical c)) hLA
  let := finite_stabilizer d.radical c
  let : Finite (⁅A,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hNQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  by_cases he : Nat.card (⁅A,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) = 2
  · exact le_inf hNQ (le_centralizer_iff.mp
      (hnorm.trans (normalizer_le_centralizer_of_card_two _ he)))
  · rw [eq_bot_of_card_le (⁅A,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) (by omega)]
    exact bot_le

include s in
/-- The last edge bounds the entire reverse critical kernel's commutator
with the second predecessor core, for either full central cover. -/
theorem small_critical_kernel_predecessor_card
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    Nat.card (⁅Z d.radical a' ⊓ Q d.radical a,
      Q d.radical (p.walk.getVert (p.walk.length-2))⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let t := p.walk.getVert (p.walk.length-1)
  have hat : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have hpred : Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical t := by
    apply Q_le_adjacent_h d.radical ht
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hZt : Z d.radical a ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-1 < replacementDistance h d
    omega
  have hfixed : Z d.radical a' ⊓ Q d.radical a =
      Z d.radical a' ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)))
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←C_eq_Q s hc a p.start_color]
      exact ⟨critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
        (by rw [(replacementGeometry h d).distance_constant a p.start_color]
            exact replacementDistance_pos h d) p.critical hx.1,hx.2⟩
  let := finite_Z d.radical a'
  let : Finite (U d.radical a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a')) (inclusion_injective _)
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a') ≤ 2 := by
    have hQC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a') index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have hcard := small_edge_fixed_card_at s hc u hR p.end_color hat
    (Z d.radical a) hZt p.critical.2 hindex
  rw [←hfixed] at hcard
  have hKt : Z d.radical a' ⊓ Q d.radical a ≤ Q d.radical t := by
    apply inf_le_left.trans
    apply (Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ p.end_color) ?_).trans
      (Q_le_adjacent_h d.radical ht hat)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ p.end_color]
    exact replacementDistance_pos h d
  let := finite_stabilizer d.radical t
  let : Finite (⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical t⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion ((Subgroup.commutator_le_sup _ _).trans
      ((sup_le hKt le_rfl).trans (fun _ hx => hx.1)))) (inclusion_injective _)
  exact (card_le_of_le (commutator_mono le_rfl hpred)).trans hcard

include s in
/-- A reverse critical kernel in the predecessor Baumann slice has its
whole core commutator fixed by the original predecessor residual. -/
theorem small_critical_kernel_predecessor_fixedCore
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hslice : Z d.radical a' ⊓ Q d.radical a ≤
      B d.radical (p.walk.getVert (p.walk.length-2)) ((replacementGeometry h d).Z_normal _)) :
    ⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      fixedCore d.radical (p.walk.getVert (p.walk.length-2)) := by
  have hcol : color d.radical (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  exact small_slice_core_commutator_le_fixedCore (h := h) hb hcol _ hslice
    (small_critical_kernel_predecessor_card s hc hb u hR p hsmall)

include h in
private theorem fixed_core_edge_generation {c t : Vertex d.radical}
    (hcol : color d.radical c = false) (hct : Adjacent d.radical c t) :
    Ltilde d.radical c ⊔ Q d.radical t = stabilizer d.radical c := by
  have hsup : replacementComponent d ⊔ d.radical = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨k,hk,r,hr,rfl⟩ := replacement_product h d g
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hbase : Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (beta d.radical) =
      stabilizer d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d,Q_beta,←Subgroup.map_sup,hsup]
    exact (MonoidHom.range_eq_map (embedM d.radical)).symm.trans (stabilizer_m_base d.radical).symm
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act] at he
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
  · rw [hg.1] at hcol
    cases hcol

include h in
/-- Edge invariance strengthens residual fixedness to centrality in the
whole vertex stabilizer, still without assuming the slice is vertex-normal. -/
theorem small_slice_edge_core_commutator_central
    (hb : 2 < replacementDistance h d) {c t : Vertex d.radical}
    (hcol : color d.radical c = false) (hct : Adjacent d.radical c t)
    (A : Subgroup (FreeAmalgam d.radical))
    (hAB : A ≤ B d.radical c ((replacementGeometry h d).Z_normal _))
    (hAn : Q d.radical t ≤ normalizer (A : Set (FreeAmalgam d.radical)))
    (hcard : Nat.card (⁅A,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2) :
    ⁅A,Q d.radical c⁆ ≤
      centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
  have hfixed := small_slice_core_commutator_le_fixedCore (h := h) hb hcol A hAB hcard
  have hQn : Q d.radical t ≤ normalizer (Q d.radical c : Set (FreeAmalgam d.radical)) :=
    (show Q d.radical t ≤ stabilizer d.radical c from
      fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Q_normalized d.radical c)
  have hHn : Q d.radical t ≤ normalizer
      ((⁅A,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅A,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)).map (MulAut.conj g).toMonoidHom = _
    rw [map_commutator]
    exact congrArg₂ (fun X Y : Subgroup (FreeAmalgam d.radical) => ⁅X,Y⁆)
      (mem_normalizer_iff_map_conj_eq.mp (hAn hg))
      (mem_normalizer_iff_map_conj_eq.mp (hQn hg))
  let := finite_stabilizer d.radical c
  let : Finite (⁅A,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion ((hfixed.trans inf_le_left).trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hHt : ⁅A,Q d.radical c⁆ ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    by_cases he : Nat.card (⁅A,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) = 2
    · exact le_centralizer_iff.mp (hHn.trans (normalizer_le_centralizer_of_card_two _ he))
    · rw [eq_bot_of_card_le (⁅A,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) (by omega)]
      exact bot_le
  apply le_centralizer_iff.mp
  rw [←fixed_core_edge_generation (h := h) hcol hct]
  exact sup_le (le_centralizer_iff.mp (hfixed.trans inf_le_right)) (le_centralizer_iff.mp hHt)

include s in
/-- At distance four the actual midpoint slice identifies the whole reverse
kernel and makes its core commutator central at the midpoint. It lies in the
last edge seed and has order at most two; both cover orders are retained. -/
theorem midpoint_kernel_core_commutator
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical g a = a')
    (hindex : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    let K := Z d.radical a' ⊓ Q d.radical a
    let H := ⁅K,Q d.radical (p.walk.getVert 2)⁆
    Nat.card H ≤ 2 ∧ H ≤ Z d.radical (p.walk.getVert 3) ∧
      H ≤ fixedCore d.radical (p.walk.getVert 2) ∧
      H ≤ centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 3
  let K := Z d.radical a' ⊓ Q d.radical a
  let H := ⁅K,Q d.radical c⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hb2 : 2 < replacementDistance h d := by omega
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent d.radical c t :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have het : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcol] at hh
    cases hx : color d.radical t <;> simp_all
  have hslice := midpoint_slice_eq_reverse_kernel s hc hb p g hg he hindex
  have hKslice : K = Z d.radical a' ⊓ B d.radical c ((replacementGeometry h d).Z_normal _) :=
    hslice.1.symm
  have hKB : K ≤ B d.radical c ((replacementGeometry h d).Z_normal _) :=
    hKslice ▸ inf_le_right
  have hAn : Q d.radical t ≤ normalizer (K : Set (FreeAmalgam d.radical)) := by
    rw [hKslice]
    exact (le_inf
      ((show Q d.radical t ≤ stabilizer d.radical a' from
        fun _ hx => hx.2 _ (adjacent_symm d.radical het)).trans (Z_normalized d.radical a'))
      ((show Q d.radical t ≤ stabilizer d.radical c from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans
        (Escape.Propagation.Rigidity.B_normalized hb2 c hcol))).trans inf_normalizer_le_normalizer_inf
  have hcard : Nat.card H ≤ 2 := by
    have hh := small_critical_kernel_predecessor_card s hc hb2 u hR p (by
      rw [hslice.2.2.1]; decide)
    simpa only [hl,Nat.reduceSub] using hh
  have hfixed : H ≤ fixedCore d.radical c :=
    small_slice_core_commutator_le_fixedCore (h := h) hb2 hcol K hKB hcard
  have hcentral : H ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) :=
    small_slice_edge_core_commutator_central (h := h) hb2 hcol hct K hKB hAn hcard
  have hHK : H ≤ K := le_normalizer_iff_commutator_le_left.mp
    ((Q_le_adjacent_h d.radical ht hct).trans hAn)
  have hHQt : H ≤ Q d.radical t := (hfixed.trans inf_le_left).trans
    (Q_le_adjacent_h d.radical ht hct)
  have hHt : H ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    hcentral.trans (centralizer_le (fun _ hx => hx.2 _ (adjacent_symm d.radical hct)))
  have hseed : H ≤ Z d.radical t := by
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a' p.end_color
    intro x hx
    rw [Z,if_neg (by simp [ht])]
    exact mem_omegaCenter_iff.mpr ⟨hHQt hx,
      elemPow_eq_one_of_isElementaryAbelian x (show x ∈ Z d.radical a' from (hHK hx).1),hHt hx⟩
  exact ⟨hcard,hseed,hfixed,hcentral⟩


include s in
/-- The two full critical kernels have the same midpoint-core commutator.
The equality follows from the original midpoint transporter, not an
independent choice of endpoint marking. -/
theorem midpoint_kernel_core_commutators_eq
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical g a = a')
    (hindex : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    ⁅Z d.radical a ⊓ Q d.radical a',Q d.radical (p.walk.getVert 2)⁆ =
      ⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical (p.walk.getVert 2)⁆ := by
  let c := p.walk.getVert 2
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hb2 : 2 < replacementDistance h d := by omega
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hB : (B d.radical c ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical c ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 c hcol ((stabilizer d.radical c).inv_mem hg))
  have hindexA : (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a) ≤ 2 := by
    have hi := hindex
    change (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical a') ≤ 2 at hi
    rw [←he,U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hi
    exact hi
  let q : CriticalPath d.radical (replacementGeometry h d) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc p⟩
  have hmid : q.walk.getVert 2 = c := by
    change p.walk.reverse.getVert 2 = c
    rw [SimpleGraph.Walk.getVert_reverse,hl]
  have hge : act d.radical g⁻¹ a' = a := by
    rw [←he,←act_mul,mul_inv_cancel,act_one]
  have hs := midpoint_slice_eq_reverse_kernel s hc hb p g hg he hindex
  have hr := midpoint_slice_eq_reverse_kernel s hc hb q g⁻¹
    (by rw [hmid]; exact (stabilizer d.radical c).inv_mem hg) hge
    (by rw [hmid]; exact hindexA)
  rw [hmid] at hr
  have hK : (Z d.radical a ⊓ Q d.radical a').map (MulAut.conj g⁻¹).toMonoidHom =
      Z d.radical a' ⊓ Q d.radical a := by
    rw [←hr.1,map_inf _ _ _ (MulAut.conj g⁻¹).injective,←Z_act,he,hB]
    exact hs.1
  have hQ : (Q d.radical c).map (MulAut.conj g⁻¹).toMonoidHom = Q d.radical c := by
    rw [←Q_act,show act d.radical g c = c from hg]
  have hcentral := (midpoint_kernel_core_commutator s hc hb u hR p g hg he hindex).2.2.2
  have hH : (⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)).map
      (MulAut.conj g⁻¹).toMonoidHom = ⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical c⁆ :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hcentral ((stabilizer d.radical c).inv_mem hg)))
  apply map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
  change (⁅Z d.radical a ⊓ Q d.radical a',Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)).map
    (MulAut.conj g⁻¹).toMonoidHom = _
  rw [map_commutator,hK,hQ,hH]

/-- The original replacement's midpoint slice supplies centrality and
transports the complete kernel commutator with the same chosen element.
All vertices of the critical walk are transported by that element. -/
theorem midpoint_kernel_core_commutator_transport_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map (SourceReduction.projection h e hz hn d) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical g a = a')
    (hindex : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2)
    (k : FreeAmalgam d.radical) (hk : k ∈ stabilizer d.radical (p.walk.getVert 2)) :
    let K := Z d.radical a' ⊓ Q d.radical a
    let H := ⁅K,Q d.radical (p.walk.getVert 2)⁆
    Nat.card H ≤ 2 ∧ H ≤ Z d.radical (p.walk.getVert 1) ⊓ Z d.radical (p.walk.getVert 3) ∧
      H ≤ fixedCore d.radical (p.walk.getVert 2) ∧
      (∀ x ∈ H, k⁻¹*x*k = x) ∧
      ⁅Z d.radical (act d.radical k a') ⊓ Q d.radical (act d.radical k a),
        Q d.radical (p.walk.getVert 2)⁆ = H ∧
      ⁅Z d.radical a ⊓ Q d.radical a',Q d.radical (p.walk.getVert 2)⁆ = H ∧
      (∀ i, (p.act k).walk.getVert i = act d.radical k (p.walk.getVert i)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hR' : d.radical.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨hcard,hseed,hfixed,hcentral⟩ := midpoint_kernel_core_commutator s hc hb u hR' p g hg he hindex
  have heq := midpoint_kernel_core_commutators_eq s hc hb u hR' p g hg he hindex
  let H := ⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical (p.walk.getVert 2)⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical (p.walk.getVert 1) = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases hx : color d.radical (p.walk.getVert 1) <;> simp_all
  have hQct := Q_le_adjacent_h d.radical ht hct
  have hHZa : H ≤ Z d.radical a := by
    dsimp only [H]
    rw [←heq]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((hQct.trans (show Q d.radical (p.walk.getVert 1) ≤ stabilizer d.radical a from
          fun _ hx => hx.2 _ (adjacent_symm d.radical hat))).trans (Z_normalized d.radical a)))
  have hfirst : H ≤ Z d.radical (p.walk.getVert 1) := by
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
    intro x hx
    rw [Z,if_neg (by simp [ht])]
    exact mem_omegaCenter_iff.mpr ⟨hQct ((hfixed hx).1),
      elemPow_eq_one_of_isElementaryAbelian x (hHZa hx),
      fun z hz => hcentral hx z (hz.2 _ (adjacent_symm d.radical hct))⟩
  dsimp only
  refine ⟨hcard,le_inf hfirst hseed,hfixed,?_,?_,heq,?_⟩
  · intro x hx
    calc
      k⁻¹*x*k = k⁻¹*(x*k) := mul_assoc _ _ _
      _ = k⁻¹*(k*x) := congrArg (k⁻¹ * ·) (hcentral hx k hk).symm
      _ = x := inv_mul_cancel_left _ _
  · have hfix : act d.radical k (p.walk.getVert 2) = p.walk.getVert 2 := hk
    have hQ : (Q d.radical (p.walk.getVert 2)).map (MulAut.conj k⁻¹).toMonoidHom =
        Q d.radical (p.walk.getVert 2) := by rw [←Q_act,hfix]
    have hH := mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hcentral ((stabilizer d.radical (p.walk.getVert 2)).inv_mem hk)))
    rw [map_commutator,map_inf _ _ _ (MulAut.conj k⁻¹).injective] at hH
    change ⁅(Z d.radical a').map (MulAut.conj k⁻¹).toMonoidHom ⊓
      (Q d.radical a).map (MulAut.conj k⁻¹).toMonoidHom,
      (Q d.radical (p.walk.getVert 2)).map (MulAut.conj k⁻¹).toMonoidHom⁆ = _ at hH
    rw [←Z_act,←Q_act,hQ] at hH
    exact hH
  · intro i
    simp only [CriticalPath.act,actWalk_getVert]

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
