module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicMidpointSlices

/-!
# Full backward-kernel commutators on the cubic graph

The fixed-seed displacement bound controls the full reverse critical
kernel at the second predecessor, including the central attachment in
the order-32 cover. A Baumann slice makes this commutator residual-fixed;
edge invariance makes it central in the whole predecessor stabilizer.
At distance four the original midpoint slice and transporter identify the
two kernel commutators, fixing them pointwise in both end-edge seeds.
The proof uses the literal critical seed-centralizer intersection, retaining
E/Q of order three rather than identifying the full centralizer with Q.

Source: Meierfrankenfeld--Stellmacher (1993), (5.8), pp.919--920,
and (5.12), pp.925--927. Adapts the independent natural branch's
SectionFive.BackwardFixedCore to the original cubic graph.
The source slice and radical-image choices, R4/R6 and terminal distance
exclusions remain with qt-e-ms-small-a6-reconstruction. Independent natural
exhaustion remains with qt-e-ms-small-a6-exhaustion-large-distance.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "Rg" => edge L R
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
/-- A commutator of order at most two from a Baumann slice is fixed by the
original residual. The slice itself need not be normal. -/
theorem small_slice_core_commutator_le_fixedCore
    (hb : 2 < sourceDistance h) {c : Vertex Rg}
    (hcol : color Rg c = false)
    (A : Subgroup (FreeAmalgam Rg))
    (hAB : A ≤ B Rg c ((sourceGeometry h).Z_normal _))
    (hcard : Nat.card (⁅A,Q Rg c⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2) :
    ⁅A,Q Rg c⁆ ≤ fixedCore Rg c := by
  have hVQ := (sourceGeometry h).V_le_Q hb c hcol
  have hVG := hVQ.trans (show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1)
  have hAQ : A ≤ Q Rg c := by
    intro a ha
    exact hVQ (((mem_B_iff Rg c _ hVG a).mp (hAB ha)).1)
  have hNQ : ⁅A,Q Rg c⁆ ≤ Q Rg c :=
    le_normalizer_iff_commutator_le_right.mp (hAQ.trans (Q Rg c).le_normalizer)
  have hLA : ⁅Ltilde Rg c,A⁆ ≤ centralizer
      (Q Rg c : Set (FreeAmalgam Rg)) := by
    apply le_trans _ (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hcol))
    apply commutator_le.mpr
    intro l hl a ha
    exact ((mem_B_iff Rg c _ hVG a).mp (hAB ha)).2 l hl
  have hnorm := fixed_mod_seed_normalizes_commutator A (Q Rg c) (Ltilde Rg c)
    (hAQ.trans (Q Rg c).le_normalizer)
    ((Ltilde_le_stabilizer c).trans (Q_normalized Rg c)) hLA
  let := finite_stabilizer Rg c
  let : Finite (⁅A,Q Rg c⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion (hNQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  by_cases he : Nat.card (⁅A,Q Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2
  · exact le_inf hNQ (le_centralizer_iff.mp
      (hnorm.trans (normalizer_le_centralizer_of_card_two _ he)))
  · rw [eq_bot_of_card_le (⁅A,Q Rg c⁆ : Subgroup (FreeAmalgam Rg)) (by omega)]
    exact bot_le

include h e hz hk in
/-- The last edge bounds the entire reverse critical kernel's commutator
with the second predecessor core, for either full central cover. -/
theorem small_critical_kernel_predecessor_card
    (hb : 2 < sourceDistance h)
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4) :
    Nat.card (⁅Z Rg a' ⊓ Q Rg a,
      Q Rg (p.walk.getVert (p.walk.length-2))⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let t := p.walk.getVert (p.walk.length-1)
  have hat : Adjacent Rg a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hpred : Q Rg (p.walk.getVert (p.walk.length-2)) ≤ Q Rg t := by
    apply Q_le_adjacent_h Rg ht
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hZt : Z Rg a ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-1 < sourceDistance h
    omega
  have hfixed : Z Rg a' ⊓ Q Rg a =
      Z Rg a' ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) := by
    let q := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
      (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h) a' p.end_color p.critical)
    exact (critical_seed_centralizer_intersection h e q).symm
  let := finite_Z Rg a'
  let : Finite (U Rg a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg a')) (inclusion_injective _)
  have hindex : (centralizer (Z Rg a : Set (FreeAmalgam Rg))).relIndex
      (U Rg a') ≤ 2 := by
    have hQC : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg a') index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p hsmall).2
  have hcard := small_edge_fixed_card_at h e hz hk u hR p.end_color hat
    (Z Rg a) hZt p.critical.2 hindex
  rw [←hfixed] at hcard
  have hKt : Z Rg a' ⊓ Q Rg a ≤ Q Rg t := by
    apply inf_le_left.trans
    apply (Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color) ?_).trans
      (Q_le_adjacent_h Rg ht hat)
    rw [SimpleGraph.dist_self,(sourceGeometry h).distance_constant _ p.end_color]
    exact sourceDistance_pos h
  let := finite_stabilizer Rg t
  let : Finite (⁅Z Rg a' ⊓ Q Rg a,Q Rg t⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion ((Subgroup.commutator_le_sup _ _).trans
      ((sup_le hKt le_rfl).trans (fun _ hx => hx.1)))) (inclusion_injective _)
  exact (card_le_of_le (commutator_mono le_rfl hpred)).trans hcard

include h e hz hk in
/-- A reverse critical kernel in the predecessor Baumann slice has its
whole core commutator fixed by the original predecessor residual. -/
theorem small_critical_kernel_predecessor_fixedCore
    (hb : 2 < sourceDistance h)
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4)
    (hslice : Z Rg a' ⊓ Q Rg a ≤
      B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _)) :
    ⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
      fixedCore Rg (p.walk.getVert (p.walk.length-2)) := by
  have hcol : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  exact small_slice_core_commutator_le_fixedCore (h := h) hb hcol _ hslice
    (small_critical_kernel_predecessor_card h e hz hk hb u hR p hsmall)

include h in
private theorem fixed_core_edge_generation {c t : Vertex Rg}
    (hcol : color Rg c = false) (hct : Adjacent Rg c t) :
    Ltilde Rg c ⊔ Q Rg t = stabilizer Rg c := by
  apply CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
  · rw [h.relative_residual]
    exact (codisjoint_subgroupOf_sup L R).eq_top
  · exact hcol
  · exact hct

include h in
/-- Edge invariance strengthens residual fixedness to centrality in the
whole vertex stabilizer, still without assuming the slice is vertex-normal. -/
theorem small_slice_edge_core_commutator_central
    (hb : 2 < sourceDistance h) {c t : Vertex Rg}
    (hcol : color Rg c = false) (hct : Adjacent Rg c t)
    (A : Subgroup (FreeAmalgam Rg))
    (hAB : A ≤ B Rg c ((sourceGeometry h).Z_normal _))
    (hAn : Q Rg t ≤ normalizer (A : Set (FreeAmalgam Rg)))
    (hcard : Nat.card (⁅A,Q Rg c⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2) :
    ⁅A,Q Rg c⁆ ≤
      centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
  have hfixed := small_slice_core_commutator_le_fixedCore (h := h) hb hcol A hAB hcard
  have hQn : Q Rg t ≤ normalizer (Q Rg c : Set (FreeAmalgam Rg)) :=
    (show Q Rg t ≤ stabilizer Rg c from
      fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Q_normalized Rg c)
  have hHn : Q Rg t ≤ normalizer
      ((⁅A,Q Rg c⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅A,Q Rg c⁆ : Subgroup (FreeAmalgam Rg)).map (MulAut.conj g).toMonoidHom = _
    rw [map_commutator]
    exact congrArg₂ (fun X Y : Subgroup (FreeAmalgam Rg) => ⁅X,Y⁆)
      (mem_normalizer_iff_map_conj_eq.mp (hAn hg))
      (mem_normalizer_iff_map_conj_eq.mp (hQn hg))
  let := finite_stabilizer Rg c
  let : Finite (⁅A,Q Rg c⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion ((hfixed.trans inf_le_left).trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hHt : ⁅A,Q Rg c⁆ ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    by_cases he : Nat.card (⁅A,Q Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2
    · exact le_centralizer_iff.mp (hHn.trans (normalizer_le_centralizer_of_card_two _ he))
    · rw [eq_bot_of_card_le (⁅A,Q Rg c⁆ : Subgroup (FreeAmalgam Rg)) (by omega)]
      exact bot_le
  apply le_centralizer_iff.mp
  rw [←fixed_core_edge_generation (h := h) hcol hct]
  exact sup_le (le_centralizer_iff.mp (hfixed.trans inf_le_right)) (le_centralizer_iff.mp hHt)

include h e hz hk in
/-- At distance four the actual midpoint slice identifies the whole reverse
kernel and makes its core commutator central at the midpoint. It lies in the
last edge seed and has order at most two; both cover orders are retained. -/
theorem midpoint_kernel_core_commutator
    (hb : sourceDistance h = 4)
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g a = a')
    (hindex : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a') ≤ 2) :
    let K := Z Rg a' ⊓ Q Rg a
    let H := ⁅K,Q Rg (p.walk.getVert 2)⁆
    Nat.card H ≤ 2 ∧ H ≤ Z Rg (p.walk.getVert 3) ∧
      H ≤ fixedCore Rg (p.walk.getVert 2) ∧
      H ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 3
  let K := Z Rg a' ⊓ Q Rg a
  let H := ⁅K,Q Rg c⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hb2 : 2 < sourceDistance h := by omega
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent Rg c t :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have het : Adjacent Rg a' t := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hcol] at hh
    cases hx : color Rg t <;> simp_all
  have hslice := midpoint_slice_eq_reverse_kernel h e hz hk hb p g hg he hindex
  have hKslice : K = Z Rg a' ⊓ B Rg c ((sourceGeometry h).Z_normal _) :=
    hslice.1.symm
  have hKB : K ≤ B Rg c ((sourceGeometry h).Z_normal _) :=
    hKslice ▸ inf_le_right
  have hAn : Q Rg t ≤ normalizer (K : Set (FreeAmalgam Rg)) := by
    rw [hKslice]
    exact (le_inf
      ((show Q Rg t ≤ stabilizer Rg a' from
        fun _ hx => hx.2 _ (adjacent_symm Rg het)).trans (Z_normalized Rg a'))
      ((show Q Rg t ≤ stabilizer Rg c from
        fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans
        (Escape.Propagation.Rigidity.B_normalized hb2 c hcol))).trans inf_normalizer_le_normalizer_inf
  have hcard : Nat.card H ≤ 2 := by
    have hh := small_critical_kernel_predecessor_card h e hz hk hb2 u hR p (by
      rw [hslice.2.2.1]; decide)
    simpa only [hl,Nat.reduceSub] using hh
  have hfixed : H ≤ fixedCore Rg c :=
    small_slice_core_commutator_le_fixedCore (h := h) hb2 hcol K hKB hcard
  have hcentral : H ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) :=
    small_slice_edge_core_commutator_central (h := h) hb2 hcol hct K hKB hAn hcard
  have hHK : H ≤ K := le_normalizer_iff_commutator_le_left.mp
    ((Q_le_adjacent_h Rg ht hct).trans hAn)
  have hHQt : H ≤ Q Rg t := (hfixed.trans inf_le_left).trans
    (Q_le_adjacent_h Rg ht hct)
  have hHt : H ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) :=
    hcentral.trans (centralizer_le (fun _ hx => hx.2 _ (adjacent_symm Rg hct)))
  have hseed : H ≤ Z Rg t := by
    let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color
    intro x hx
    rw [Z,if_neg (by simp [ht])]
    exact mem_omegaCenter_iff.mpr ⟨hHQt hx,
      elemPow_eq_one_of_isElementaryAbelian x (show x ∈ Z Rg a' from (hHK hx).1),hHt hx⟩
  exact ⟨hcard,hseed,hfixed,hcentral⟩


include h e hz hk in
/-- The two full critical kernels have the same midpoint-core commutator.
The equality follows from the original midpoint transporter, not an
independent choice of endpoint marking. -/
theorem midpoint_kernel_core_commutators_eq
    (hb : sourceDistance h = 4)
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g a = a')
    (hindex : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a') ≤ 2) :
    ⁅Z Rg a ⊓ Q Rg a',Q Rg (p.walk.getVert 2)⁆ =
      ⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert 2)⁆ := by
  let c := p.walk.getVert 2
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hb2 : 2 < sourceDistance h := by omega
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hB : (B Rg c ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg c ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 c hcol ((stabilizer Rg c).inv_mem hg))
  have hindexA : (B Rg c ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a) ≤ 2 := by
    have hi := hindex
    change (B Rg c ((sourceGeometry h).Z_normal _)).relIndex (U Rg a') ≤ 2 at hi
    rw [←he,U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hi
    exact hi
  let q : CriticalPath Rg (sourceGeometry h) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h) a' p.end_color p.critical⟩
  have hmid : q.walk.getVert 2 = c := by
    change p.walk.reverse.getVert 2 = c
    rw [SimpleGraph.Walk.getVert_reverse,hl]
  have hge : act Rg g⁻¹ a' = a := by
    rw [←he,←act_mul,mul_inv_cancel,act_one]
  have hs := midpoint_slice_eq_reverse_kernel h e hz hk hb p g hg he hindex
  have hr := midpoint_slice_eq_reverse_kernel h e hz hk hb q g⁻¹
    (by rw [hmid]; exact (stabilizer Rg c).inv_mem hg) hge
    (by rw [hmid]; exact hindexA)
  rw [hmid] at hr
  have hK : (Z Rg a ⊓ Q Rg a').map (MulAut.conj g⁻¹).toMonoidHom =
      Z Rg a' ⊓ Q Rg a := by
    rw [←hr.1,map_inf _ _ _ (MulAut.conj g⁻¹).injective,←Z_act,he,hB]
    exact hs.1
  have hQ : (Q Rg c).map (MulAut.conj g⁻¹).toMonoidHom = Q Rg c := by
    rw [←Q_act,show act Rg g c = c from hg]
  have hcentral := (midpoint_kernel_core_commutator h e hz hk hb u hR p g hg he hindex).2.2.2
  have hH : (⁅Z Rg a' ⊓ Q Rg a,Q Rg c⁆ : Subgroup (FreeAmalgam Rg)).map
      (MulAut.conj g⁻¹).toMonoidHom = ⁅Z Rg a' ⊓ Q Rg a,Q Rg c⁆ :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hcentral ((stabilizer Rg c).inv_mem hg)))
  apply map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
  change (⁅Z Rg a ⊓ Q Rg a',Q Rg c⁆ : Subgroup (FreeAmalgam Rg)).map
    (MulAut.conj g⁻¹).toMonoidHom = _
  rw [map_commutator,hK,hQ,hH]

include h e hz hk in
/-- The original cubic graph's midpoint slice supplies centrality and
transports the complete kernel commutator with the same chosen element.
All vertices of the critical walk are transported by that element. -/
theorem midpoint_kernel_core_commutator_transport
    (hb : sourceDistance h = 4)
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g a = a')
    (hindex : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a') ≤ 2)
    (k : FreeAmalgam Rg) (hkm : k ∈ stabilizer Rg (p.walk.getVert 2)) :
    let K := Z Rg a' ⊓ Q Rg a
    let H := ⁅K,Q Rg (p.walk.getVert 2)⁆
    Nat.card H ≤ 2 ∧ H ≤ Z Rg (p.walk.getVert 1) ⊓ Z Rg (p.walk.getVert 3) ∧
      H ≤ fixedCore Rg (p.walk.getVert 2) ∧
      (∀ x ∈ H, k⁻¹*x*k = x) ∧
      ⁅Z Rg (act Rg k a') ⊓ Q Rg (act Rg k a),
        Q Rg (p.walk.getVert 2)⁆ = H ∧
      ⁅Z Rg a ⊓ Q Rg a',Q Rg (p.walk.getVert 2)⁆ = H ∧
      (∀ i, (p.act k).walk.getVert i = act Rg k (p.walk.getVert i)) := by
  have hb2 : 2 < sourceDistance h := by omega
  obtain ⟨hcard,hseed,hfixed,hcentral⟩ := midpoint_kernel_core_commutator h e hz hk hb u hR p g hg he hindex
  have heq := midpoint_kernel_core_commutators_eq h e hz hk hb u hR p g hg he hindex
  let H := ⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert 2)⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg (p.walk.getVert 1) = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.start_color] at hh
    cases hx : color Rg (p.walk.getVert 1) <;> simp_all
  have hQct := Q_le_adjacent_h Rg ht hct
  have hHZa : H ≤ Z Rg a := by
    dsimp only [H]
    rw [←heq]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((hQct.trans (show Q Rg (p.walk.getVert 1) ≤ stabilizer Rg a from
          fun _ hx => hx.2 _ (adjacent_symm Rg hat))).trans (Z_normalized Rg a)))
  have hfirst : H ≤ Z Rg (p.walk.getVert 1) := by
    let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
    intro x hx
    rw [Z,if_neg (by simp [ht])]
    exact mem_omegaCenter_iff.mpr ⟨hQct ((hfixed hx).1),
      elemPow_eq_one_of_isElementaryAbelian x (hHZa hx),
      fun z hz => hcentral hx z (hz.2 _ (adjacent_symm Rg hct))⟩
  dsimp only
  refine ⟨hcard,le_inf hfirst hseed,hfixed,?_,?_,heq,?_⟩
  · intro x hx
    calc
      k⁻¹*x*k = k⁻¹*(x*k) := mul_assoc _ _ _
      _ = k⁻¹*(k*x) := congrArg (k⁻¹ * ·) (hcentral hx k hkm).symm
      _ = x := inv_mul_cancel_left _ _
  · have hfix : act Rg k (p.walk.getVert 2) = p.walk.getVert 2 := hkm
    have hQ : (Q Rg (p.walk.getVert 2)).map (MulAut.conj k⁻¹).toMonoidHom =
        Q Rg (p.walk.getVert 2) := by rw [←Q_act,hfix]
    have hH := mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hcentral ((stabilizer Rg (p.walk.getVert 2)).inv_mem hkm)))
    rw [map_commutator,map_inf _ _ _ (MulAut.conj k⁻¹).injective] at hH
    change ⁅(Z Rg a').map (MulAut.conj k⁻¹).toMonoidHom ⊓
      (Q Rg a).map (MulAut.conj k⁻¹).toMonoidHom,
      (Q Rg (p.walk.getVert 2)).map (MulAut.conj k⁻¹).toMonoidHom⁆ = _ at hH
    rw [←Z_act,←Q_act,hQ] at hH
    exact hH
  · intro i
    simp only [CriticalPath.act,actWalk_getVert]

omit hk in
include h e hz in
private theorem vertex_seed_eq_moving_sup_edge {c b : Vertex Rg}
    (hc : color Rg c = false) (hcb : Adjacent Rg c b) :
    Z Rg c = U Rg c ⊔ Z Rg b := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common Rg c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    have hb := CubicAction.graph_Z_eq_moved_sup_edge h e hz (base_adjacent Rg)
    rw [graph_U_map h e hz] at hb
    have he := congrArg (fun A : Subgroup (FreeAmalgam Rg) =>
      A.map (MulAut.conj g⁻¹).toMonoidHom) hb
    rw [Subgroup.map_sup,←Z_act,←U_act,←Z_act] at he
    simpa [alpha,beta] using he
  · rw [hg.1] at hc
    cases hc

omit hk in
include h e hz in
private theorem full_fixed_seed_edge_commutator
    {c t : Vertex Rg} (hcol : color Rg c = false)
    (hct : Adjacent Rg c t)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t)
    (D : Subgroup (FreeAmalgam Rg)) (hD : D ≤ Q Rg t) :
    ⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),D⁆ =
      ⁅U Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),D⁆ := by
  let F := U Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hcol] at hh
    cases he : color Rg t <;> simp_all
  have hseed : Z Rg t ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedA := hseed.trans (centralizer_le hA)
  have hseedN : Z Rg t ≤ normalizer (U Rg c : Set (FreeAmalgam Rg)) :=
    ((adjacent_Z_le Rg hcol hct).trans (Z_le_stabilizer Rg c)).trans (U_normalized c)
  have heq : Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)) = F ⊔ Z Rg t := by
    rw [vertex_seed_eq_moving_sup_edge h e hz hcol hct,
      sup_comm (U Rg c),inf_centralizer_sup_of_centralizing _ _ _ hseedN hseedA]
    exact sup_comm _ _
  rw [heq]
  apply le_antisymm _ (commutator_mono le_sup_left le_rfl)
  apply commutator_le.mpr
  intro x hx r hr
  have hn : Z Rg t ≤ normalizer (F : Set (FreeAmalgam Rg)) :=
    (le_inf hseedN (hseedA.trans (centralizer (A : Set (FreeAmalgam Rg))).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hp : x ∈ (F : Set (FreeAmalgam Rg)) * (Z Rg t : Set (FreeAmalgam Rg)) := by
    rw [←coe_mul_of_right_le_normalizer_left F (Z Rg t) hn]
    exact hx
  obtain ⟨w,hw,z,hz,rfl⟩ := hp
  have hzero : ⁅z,r⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hseed hz r (hD hr)).symm
  rw [commutatorElement_mul_left_eq_conj_mul,hzero,mul_one,mul_inv_cancel,one_mul]
  exact commutator_mem_commutator hw hr

omit hk in
include h e hz in
/-- The full reverse kernel is the source moving kernel times the last edge
seed. That seed lies in the predecessor slice and centralizes its core, so
slice placement and every predecessor-core commutator agree for both kernels. -/
theorem critical_kernel_predecessor_moving
    (hb : 2 < sourceDistance h)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a') :
    Z Rg a' ⊓ Q Rg a =
        (U Rg a' ⊓ Q Rg a) ⊔ Z Rg (p.walk.getVert (p.walk.length-1)) ∧
      (Z Rg a' ⊓ Q Rg a ≤
          B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _) ↔
        U Rg a' ⊓ Q Rg a ≤
          B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _)) ∧
      ∀ D : Subgroup (FreeAmalgam Rg),
        D ≤ Q Rg (p.walk.getVert (p.walk.length-2)) →
        ⁅Z Rg a' ⊓ Q Rg a,D⁆ = ⁅U Rg a' ⊓ Q Rg a,D⁆ := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let c := p.walk.getVert (p.walk.length-2)
  let t := p.walk.getVert (p.walk.length-1)
  have hat : Adjacent Rg a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hct : Adjacent Rg c t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hcol : color Rg c = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hZt : Z Rg a ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-1 < sourceDistance h
    omega
  have hfix (T : Subgroup (FreeAmalgam Rg)) (hT : T ≤ Z Rg a') :
      T ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) = T ⊓ Q Rg a := by
    let q := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
      (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
        a' p.end_color p.critical)
    calc
      _ = T ⊓ (Z Rg a' ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg))) := by
        rw [←inf_assoc,inf_eq_left.mpr hT]
      _ = T ⊓ (Z Rg a' ⊓ Q Rg a) := by rw [critical_seed_centralizer_intersection h e q]
      _ = T ⊓ Q Rg a := by rw [←inf_assoc,inf_eq_left.mpr hT]
  have hseed : Z Rg t ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedN : Z Rg t ≤ normalizer (U Rg a' : Set (FreeAmalgam Rg)) :=
    ((adjacent_Z_le Rg p.end_color hat).trans (Z_le_stabilizer Rg a')).trans (U_normalized a')
  have heq : Z Rg a' ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) =
      (U Rg a' ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg))) ⊔ Z Rg t := by
    rw [vertex_seed_eq_moving_sup_edge h e hz p.end_color hat,
      sup_comm (U Rg a'),inf_centralizer_sup_of_centralizing _ _ _ hseedN
        (hseed.trans (centralizer_le hZt))]
    exact sup_comm _ _
  rw [hfix _ le_rfl,hfix _ (DistanceEight.U_le_Z Rg a')] at heq
  refine ⟨heq,?_,?_⟩
  · rw [heq]
    have hseedB := (adjacent_Z_le Rg hcol hct).trans (Escape.EdgeTransfer.Z_le_B hb c hcol)
    exact ⟨fun hh => le_sup_left.trans hh,fun hh => sup_le hh hseedB⟩
  · intro D hD
    have hh := full_fixed_seed_edge_commutator (h := h) (e := e) (hz := hz)
      p.end_color hat (Z Rg a) hZt D (hD.trans (Q_le_adjacent_h Rg ht hct))
    rwa [hfix _ le_rfl,hfix _ (DistanceEight.U_le_Z Rg a')] at hh

include h in

/-- The same residual element preserves the slice commutator while
transporting its core actor. No invariance of the slice itself is assumed. -/
theorem small_slice_commutator_residual_transport
    (hb : 2 < sourceDistance h) {c : Vertex Rg}
    (hcol : color Rg c = false)
    (A : Subgroup (FreeAmalgam Rg))
    (hAB : A ≤ B Rg c ((sourceGeometry h).Z_normal _))
    (hcard : Nat.card (⁅A,Q Rg c⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2)
    (D : Subgroup (FreeAmalgam Rg)) (hD : D ≤ Q Rg c)
    (k : FreeAmalgam Rg) (hkm : k ∈ Ltilde Rg c) :
    ⁅A,D.map (MulAut.conj k).toMonoidHom⁆ = ⁅A,D⁆ := by
  have hfixed := small_slice_core_commutator_le_fixedCore (h := h) hb hcol A hAB hcard
  have hVQ := (sourceGeometry h).V_le_Q hb c hcol
  have hVG := hVQ.trans (show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1)
  have hAQ : A ≤ Q Rg c := by
    intro a ha
    exact hVQ (((mem_B_iff Rg c _ hVG a).mp (hAB ha)).1)
  have hZQ : Z Rg c ≤ centralizer (Q Rg c : Set (FreeAmalgam Rg)) :=
    commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hcol)
  have he (a : FreeAmalgam Rg) (ha : a ∈ A)
      (x : FreeAmalgam Rg) (hx : x ∈ Q Rg c) :
      ⁅a,k*x*k⁻¹⁆ = ⁅a,x⁆ := by
    have hx' : k*x*k⁻¹ ∈ Q Rg c :=
      (mem_normalizer_iff.mp ((Q_normalized Rg c) (Ltilde_le_stabilizer _ hkm)) x).mp hx
    have hka : ⁅k,a⁆ ∈ Z Rg c :=
      ((mem_B_iff Rg c _ hVG a).mp (hAB ha)).2 k hkm
    have hax' : ⁅a,k*x*k⁻¹⁆ ∈ Q Rg c :=
      (Subgroup.commutator_le_sup _ _).trans (sup_le hAQ le_rfl)
        (commutator_mem_commutator ha hx')
    have hzero : ⁅⁅k,a⁆,k*x*k⁻¹⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hZQ hka _ hx').symm
    have hfix : k*⁅a,x⁆*k⁻¹ = ⁅a,x⁆ := by
      have hh := (hfixed (commutator_mem_commutator ha hx)).2 k hkm
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

omit hk in
include h e hz in
/-- Whole-core application of full reverse-kernel control and the literal
midpoint transport. The point-core and slice hypotheses remain only in the
branches that use them; neither the cubic kernel nor a full cover is removed. -/
theorem coreExhaustion_or_cubic_backward_kernels :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) ≤ pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
          (Q Rg a').relIndex (Z Rg a) < 4 →
          Nat.card (⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆ :
            Subgroup (FreeAmalgam Rg)) ≤ 2 ∧
          (Z Rg a' ⊓ Q Rg a ≤
              B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _) →
            ⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
              fixedCore Rg (p.walk.getVert (p.walk.length-2)))) ∧
      (∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) ≤ pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
          sourceDistance h = 4 →
          ∀ g ∈ stabilizer Rg (p.walk.getVert 2), act Rg g a = a' →
            (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a') ≤ 2 →
            ∀ k ∈ stabilizer Rg (p.walk.getVert 2),
              let H := ⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert 2)⁆
              Nat.card H ≤ 2 ∧ H ≤ Z Rg (p.walk.getVert 1) ⊓ Z Rg (p.walk.getVert 3) ∧
                H ≤ fixedCore Rg (p.walk.getVert 2) ∧
                (∀ x ∈ H, k⁻¹*x*k = x) ∧
                ⁅Z Rg (act Rg k a') ⊓ Q Rg (act Rg k a),Q Rg (p.walk.getVert 2)⁆ = H ∧
                ⁅Z Rg a ⊓ Q Rg a',Q Rg (p.walk.getVert 2)⁆ = H ∧
                (∀ i, (p.act k).walk.getVert i = act Rg k (p.walk.getVert i))) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,?_,?_⟩
    · intro u hR a a' p hsmall
      exact ⟨small_critical_kernel_predecessor_card h e hz hk hb u hR p hsmall,
        small_critical_kernel_predecessor_fixedCore h e hz hk hb u hR p hsmall⟩
    · intro u hR a a' p hb4 g hg he hi k hkm
      exact midpoint_kernel_core_commutator_transport h e hz hk hb4 u hR p g hg he hi k hkm

omit hk in
include h e hz in
/-- Literal C.1.32 application of the same full-kernel and midpoint bounds. -/
theorem rankTwo_or_cubic_backward_kernels :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      (∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) ≤ pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
          (Q Rg a').relIndex (Z Rg a) < 4 →
          Nat.card (⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆ :
            Subgroup (FreeAmalgam Rg)) ≤ 2 ∧
          (Z Rg a' ⊓ Q Rg a ≤
              B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _) →
            ⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
              fixedCore Rg (p.walk.getVert (p.walk.length-2)))) ∧
      (∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) ≤ pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
          sourceDistance h = 4 →
          ∀ g ∈ stabilizer Rg (p.walk.getVert 2), act Rg g a = a' →
            (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a') ≤ 2 →
            ∀ k ∈ stabilizer Rg (p.walk.getVert 2),
              let H := ⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert 2)⁆
              Nat.card H ≤ 2 ∧ H ≤ Z Rg (p.walk.getVert 1) ⊓ Z Rg (p.walk.getVert 3) ∧
                H ≤ fixedCore Rg (p.walk.getVert 2) ∧
                (∀ x ∈ H, k⁻¹*x*k = x) ∧
                ⁅Z Rg (act Rg k a') ⊓ Q Rg (act Rg k a),Q Rg (p.walk.getVert 2)⁆ = H ∧
                ⁅Z Rg a ⊓ Q Rg a',Q Rg (p.walk.getVert 2)⁆ = H ∧
                (∀ i, (p.act k).walk.getVert i = act Rg k (p.walk.getVert i))) :=
  (coreExhaustion_or_cubic_backward_kernels h e hz).imp (rankTwo_of_exhaustion h e hz) id


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
