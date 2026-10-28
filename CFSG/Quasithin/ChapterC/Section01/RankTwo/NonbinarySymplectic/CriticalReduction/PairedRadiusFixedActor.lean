module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusBudget

/-!
# The full fixed actor under the small radius budget

The original seed joined with the full endpoint kernel centralizes the
literal intersection X_z intersect Q_a. A q-squared radius budget therefore
leaves at most q images on this actor. On the same selected source pair,
any nontrivial action saturates this budget on a whole neighboring seed.
Its full fixed kernel is then the original seed-kernel intersection.
Full-cover duality, the two original smaller movers and the actual paired
generation make that kernel normal, contradicting its retained B-index.

Thus the same pair centralizes the full actor. This eliminates its moving
case without placing either seed in the penultimate kernel. The remaining
comparison with that kernel in MS93 (5.11), printed p.923, is not asserted.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

private theorem saturated_fixed_kernel {G : Type*} [Group G]
    (V D E C : Subgroup G) [Finite V] [IsMulCommutative V]
    (hDV : D ≤ V) (hEV : E ≤ V) (hDC : D ≤ C) {q : ℕ} (hq : 0 < q)
    (hi : D.relIndex V ≤ q) (hlo : q ≤ C.relIndex E) :
    V ⊓ C = D ∧ E ⊔ D = V := by
  let : Finite E := Finite.of_injective (inclusion hEV) (inclusion_injective _)
  let T := V ⊓ C
  have hDT : D ≤ T := le_inf hDV hDC
  let : Finite T := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hTC : T.relIndex V = C.relIndex V := inf_relIndex_left _ _
  have hClo : q ≤ T.relIndex V := by
    rw [hTC]
    exact hlo.trans (relIndex_le_of_le_right hEV index_ne_zero_of_finite)
  have hp := relIndex_mul_relIndex D T V hDT inf_le_left
  have hpos : 0 < D.relIndex T := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hone : D.relIndex T = 1 := by nlinarith
  refine ⟨le_antisymm (relIndex_eq_one.mp hone) hDT,?_⟩
  let W := E ⊔ D
  have hWV : W ≤ V := sup_le hEV hDV
  let : Finite W := Finite.of_injective (inclusion hWV) (inclusion_injective _)
  let : CommGroup V := IsMulCommutative.instCommGroup
  have hsup := relIndex_sup_right (E.subgroupOf V) (D.subgroupOf V)
  rw [←subgroupOf_sup hEV hDV,relIndex_subgroupOf hWV,relIndex_subgroupOf hEV] at hsup
  have hDlo : q ≤ D.relIndex W := by
    rw [hsup]
    exact hlo.trans (relIndex_le_of_le_left hDC index_ne_zero_of_finite)
  have hp' := relIndex_mul_relIndex D W V le_sup_right hWV
  have hpos' : 0 < W.relIndex V := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hone' : W.relIndex V = 1 := by nlinarith
  exact le_antisymm hWV (relIndex_eq_one.mp hone')

private theorem commutator_eq_of_fixed_join {G : Type*} [Group G]
    (V E D A : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (hDV : D ≤ V) (hDA : D ≤ centralizer (A : Set G))
    (he : E ⊔ D = V) : ⁅E,A⁆ = ⁅V,A⁆ := by
  rw [commutator_comm E,commutator_comm V]
  apply le_antisymm (commutator_mono le_rfl hEV)
  apply commutator_le.mpr
  intro a ha v hv
  have hn : E ≤ normalizer (D : Set G) :=
    (hEV.trans (V.le_centralizer.trans (centralizer_le hDV))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hv' : v ∈ (E : Set G)*(D : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right E D hn,he]
    exact hv
  obtain ⟨e,he,d,hd,rfl⟩ := hv'
  have hc : ⁅a,d⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hDA hd a ha)
  rw [commutatorElement_mul_right_eq_mul_conj,hc,mul_one,mul_inv_cancel_right]
  exact commutator_mem_commutator ha he

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem small_radius_actor_centralizer
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (V d.radical a) ≤ Nat.card F^2) :
    Z d.radical a ⊔ Q d.radical z ≤
      centralizer ((X d.radical z ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  let rev := (show CriticalSegment geometry from ⟨a,z,path⟩).reverse hedge (by omega)
  have hrevfirst : rev.first=z := rfl
  have hzt : Adjacent d.radical z (rev.path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (rev.path.walk.adj_getVert_succ (by rw [rev.path.length_eq_b]; omega : 0 < rev.path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero,Nat.zero_add,hrevfirst] using hh
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hs : (Q d.radical z).relIndex (Z d.radical a)<Nat.card F^2 := by
    rw [(h.replacement_small_radius_critical_indices d path hb hi).1]
    nlinarith
  have hX : X d.radical z=Z d.radical z :=
    h.replacement_root_X_eq_Z d rev.path hb.le hzt hs
  apply sup_le
  · exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color)).trans
      (centralizer_le inf_le_right)
  · rw [hX]
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes z path.end_color))).trans (centralizer_le inf_le_left)

/-- The original small-radius budget bounds the fixed index of the full
X-intersection on the whole radius, without endpoint-stabilizer containment. -/
theorem Input.replacement_small_radius_fixed_actor_budget
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (V d.radical a) ≤ Nat.card F^2) :
    (centralizer ((X d.radical z ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)).relIndex
      (V d.radical a) ≤ Nat.card F := by
  let := finite_stabilizer d.radical a
  let : Finite (V d.radical a) := Finite.of_injective
    (inclusion ((geometry.V_le_Q (by omega) a path.start_color).trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  exact (relIndex_le_of_le_left
    ((sup_le_sup_left inf_le_right _).trans (small_radius_actor_centralizer h d path hb hi))
    index_ne_zero_of_finite).trans
      (h.replacement_small_radius_critical_indices d path hb hi).2.2.2

private theorem selected_kernel_not_normal
    {geometry : Geometry d.radical} {a v t : Vertex d.radical}
    (hb : 4 < geometry.b d.radical) (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v))
    (C : Subgroup (FreeAmalgam d.radical))
    (hi : C.relIndex (Z d.radical v) ≤ Nat.card F) :
    ¬ stabilizer d.radical a ≤ normalizer
      (((Z d.radical v ⊓ C) ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  intro hn
  let D := (Z d.radical v ⊓ C) ⊔ Z d.radical a
  have hYV := neighbor_seed_join_le_radius hat hvt
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) a ha)
  let := finite_stabilizer d.radical a
  let : Finite (Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hYQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hidx := (neighbor_seed_join_index_le geometry (by omega) ha hat hvt).trans
    (h.replacement_neighbor_seed_index_le_cube d geometry hb.le ha hat hvt)
  have hDi : (Z d.radical a).relIndex D < Nat.card F^4 :=
    lt_of_le_of_lt ((relIndex_le_of_le_right (sup_le_sup inf_le_left le_rfl)
      index_ne_zero_of_finite).trans hidx)
      ((pow_lt_pow_iff_right₀ (show 1<Nat.card F from Finite.one_lt_card)).mpr (by decide))
  have hDB := h.replacement_small_radius_le_B d geometry (by omega) ha D
    ((sup_le_sup inf_le_left le_rfl).trans hYV) ((Ltilde_le_stabilizer a).trans hn) hDi
  have hkernel : Z d.radical v ⊓ C ≤ B d.radical a (geometry.Z_normal a) := le_sup_left.trans hDB
  let := finite_Z d.radical v
  have hZi : (B d.radical a (geometry.Z_normal a)).relIndex (Z d.radical v) ≤ Nat.card F := by
    apply le_trans (relIndex_le_of_le_left hkernel index_ne_zero_of_finite)
    simpa only [inf_relIndex_left] using hi
  exact hmove.not_ge ((relIndex_le_of_le_right (H := B d.radical a (geometry.Z_normal a))
    (U_le_Z v) index_ne_zero_of_finite).trans hZi)

private theorem selected_actor_not_moving
    {geometry : Geometry d.radical} {a z v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (V d.radical a) ≤ Nat.card F^2)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v))
    (hgen : (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical t) (Nat.card F^2) ⊔ Z d.radical z) ⊔
        (Z d.radical z).map (MulAut.conj x).toMonoidHom=stabilizer d.radical a)
    (hfixed : (Z d.radical a ⊓ centralizer (Subgroup.SmallMover.join
      (U d.radical v) (Q d.radical v) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
      centralizer (Subgroup.SmallMover.join (U d.radical (act d.radical x v))
        (Q d.radical (act d.radical x v)) (Q d.radical (act d.radical x t)) (Nat.card F^2) : Set _) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (hc₁ : ⁅Z d.radical v,Q d.radical a⁆ ≤ Z d.radical a ⊓
      centralizer (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical)))
    (hc₂ : ⁅Z d.radical (act d.radical x v),Q d.radical a⁆ ≤ Z d.radical a ⊓
      centralizer (Subgroup.SmallMover.join (U d.radical (act d.radical x v))
        (Q d.radical (act d.radical x v)) (Q d.radical (act d.radical x t)) (Nat.card F^2) : Set _)) :
    ⁅Z d.radical v,X d.radical z ⊓ Q d.radical a⁆=⊥ := by
  by_contra hn
  let A := X d.radical z ⊓ Q d.radical a
  let C := centralizer (A : Set (FreeAmalgam d.radical))
  let w := act d.radical x v
  let Y := Z d.radical v ⊔ Z d.radical w
  let D := Y ⊓ (Z d.radical a ⊔ Q d.radical z)
  let K₁ := Z d.radical v ⊓ C
  let K₂ := Z d.radical w ⊓ C
  let f := (MulAut.conj x).toMonoidHom
  have ha : act d.radical x a=a := hx
  have hatx : Adjacent d.radical a (act d.radical x t) := by
    rw [←ha]; exact (adjacent_act_iff d.radical x a t).mpr hat
  have hwtx : Adjacent d.radical w (act d.radical x t) :=
    (adjacent_act_iff d.radical x v t).mpr hvt
  have hvcolor : color d.radical v=false := by
    have hh := adjacent_color_ne d.radical hat
    have hh' := adjacent_color_ne d.radical hvt
    rw [path.start_color] at hh
    cases ht : color d.radical t <;> cases hv : color d.radical v <;> simp_all
  have hwcolor : color d.radical w=false := by rw [show w=act d.radical x v from rfl,action_preserves_color,hvcolor]
  have hYV : Y ≤ V d.radical a := sup_le
    (le_sup_left.trans (neighbor_seed_join_le_radius hat hvt))
    (le_sup_left.trans (neighbor_seed_join_le_radius hatx hwtx))
  let := finite_stabilizer d.radical a
  let : Finite (V d.radical a) := Finite.of_injective
    (inclusion ((geometry.V_le_Q (by omega) a path.start_color).trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  let : Finite Y := Finite.of_injective (inclusion hYV) (inclusion_injective _)
  let := V_abelian_of_four_lt d.radical path.start_color hb
  let : IsMulCommutative Y := le_centralizer_iff_isMulCommutative.mp
    (hYV.trans ((V d.radical a).le_centralizer.trans (centralizer_le hYV)))
  have hDcentral : D ≤ C := inf_le_right.trans (small_radius_actor_centralizer h d path hb hi)
  have hbudget : D.relIndex Y ≤ Nat.card F := by
    rw [inf_relIndex_left]
    exact (relIndex_le_of_le_right hYV index_ne_zero_of_finite).trans
      ((relIndex_le_of_le_left (sup_le_sup_left inf_le_right _) index_ne_zero_of_finite).trans
        (h.replacement_small_radius_critical_indices d path hb hi).2.2.2)
  have hAS (c s : Vertex d.radical) (has : Adjacent d.radical a s)
      (hcs : Adjacent d.radical c s) (hc : color d.radical c=false) : A ≤ stabilizer d.radical c :=
    inf_le_right.trans (Q_le_stabilizer_of_dist_le_two a c path.start_color hc
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two has hcs))
  have hlower (c s : Vertex d.radical) (has : Adjacent d.radical a s)
      (hcs : Adjacent d.radical c s) (hc : color d.radical c=false)
      (hne : ⁅Z d.radical c,A⁆≠⊥) : Nat.card F ≤ C.relIndex (Z d.radical c) := by
    have hescape : ¬ A ≤ Q d.radical c := by
      intro he
      exact hne (le_bot_iff.mp ((commutator_mono le_rfl he).trans_eq (geometry.centralizes c hc)))
    let := finite_Z d.radical c
    exact (h.replacement_natural_fixed_index_lower d geometry hb.le hc A (hAS c s has hcs hc) hescape).trans
      (relIndex_le_of_le_right (U_le_Z c) index_ne_zero_of_finite)
  have hlo₁ := hlower v t hat hvt hvcolor hn
  obtain ⟨hkernel,hjoin₁⟩ := saturated_fixed_kernel Y D (Z d.radical v) C
    inf_le_left le_sup_left hDcentral Nat.card_pos hbudget hlo₁
  have hK₁D : K₁ ≤ Z d.radical a ⊔ Q d.radical z := by
    exact ((inf_le_inf le_sup_left le_rfl).trans hkernel.le).trans inf_le_right
  have hK₂D : K₂ ≤ Z d.radical a ⊔ Q d.radical z := by
    exact ((inf_le_inf le_sup_right le_rfl).trans hkernel.le).trans inf_le_right
  have hsmall := (h.replacement_small_radius_critical_indices d path hb hi).2.1
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hs : (Q d.radical a).relIndex (Z d.radical z)<Nat.card F^2 := by rw [hsmall]; nlinarith
  have hcomm : ⁅Z d.radical v,A.map f⁆ ≤ ⁅Z d.radical v,A⁆ := by
    have hwmap : (Z d.radical w).map f=Z d.radical v := by
      simpa only [inv_inv,←act_mul,mul_inv_cancel,act_one] using
        (Z_act d.radical x⁻¹ (act d.radical x v)).symm
    have he : ⁅Z d.radical v,A.map f⁆=⁅Z d.radical w,A⁆.map f := by rw [map_commutator,hwmap]
    rw [he]
    by_cases hz : ⁅Z d.radical w,A⁆=⊥
    · rw [hz,Subgroup.map_bot]; exact bot_le
    have hlo₂ := hlower w (act d.radical x t) hatx hwtx hwcolor hz
    obtain ⟨_,hjoin₂⟩ := saturated_fixed_kernel Y D (Z d.radical w) C
      inf_le_left le_sup_right hDcentral Nat.card_pos hbudget hlo₂
    have hcommon : ⁅Z d.radical v,A⁆=⁅Z d.radical w,A⁆ :=
      (commutator_eq_of_fixed_join Y (Z d.radical v) D A le_sup_left inf_le_left hDcentral hjoin₁).trans
        (commutator_eq_of_fixed_join Y (Z d.radical w) D A le_sup_right inf_le_left hDcentral hjoin₂).symm
    have hcent : ⁅Z d.radical v,A⁆ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
      have hboth := le_inf ((commutator_mono le_rfl inf_le_right).trans hc₁)
        (hcommon.le.trans (((commutator_mono le_rfl inf_le_right).trans hc₂).trans inf_le_right))
      rw [hfixed] at hboth
      exact hboth.trans inf_le_right
    rw [←hcommon]
    rintro y ⟨u,hu,rfl⟩
    change x*u*x⁻¹ ∈ _
    rw [hcent hu x hx,mul_inv_cancel_right]
    exact hu
  have hQa : (Q d.radical a).map f=Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hx)
  have hAfS : A.map f ≤ stabilizer d.radical v :=
    ((map_mono (f := f) (show A ≤ Q d.radical a from inf_le_right)).trans_eq hQa).trans
      (Q_le_stabilizer_of_dist_le_two a v path.start_color hvcolor
        (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hat hvt))
  have hKmap : K₁ ≤ K₂.map f := by
    have hh := h.replacement_root_neighbor_fixed_antitone_of_commutator_le d path hb.le
      hat hvt hs (A.map f) A hAfS (hAS v t hat hvt hvcolor) hcomm
    have hwmap : (Z d.radical w).map f=Z d.radical v := by
      simpa only [inv_inv,←act_mul,mul_inv_cancel,act_one] using
        (Z_act d.radical x⁻¹ (act d.radical x v)).symm
    dsimp only [K₁,K₂,C]
    rw [←map_inf_centralizer_of_injective f (MulAut.conj x).injective,hwmap]
    exact hh
  have hZa : (Z d.radical a).map f=Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a hx)
  have hSa : (stabilizer d.radical a).map f=stabilizer d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical a).le_normalizer hx)
  have haS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hproduct : ⁅Z d.radical a ⊔ Q d.radical z,Z d.radical z⁆ ≤ Z d.radical a := by
    apply commutator_le.mpr
    intro y hy z' hz'
    have hy' : y ∈ (Z d.radical a : Set (FreeAmalgam d.radical))*(Q d.radical z : Set _) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ (haS.trans (Q_normalized _ z))]
      exact hy
    obtain ⟨u,hu,k,hk,rfl⟩ := hy'
    have hkc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes z path.end_color)) hk
    have he : ⁅k,z'⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hkc z' hz').symm
    rw [commutatorElement_mul_left_eq_conj_mul,he,mul_one,mul_inv_cancel,one_mul]
    exact critical_commutator_le_start_seed path (commutator_mem_commutator hu hz')
  have hd₁ := (commutator_mono hK₁D le_rfl).trans hproduct
  have hd₂ := map_mono (f := f) ((commutator_mono hK₂D le_rfl).trans hproduct)
  rw [map_commutator,hZa] at hd₂
  have hdmap := (commutator_mono hKmap le_rfl).trans hd₂
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hzmapS : (Z d.radical z).map f ≤ stabilizer d.radical a := by
    have hh := map_mono hzS (f := f); rwa [hSa] at hh
  have hn₁ := normalizes_sup_of_displacement _ _ _ (hzS.trans (Z_normalized d.radical a)) hd₁
  have hn₂ := normalizes_sup_of_displacement _ _ _ (hzmapS.trans (Z_normalized d.radical a)) hdmap
  have hCi : C.relIndex (Z d.radical v) ≤ Nat.card F :=
    (relIndex_le_of_le_right (le_sup_left.trans hYV) index_ne_zero_of_finite).trans
      (h.replacement_small_radius_fixed_actor_budget d path hb hi)
  let := finite_Z d.radical v
  have hUi := (relIndex_le_of_le_right (U_le_Z v) index_ne_zero_of_finite).trans hCi
  have htcolor : color d.radical t=true := by
    have hh := adjacent_color_ne d.radical hat
    rw [path.start_color] at hh
    cases ht : color d.radical t
    · exact False.elim (hh ht.symm)
    · rfl
  have hAT : A ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical htcolor hat)
  have hJn := h.replacement_small_mover_join_normalizes_full_seed_fixed d geometry hb.le
    hvcolor hvt A hAT hUi
  have hJZa := (Subgroup.SmallMover.join_le (U d.radical v) (Q d.radical v)
    (Q d.radical t) (Nat.card F^2)).trans
    ((show Q d.radical t ≤ stabilizer d.radical a from
      fun _ hx => hx.2 a (adjacent_symm _ hat)).trans (Z_normalized d.radical a))
  have hJn' := (le_inf hJn hJZa).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact selected_kernel_not_normal h d hb path.start_color hat hvt hmove C hCi
    (hgen ▸ sup_le (sup_le hJn' hn₁) hn₂)

private theorem neighbor_commutator_fixed
    {geometry : Geometry d.radical} {a z t v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (hs : (Q d.radical a).relIndex (Z d.radical z)<Nat.card F^2)
    (hequal : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    ⁅Z d.radical v,Q d.radical a⁆ ≤ Z d.radical a ⊓
      centralizer (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  obtain ⟨hc,hd⟩ := h.replacement_equal_root_neighbor_commutator d path hb.le hat hvt hs
    (h.replacement_small_mover_index_le_square_of_four_lt d geometry hb path.start_color hat) hequal
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hQJ := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
    (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
    (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
    (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
      (h.replacement_two_group d) (h.replacement_core_le d)))
  rw [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hQJ
  have hcomm := (commutator_mono le_rfl hQJ).trans hd
  refine le_inf (hcomm.trans hc) ?_
  rw [hequal]
  intro y hy j hj
  exact (mem_omegaCenter_iff.mp (hcomm hy)).2.2 j hj

/-- The actual paired source conjugator can be retained with its two
generation identities and whole-seed fixed equality while its full joined
seed centralizes X_z intersect Q_a. No penultimate-kernel containment is assumed. -/
theorem Input.replacement_paired_small_radius_fixed_actor
    {geometry : Geometry d.radical} (p p' : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hl : BackwardLink geometry (pairedRadiusChoice geometry (Nat.card F)) p p')
    (hi : (Q d.radical p.last).relIndex (V d.radical p.first) ≤ Nat.card F^2) :
    ∃ x ∈ Ltilde d.radical p.first,
      let t := p'.path.walk.getVert 1
      let v := p'.first
      let w := act d.radical x v
      let J := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical t) (Nat.card F^2)
      let J' := Subgroup.SmallMover.join (U d.radical w) (Q d.radical w)
        (Q d.radical (act d.radical x t)) (Nat.card F^2)
      Adjacent d.radical p.first (act d.radical x t) ∧ Adjacent d.radical w (act d.radical x t) ∧
      (B d.radical p.first (geometry.Z_normal p.first)).relIndex (U d.radical w)=nextMovingIndex p ∧
      (J ⊔ Z d.radical p.last) ⊔ (Z d.radical p.last).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical p.first ∧
      (J' ⊔ Z d.radical p.last) ⊔ (Z d.radical p.last).map (MulAut.conj x⁻¹).toMonoidHom =
        stabilizer d.radical p.first ∧
      (Z d.radical p.first ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓ centralizer (J' : Set _) =
        Z d.radical p.first ⊓ centralizer (stabilizer d.radical p.first : Set (FreeAmalgam d.radical)) ∧
      ⁅Z d.radical v ⊔ Z d.radical w,X d.radical p.last ⊓ Q d.radical p.first⁆=⊥ := by
  obtain ⟨t,hchoice,hat,hvt,hfirst⟩ := hl.choice
  obtain ⟨x,hx,hatx,hvtx,hix,hgen,hgen',hfixed⟩ := hchoice.2
  refine ⟨x,hx,?_⟩
  dsimp only
  rw [hfirst]
  refine ⟨hatx,hvtx,hix,hgen,hgen',hfixed,?_⟩
  have hxS := Ltilde_le_stabilizer p.first hx
  have hxinv := (stabilizer d.radical p.first).inv_mem hxS
  have hax : act d.radical x p.first=p.first := hxS
  have htwo : p'.path.walk.getVert 2=p.first := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hl.overlap 0 (by omega)
  have hequal : Subgroup.SmallMover.join (U d.radical p'.first) (Q d.radical p'.first)
      (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical p.first) (Q d.radical p.first)
        (Q d.radical t) (Nat.card F^2) := by
    have hh := h.replacement_mover_agreement_of_four_lt d p' hb
    simpa only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero,
      htwo,hfirst] using hh.symm
  have hequalx : Subgroup.SmallMover.join (U d.radical (act d.radical x p'.first))
      (Q d.radical (act d.radical x p'.first)) (Q d.radical (act d.radical x t)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical p.first) (Q d.radical p.first)
        (Q d.radical (act d.radical x t)) (Nat.card F^2) := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hequal
    rw [Subgroup.SmallMover.join_map _ (MulAut.conj x⁻¹).injective,
      Subgroup.SmallMover.join_map _ (MulAut.conj x⁻¹).injective,
      ←U_act,←Q_act,←Q_act,←U_act,←Q_act,hax] at hh
    exact hh
  have hs : (Q d.radical p.first).relIndex (Z d.radical p.last)<Nat.card F^2 := by
    rw [(h.replacement_small_radius_critical_indices d p.path hb hi).2.1]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  have hc₁ := neighbor_commutator_fixed h d p.path hb hat hvt hs hequal
  have hc₂ := neighbor_commutator_fixed h d p.path hb hatx hvtx hs hequalx
  have hmove₁ : Nat.card F < (B d.radical p.first (geometry.Z_normal p.first)).relIndex
      (U d.radical p'.first) := by
    obtain ⟨g,hg,hgv,hgt,hindex⟩ := hchoice.1
    rw [hindex]
    exact h.replacement_path_moving_index_gt_field d p.path hb
  have hmove₂ : Nat.card F < (B d.radical p.first (geometry.Z_normal p.first)).relIndex
      (U d.radical (act d.radical x p'.first)) := by
    rw [hix]
    exact h.replacement_path_moving_index_gt_field d p.path hb
  have hz₁ := selected_actor_not_moving h d p.path hb hi hat hvt x hxS hmove₁ hgen hfixed hc₁ hc₂
  have hundo (v : Vertex d.radical) : act d.radical x⁻¹ (act d.radical x v)=v := by
    rw [←act_mul,mul_inv_cancel,act_one]
  have hfixed' : (Z d.radical p.first ⊓ centralizer (Subgroup.SmallMover.join
      (U d.radical (act d.radical x p'.first)) (Q d.radical (act d.radical x p'.first))
      (Q d.radical (act d.radical x t)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
      centralizer (Subgroup.SmallMover.join (U d.radical (act d.radical x⁻¹ (act d.radical x p'.first)))
        (Q d.radical (act d.radical x⁻¹ (act d.radical x p'.first)))
        (Q d.radical (act d.radical x⁻¹ (act d.radical x t))) (Nat.card F^2) : Set _) =
      Z d.radical p.first ⊓ centralizer (stabilizer d.radical p.first : Set (FreeAmalgam d.radical)) := by
    simp only [hundo]
    rw [inf_right_comm]
    exact hfixed
  have hc₁' := hc₁
  have hz₂ := selected_actor_not_moving h d p.path hb hi hatx hvtx x⁻¹ hxinv hmove₂ hgen' hfixed' hc₂
    (by simpa only [hundo] using hc₁')
  exact commutator_eq_bot_iff_le_centralizer.mpr (sup_le
    (commutator_eq_bot_iff_le_centralizer.mp hz₁) (commutator_eq_bot_iff_le_centralizer.mp hz₂))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
