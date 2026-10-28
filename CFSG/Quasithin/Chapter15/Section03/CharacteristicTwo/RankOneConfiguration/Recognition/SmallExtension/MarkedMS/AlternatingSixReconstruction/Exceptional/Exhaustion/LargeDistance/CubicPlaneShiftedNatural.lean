module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneReciprocalKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusGrowth

/-!
# The order-sixteen shifted comparison in the cubic plane branch

For overlapping critical paths a--c--z and d--a--c, a failed shifted
comparison gives the retained radius line H = [V_a intersect Q_c,
Z_z intersect Q_a]. The reciprocal-kernel calculation puts H in the actual
moving cover at z. On the order-sixteen cover, its natural projection is
injective, so H's alignment with [Z_a,Z_z] modulo the full endpoint center
is an equality of the two literal subgroups.

If the forward Baumann slice of U_c at a is strict, the full intersection
Z_c intersect Z_a is the first-edge seed. The failure line lies there and
in the first backward edge seed. When those two edge kernels generate G_a,
H is central in G_a. Equality with the critical line contradicts its known
noncentrality. Thus the shifted comparison holds on the order-sixteen cover
under these original generating and strict-forward hypotheses.

The original paired backward selector supplies such generating edges. Its
same component switch transports the strict forward slice, radius escape
and cover order to the alternate critical endpoint. The selected application
proves the comparison for every subgroup of the full shifted kernel, hence
for both the full and moving kernels, on the backward branch actually
chosen by that selector. The whole-core and literal C.1.32 applications
retain both covers; a failed comparison in this strict-forward configuration
must have moving-cover order thirty-two.

This proves this specialized part of the comparison in MS93 (5.12)(1).
The augmentation-cover comparison, other slice configurations, terminal
contradiction, remaining radical/image/distance cases, both core exhaustions
and unconditional A6 reconstruction remain open. The graph and quotient are
the original cubic ones: projection kernel E, nontrivial odd E/Q, and the
specified proper odd-index radical without a Sylow assumption.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.6)--(5.8) and (5.12)(1), printed pp.866--867,
917--920,924--925; Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk


include h e hz hk in
private theorem graph_moving_center_eq_bot_of_sixteen
    {a : Vertex Rg} (ha : color Rg a = false) (hn : Nat.card (U Rg a) = 16) :
    U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) = ⊥ := by
  obtain ⟨_,_,_,_,_,_,f,hf,hker,_⟩ := graph_cover h e hz hk a ha
  have hr : Nat.card f.range = 16 := by
    rw [MonoidHom.range_eq_top.mpr hf,Nat.card_congr topEquiv.toEquiv]
    change Nat.card (natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      finrank_natural_even (Fin 6) (by decide)]
    rfl
  have hc := f.ker.card_mul_index
  rw [index_ker,hr,hn] at hc
  have he : f.ker.map (U Rg a).subtype =
      U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    rw [hker]
    change ((centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))).comap
      (U Rg a).subtype).map (U Rg a).subtype = _
    rw [map_comap_eq,range_subtype,inf_comm]
  rw [←he,card_eq_one.mp (show Nat.card f.ker = 1 by omega),Subgroup.map_bot]

private theorem central_join_cancel {J : Type*} [Group J]
    (A B U C : Subgroup J) (hA : A ≤ U) (hB : B ≤ U)
    (hC : C ≤ centralizer (U : Set J)) (hdis : U ⊓ C = ⊥)
    (he : A ⊔ C = B ⊔ C) : A = B := by
  have step (A B : Subgroup J) (hA : A ≤ U) (hB : B ≤ U)
      (he : A ⊔ C ≤ B ⊔ C) : A ≤ B := by
    intro x hx
    have hxc : x ∈ (B : Set J) * (C : Set J) := by
      rw [←coe_mul_of_right_le_normalizer_left B C
        ((hC.trans (centralizer_le hB)).trans (Subgroup.centralizer_le_normalizer _))]
      exact he (mem_sup_left hx)
    obtain ⟨b,hb,c,hc,rfl⟩ := hxc
    have hcU : c ∈ U := by
      have hh := U.mul_mem (U.inv_mem (hB hb)) (hA hx)
      simpa only [inv_mul_cancel_left] using hh
    have hc1 : c = 1 := mem_bot.mp (hdis ▸ (show c ∈ U ⊓ C from ⟨hcU,hc⟩))
    change b * c ∈ B
    rw [hc1,mul_one]
    exact hb
  exact le_antisymm (step A B hA hB he.le) (step B A hB hA he.ge)

include h e hz hk in
/-- On the order-sixteen cover the shifted failure line is the literal
critical line, rather than merely its image modulo the endpoint center. -/
theorem plane_shifted_failure_line_eq_of_sixteen
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    (K : Subgroup (FreeAmalgam Rg)) (hK : K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2))
    (hfail : ¬ ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg a⁆ ⊔ ⁅Z Rg a,Z Rg z⁆)
    (hn : Nat.card (U Rg z) = 16) :
    ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆ =
      ⁅Z Rg a,Z Rg z⁆ := by
  let H := ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆
  let T := ⁅Z Rg a,Z Rg z⁆
  let C := stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have ht : color Rg (p.walk.getVert 3) = true := by
    have hc : color Rg (p.walk.getVert 2) = false := q.end_color
    have hh := adjacent_color_ne Rg hct
    rw [hc] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  have hYt : V Rg a ⊓ Q Rg (p.walk.getVert 2) ≤
      Q Rg (p.walk.getVert (p.walk.length-1)) := by
    rw [hl]
    exact inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hAY : Z Rg a ≤ V Rg a ⊓ Q Rg (p.walk.getVert 2) := by
    refine le_inf (Z_le_VBall Rg _ 2) ?_
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact hb
  have halign := (plane_radius_kernel_alignment h e hz hk u hR p (hsmall _ _ p)
    _ inf_le_left hYt hAY hescape).2.2.2.2.2
  have hHU : H ≤ U Rg z :=
    (plane_shifted_kernel_failure_reciprocal h e hz hk u hR hb4 hsmall p q hqa
      hescape K hK hfail).2.2.2.2.1.trans inf_le_right
  let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by
        rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      z p.end_color p.critical)
  have hTU : T ≤ U Rg z := by
    change ⁅Z Rg a,Z Rg z⁆ ≤ _
    rw [commutator_comm,←small_critical_moving_commutator_eq h e hz hk pr (hsmall _ _ pr)]
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) z pr.start_color
        (by rw [(sourceGeometry h).distance_constant _ pr.start_color]; exact sourceDistance_pos h)
        pr.critical).trans (U_normalized z))
  have hUC : U Rg z ⊓ C = ⊥ := le_bot_iff.mp
    ((inf_le_inf_left _ (show C ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
      from inf_le_right)).trans_eq (graph_moving_center_eq_bot_of_sixteen h e hz hk p.end_color hn))
  exact central_join_cancel H T (U Rg z) C hHU hTU
    (inf_le_right.trans (centralizer_le ((DistanceEight.U_le_Z Rg z).trans
      (Z_le_stabilizer Rg z)))) hUC halign

include h e hz hk in
/-- A strict forward slice and the actual generating backward edges put the
shifted failure line in the original starting stabilizer's center. -/
theorem plane_shifted_failure_central_of_strict_forward
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    (K : Subgroup (FreeAmalgam Rg)) (hK : K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2))
    (hfail : ¬ ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg a⁆ ⊔ ⁅Z Rg a,Z Rg z⁆)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a)
    (hs : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
    ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆ ≤
      centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  let H := ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb4
  have hav : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have has : Adjacent Rg a (q.walk.getVert 1) := by
    have hh := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
    simpa only [hqa] using hh
  have hr := plane_shifted_kernel_failure_reciprocal h e hz hk u hR hb4 hsmall
    p q hqa hescape K hK hfail
  have hHs : H ≤ Z Rg (q.walk.getVert 1) := hr.2.2.2.2.2.1
  have hXZ := (plane_small_four_omega_generated h e hz hk u hR hb4 hsmall z p.end_color).2
  have hline := plane_four_full_kernel_line h e hz hk u hR hb4 hsmall p
    (V Rg a ⊓ Q Rg (p.walk.getVert 2)) inf_le_left inf_le_right (by rwa [hXZ])
  rw [hXZ] at hline
  have hHc : H ≤ Z Rg (p.walk.getVert 2) := hline.2.2.1.trans inf_le_right
  have hHa : H ≤ Z Rg a :=
    hHs.trans (adjacent_Z_le Rg p.start_color has)
  have hHv : H ≤ Z Rg (p.walk.getVert 1) :=
    (le_inf hHc hHa).trans_eq
      (plane_strict_slice_eq_edge h e hz hk u hR p.start_color q.end_color hav hcv hs).2.1
  exact (le_inf hHs hHv).trans
    ((plane_generating_edge_seed_intersection h e hz hk u hR p.start_color has hav hgen).le.trans
      inf_le_right)

include h e hz hk in
/-- The strict-forward branch of the literal shifted comparison is proved
for the order-sixteen cover and generating backward configuration. -/
theorem plane_shifted_comparison_of_sixteen_strict_forward
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hescape : ¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a)
    (K : Subgroup (FreeAmalgam Rg)) (hK : K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2))
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a)
    (hs : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) (hn : Nat.card (U Rg z) = 16) :
    ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg a⁆ ⊔ ⁅Z Rg a,Z Rg z⁆ := by
  by_contra hfail
  have hc := plane_shifted_failure_central_of_strict_forward h e hz hk u hR hb4 hsmall
    p q hqa hescape K hK hfail hgen hs
  rw [plane_shifted_failure_line_eq_of_sixteen h e hz hk u hR hb4 hsmall
    p q hqa hescape K hK hfail hn] at hc
  exact critical_commutator_not_central h e hz hk p hc


include h e hz hk in
/-- Apply the strict-forward comparison to a backward path produced by the
original paired selector. The same component switch transports escape,
the strict slice and the order-sixteen cover to the alternate endpoint. -/
theorem plane_selected_strict_forward_comparison_of_sixteen
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hescape : ¬ ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg (alpha Rg))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) (hn : Nat.card (U Rg z) = 16) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf (L ⊔ R),
      let x := (embedM Rg r)⁻¹
      ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let d := act Rg g (p.walk.getVert 2)
          let comparison := fun w (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w) =>
            ∃ q : CriticalPath Rg (sourceGeometry h) d (v.walk.getVert 2),
              q.walk.getVert 1 = t ∧
              (∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i) ∧
              ∀ K : Subgroup (FreeAmalgam Rg), K ≤ Z Rg d ⊓ Q Rg (v.walk.getVert 2) →
                ⁅K,Z Rg w⁆ ≤ ⁅K,Z Rg w ⊓ Q Rg (alpha Rg)⁆ ⊔ ⁅Z Rg (alpha Rg),Z Rg w⁆
          comparison z p ∨ comparison (act Rg x z) p' := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have ha1 : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hc1 : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,r,hr,p',hverts,hps,hgen,hpair,hnorm,hinside,g,hg,hgt,hstrict,halt⟩ :=
    plane_small_critical_backward_shift h e hz hk u hR p (hsmall _ _ p) hc1 hs
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hat' : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←show act Rg x (alpha Rg) = alpha Rg from hx]
    exact (adjacent_act_iff Rg x _ _).mpr hat
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat] at hgen hpair
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat'] at hpair
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl ha1] at hnorm hinside
  have hfirst : Q Rg t ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg (alpha Rg) := by
    apply le_antisymm
    · exact sup_le (fun _ hv => hv.2 _ (adjacent_symm Rg hat))
        (fun _ hv => hv.2 _ (adjacent_symm Rg ha1))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_left ((le_sup_left.trans hinside).trans le_sup_right))
        ((le_sup_right.trans hinside).trans le_sup_right)
  have hQfirst : Q Rg (p'.walk.getVert 1) = Q Rg (p.walk.getVert 1) := by
    rw [hverts 1,Q_act]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg))).inv_mem hnorm)
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hs' : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p'.walk.getVert 2)) := by
    have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
        (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h) hb
        (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hx))
    rw [hverts 2]
    change 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg x (p.walk.getVert 2)))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hs
  have hn' : Nat.card (U Rg (act Rg x z)) = 16 := by
    rw [U_act,card_map_of_injective (MulAut.conj x⁻¹).injective]
    exact hn
  have hescape' : ¬ ⁅V Rg (alpha Rg) ⊓ Q Rg (p'.walk.getVert 2),Z Rg (act Rg x z)⁆ ≤
      Z Rg (alpha Rg) := by
    intro he
    apply hescape
    apply (map_le_map_iff_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
      (MulAut.conj x⁻¹).injective).mp
    rw [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,
      ←V_act,←Q_act,←Z_act,←Z_act,show act Rg x (alpha Rg) = alpha Rg from hx,←hverts 2]
    exact he
  refine ⟨t,hat,r,hr,p',hverts,hgen,hpair,g,hg,hgt,?_⟩
  have hl' : p'.walk.length = 4 := p'.length_eq_b.trans hb4
  have cast_end {d v w : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) d v)
      (he : v = w) : ∃ q' : CriticalPath Rg (sourceGeometry h) d w,
        ∀ i, q'.walk.getVert i = q.walk.getVert i := by
    subst w
    exact ⟨q,fun _ => rfl⟩
  rcases halt with ⟨q,hq1,hqv⟩ | ⟨q,hq1,hqv⟩
  · obtain ⟨q',hq'⟩ := cast_end q (show p.walk.getVert (p.walk.length-2) =
        p.walk.getVert 2 by rw [hl])
    have hqv' : ∀ i ≤ 2, q'.walk.getVert (i+2) = p.walk.getVert i :=
      fun i hi => (hq' (i+2)).trans (hqv i (by omega))
    have hq1' := (hq' 1).trans hq1
    refine Or.inl ⟨q',hq1',hqv',?_⟩
    intro K hK
    apply plane_shifted_comparison_of_sixteen_strict_forward h e hz hk u hR hb4 hsmall
      p q' (by simpa only [SimpleGraph.Walk.getVert_zero] using hqv' 0 (by omega))
      hescape K hK
    · rw [hq1']
      exact hfirst
    · exact hs
    · exact hn
  · obtain ⟨q',hq'⟩ := cast_end q (show p'.walk.getVert (p'.walk.length-2) =
        p'.walk.getVert 2 by rw [hl'])
    have hqv' : ∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i :=
      fun i hi => (hq' (i+2)).trans (hqv i (by omega))
    have hq1' := (hq' 1).trans hq1
    refine Or.inr ⟨q',hq1',hqv',?_⟩
    intro K hK
    apply plane_shifted_comparison_of_sixteen_strict_forward h e hz hk u hR hb4 hsmall
      p' q' (by simpa only [SimpleGraph.Walk.getVert_zero] using hqv' 0 (by omega))
      hescape' K hK
    · rw [hq1',hQfirst]
      exact hfirst
    · exact hs'
    · exact hn'

omit hk in
include h e hz in
/-- On the original whole-core reduction, a failed shifted comparison with
strict forward slice and generating backward edges requires the order-32 cover. -/
theorem coreExhaustion_or_cubic_strict_forward_comparison :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∀ a z d (p : CriticalPath Rg (sourceGeometry h) a z)
            (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2)),
            q.walk.getVert 2 = a →
            (¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a) →
            ∀ K : Subgroup (FreeAmalgam Rg), K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2) →
              Q Rg (q.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a →
              2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) →
              ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg a⁆ ⊔ ⁅Z Rg a,Z Rg z⁆ ∨
                Nat.card (U Rg z) = 32)) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    intro hb4 hsmall a z d p q hqa hescape K hK hgen hstrict
    rcases hcovers z p.end_color with hn | hn
    · exact Or.inl (plane_shifted_comparison_of_sixteen_strict_forward h e hz hk u hplane
        hb4 hsmall p q hqa hescape K hK hgen hstrict hn)
    · exact Or.inr hn

omit hk in
include h e hz in
/-- Literal C.1.32 application retaining the original projection, radical,
full central attachments and both cover alternatives. -/
theorem rankTwo_or_cubic_strict_forward_comparison :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∀ a z d (p : CriticalPath Rg (sourceGeometry h) a z)
            (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2)),
            q.walk.getVert 2 = a →
            (¬ ⁅V Rg a ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg a) →
            ∀ K : Subgroup (FreeAmalgam Rg), K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2) →
              Q Rg (q.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a →
              2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) →
              ⁅K,Z Rg z⁆ ≤ ⁅K,Z Rg z ⊓ Q Rg a⁆ ⊔ ⁅Z Rg a,Z Rg z⁆ ∨
                Nat.card (U Rg z) = 32)) :=
  (coreExhaustion_or_cubic_strict_forward_comparison h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
