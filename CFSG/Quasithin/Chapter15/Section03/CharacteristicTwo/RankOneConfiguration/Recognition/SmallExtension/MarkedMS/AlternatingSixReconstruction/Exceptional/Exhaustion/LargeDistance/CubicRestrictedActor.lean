module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRestrictedCover

/-!
# Radius centrality in the cubic full-symmetric branch

The reverse moving layer has image of order at least four modulo the actual
two-core. On the augmentation cover, restrict it while preserving its full
commutator with the initial moving layer. The marked model calculation then
supplies an even involution. On the natural cover the entire reverse moving
layer already has the required commutator control. The chief-factor budget
and abelian edge generation therefore prove radius centrality in both cases.

The full fixed attachment, the cubic action kernel and the original factor
embeddings are retained. The final alternatives apply these conclusions to
the entire intrinsic core and the literal C.1.32 consumer. Terminal distance
exclusions and the final natural/exceptional assembly remain in
qt-e-ms-small-a6-reconstruction; this does not prove whole-core exhaustion.
Source: MS93 (5.2)(i)--(iii), printed pp.914--915. The restriction argument
adapts Natural.Exhaustion.LargeDistance.SectionFive.RestrictedActor.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "T" => edge L R
local notation "π" => CubicAction.projection h e hz hk

private theorem critical_seed_commutator_le {a c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a c) :
    ⁅Z T a,Z T c⁆ ≤ Z T a ⊓ Z T c := by
  have hac : Z T a ≤ stabilizer T c :=
    Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hca : Z T c ≤ stabilizer T a := by
    apply Z_le_stabilizer_of_dist_le c ((sourceGeometry h).exists_critical c p.end_color)
    rw [SimpleGraph.dist_comm,p.critical.1,
      (sourceGeometry h).distance_constant a p.start_color,
      (sourceGeometry h).distance_constant c p.end_color]
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp (hca.trans (Z_normalized T a)))
    (le_normalizer_iff_commutator_le_right.mp (hac.trans (Z_normalized T c)))

private theorem critical_radius_intersection_centralizes {a c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a c) (hb : 2 < sourceDistance h) :
    V T a ⊓ Q T (p.walk.getVert (p.walk.length-2)) ≤
      centralizer ((⁅Z T a,Z T c⁆ : Subgroup (FreeAmalgam T)) : Set (FreeAmalgam T)) := by
  have hQ : Q T a ≤ centralizer (Z T a : Set (FreeAmalgam T)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q T a p.start_color))
  exact ((inf_le_left.trans (V_le_Q T p.start_color hb)).trans hQ).trans
    (centralizer_le ((critical_seed_commutator_le h p).trans inf_le_left))

include h e hz hk in
/-- A large forward seed image forces the reverse moving layer itself to
have image of order at least four, with the cubic kernel still retained. -/
theorem reverse_critical_moving_image_four_le {a c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a c)
    (hforward : 4 ≤ (Q T c).relIndex (Z T a)) :
    4 ≤ (Q T a).relIndex (U T c) := by
  obtain ⟨i,hi,hir,hiQ,_,hiU,_⟩ := graph_cover h e hz hk c p.end_color
  have hA : Z T a ≤ i.range := by
    rw [hir]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hB : Q T a ≤ centralizer (Z T a : Set (FreeAmalgam T)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q T a p.start_color))
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  rw [←hiU]
  apply embedded_centralizing_index_four_le h e hz hk i hi (Z T a) (Q T a) hA hB
  rwa [hiQ]

include h e hz hk in
/-- Reversing the actual critical pair also bounds the forward moving image. -/
theorem critical_forward_moving_image_four_le {a c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a c)
    (hforward : 4 ≤ (Q T c).relIndex (Z T a)) :
    4 ≤ (Q T c).relIndex (U T a) := by
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
    c p.end_color p.critical
  let q : CriticalPath T (sourceGeometry h) c a := CriticalPath.ofPair p.end_color hr
  exact reverse_critical_moving_image_four_le h e hz hk q
    (reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) p hforward)

private theorem even_involution (A : Subgroup (Equiv.Perm (Fin 6)))
    [IsElementaryAbelian 2 A] (hA : 4 ≤ Nat.card A) :
    ∃ a ∈ A, orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  by_contra hn
  have hnone : ∀ a ∈ A, a ≠ 1 → a ∉ alternatingGroup (Fin 6) := by
    intro a ha hne he
    exact hn ⟨a,ha,orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) hne,he⟩
  let f := (Equiv.Perm.sign (α := Fin 6)).comp A.subtype
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro a ha
    by_contra hne
    exact hnone a a.property (fun he => hne (Subtype.ext he)) ha
  have hc := Nat.card_le_card_of_injective f hf
  have ht : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card,Fintype.card_units_int]
  rw [ht] at hc
  omega

/-- The complete reverse moving group has an even involution in the original
marked symmetric quotient, for either cover order. -/
theorem critical_moving_even_actor {c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) (alpha T) c)
    (hforward : 4 ≤ (Q T c).relIndex (Z T (alpha T))) :
    ∃ a ∈ ((U T c).comap (embedM T)).map π,
      orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c p.end_color
  let : IsElementaryAbelian 2 (U T c) := IsElementaryAbelian.of_le (DistanceEight.U_le_Z T c)
  let := IsElementaryAbelian.comap_of_injective (p := 2) (embedM T) (embedM_injective T) (U T c)
  let := IsElementaryAbelian.map (p := 2) (A := (U T c).comap (embedM T)) π
  apply even_involution
  rw [CubicAction.permutation_image_card_of_two h e hz hk _ (IsElementaryAbelian.isPGroup 2 _)]
  have hUr : U T c ≤ (embedM T).range := by
    change U T c ≤ Mbar T
    rw [←stabilizer_m_base T]
    exact (DistanceEight.U_le_Z T c).trans (critical_Z_le_stabilizer T (sourceGeometry h)
      (alpha T) rfl (sourceDistance_pos h) p.critical)
  have hr := reverse_critical_moving_image_four_le h e hz hk p hforward
  rw [Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le,
    ←map_comap_eq_self hUr,relIndex_map_map_of_injective _ _ (embedM_injective T)] at hr
  exact hr

include h e hz hk in
/-- The entire natural cover controls the critical radius intersection. -/
theorem critical_radius_moving_commutator_le_Z_of_natural
    (hnat : Nat.card (initialMoved L R) = 16)
    (hb : 2 < sourceDistance h) {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (hcard : 4 ≤ (Q T a').relIndex (Z T a)) :
    ⁅V T a ⊓ Q T (p.walk.getVert (p.walk.length-2)),U T a'⁆ ≤
      Z T a := by
  have hl : 2 < p.walk.length := by rw [p.length_eq_b]; exact hb
  let t := p.walk.getVert (p.walk.length-1)
  have hct : Adjacent T a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1 = p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm T ((cosetGraph_adj T _ _).mp hh)
  have ht : color T t = true := by
    have hh := adjacent_color_ne T hct
    rw [p.end_color] at hh
    cases he : color T t <;> simp_all
  have het : Adjacent T (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1 = p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj T _ _).mp hh
  let Y := V T a ⊓ Q T (p.walk.getVert (p.walk.length-2))
  have hYt : Y ≤ Q T t := inf_le_right.trans (Q_le_adjacent_h T ht het)
  have hY : Y ≤ stabilizer T a' := fun _ hx =>
    (hYt hx).2 _ (adjacent_symm T hct)
  have hcomm : ⁅U T a',Z T a⁆ ≤ ⁅Z T a,Z T a'⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl (DistanceEight.U_le_Z T a')
  have hRZa : ⁅Z T a,Z T a'⁆ ≤ Z T a :=
    (critical_seed_commutator_le h p).trans inf_le_left
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  have hAA : ⁅U T a',Z T a⁆ ≤
      centralizer (Z T a : Set (FreeAmalgam T)) :=
    (hcomm.trans hRZa).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hAY : ⁅U T a',Z T a⁆ ≤
      centralizer (Y : Set (FreeAmalgam T)) :=
    hcomm.trans (le_centralizer_iff.mp (critical_radius_intersection_centralizes h p hb))
  obtain ⟨i,hi,hir,hiQ,_,hiU,_⟩ := graph_cover h e hz hk a' p.end_color
  have hA : Z T a ≤ i.range := by
    rw [hir]
    exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hcontrol : ⁅U T a',Y⁆ ≤ ⁅U T a',Z T a⁆ := by
    rw [←hiU]
    apply embedded_natural_commutator_control h e hz hk hnat i hi (Z T a) Y hA
      (hY.trans_eq hir.symm)
    · rwa [hiQ]
    · rwa [hiU]
    · rwa [hiU]
  rw [commutator_comm]
  exact hcontrol.trans (hcomm.trans hRZa)

/-- A restricted reverse actor preserves the original movement and contains
an even involution in the same marked symmetric quotient. -/
theorem critical_radius_restricted_even_actor
    (hcore : Nat.card (initialMoved L R) = 32) {a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) (alpha T) a')
    (hforward : 4 ≤ (Q T a').relIndex (Z T (alpha T))) :
    ∃ W : Subgroup (FreeAmalgam T), W ≤ U T a' ∧
      ⁅V T (alpha T) ⊓ Q T (p.walk.getVert (p.walk.length-2)),W⁆ ≤
        Z T (alpha T) ∧
      ∃ a ∈ (W.comap (embedM T)).map π,
        orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  have hb := distance_gt_two h e hz hk
  let a := alpha T
  have hl : 2 < p.walk.length := by rw [p.length_eq_b]; exact hb
  let t := p.walk.getVert (p.walk.length-1)
  have hct : Adjacent T a' t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm T ((cosetGraph_adj T _ _).mp hh)
  have ht : color T t = true := by
    have hh := adjacent_color_ne T hct
    rw [p.end_color] at hh
    cases he : color T t <;> simp_all
  have het : Adjacent T (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj T _ _).mp hh
  let Y := V T a ⊓ Q T (p.walk.getVert (p.walk.length-2))
  have hYt : Y ≤ Q T t := inf_le_right.trans (Q_le_adjacent_h T ht het)
  have hY : Y ≤ stabilizer T a' := fun _ hx =>
    (hYt hx).2 _ (adjacent_symm T hct)
  have hcomm : ⁅U T a',U T a⁆ ≤ ⁅Z T a,Z T a'⁆ := by
    rw [commutator_comm]
    exact commutator_mono (DistanceEight.U_le_Z T a) (DistanceEight.U_le_Z T a')
  have hRZa : ⁅Z T a,Z T a'⁆ ≤ Z T a :=
    (critical_seed_commutator_le h p).trans inf_le_left
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  let : IsElementaryAbelian 2 (U T a) := IsElementaryAbelian.of_le (DistanceEight.U_le_Z T a)
  have hAA : ⁅U T a',U T a⁆ ≤
      centralizer (U T a : Set (FreeAmalgam T)) :=
    (hcomm.trans hRZa).trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (show (U T a : Set (FreeAmalgam T)) ⊆ Z T a from DistanceEight.U_le_Z T a)))
  have hAY : ⁅U T a',U T a⁆ ≤ centralizer (Y : Set (FreeAmalgam T)) :=
    hcomm.trans (le_centralizer_iff.mp (critical_radius_intersection_centralizes h p hb))
  obtain ⟨i,hi,hir,hiQ,_,hiU,_⟩ := graph_cover h e hz hk a' p.end_color
  have hA : U T a ≤ i.range := by
    rw [hir]
    exact (DistanceEight.U_le_Z T a).trans (Z_le_stabilizer_of_dist_le a _ p.critical.1.le)
  have hforwardU := critical_forward_moving_image_four_le h e hz hk p hforward
  obtain ⟨W,hW,_,hpres,hcontrol⟩ := embedded_cover_restriction_preserving h e hz hk i hi (U T a) hA
    (hiQ.symm ▸ hforwardU) (hiU.symm ▸ hAA)
  have hWU : W ≤ U T a' := hiU ▸ hW
  have hbound : ⁅Y,W⁆ ≤ Z T a := by
    rw [commutator_comm]
    have hh := hcontrol Y (hY.trans_eq hir.symm) (hiU.symm ▸ hAY)
    rw [hiU] at hh
    exact hh.trans (hcomm.trans hRZa)
  have hUbase : U T a' ≤ (embedM T).range := by
    change U T a' ≤ Mbar T
    rw [←stabilizer_m_base T]
    exact (DistanceEight.U_le_Z T a').trans
      (critical_Z_le_stabilizer T (sourceGeometry h) (alpha T) rfl
        (sourceDistance_pos h) p.critical)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color
  let : IsElementaryAbelian 2 (U T a') := IsElementaryAbelian.of_le (DistanceEight.U_le_Z T a')
  have hqreverse : ⁅U T a,U T a'⁆ ≤
      centralizer (U T a' : Set (FreeAmalgam T)) :=
    ((commutator_mono (DistanceEight.U_le_Z T a) (DistanceEight.U_le_Z T a')).trans
      ((critical_seed_commutator_le h p).trans inf_le_right)).trans
        ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
          (centralizer_le (DistanceEight.U_le_Z T a')))
  have hpresreverse : ⁅U T a,W⁆ = ⁅U T a,U T a'⁆ := by
    rw [commutator_comm,commutator_comm (U T a)]
    exact hiU ▸ hpres
  have hr := reverse_critical_moving_image_four_le h e hz hk p hforward
  have hQbase := Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le
  have hU := (graph_U_map h e hz).symm
  obtain ⟨c,hcW,hc2,hceven⟩ := embedded_preserving_actor_even h e hz hk hcore
    (embedM T) (embedM_injective T) (U T a') W hUbase hWU
    (hQbase ▸ hr) (hU ▸ hqreverse) (hU ▸ hpresreverse)
  exact ⟨W,hWU,hbound,c,hcW,hc2,hceven⟩


/-- A controlled reverse even actor for either central cover, through the
original marked projection. No restriction or parity premise remains. -/
theorem critical_radius_even_actor {c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) (alpha T) c)
    (hforward : 4 ≤ (Q T c).relIndex (Z T (alpha T))) :
    ∃ W : Subgroup (FreeAmalgam T), W ≤ U T c ∧
      ⁅V T (alpha T) ⊓ Q T (p.walk.getVert (p.walk.length-2)),W⁆ ≤
        Z T (alpha T) ∧
      ∃ a ∈ (W.comap (embedM T)).map π,
        orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  rcases moved_card h e hz hk with hnat | hcore
  · obtain ⟨a,ha,ha2,heven⟩ := critical_moving_even_actor h e hz hk p hforward
    exact ⟨U T c,le_rfl,critical_radius_moving_commutator_le_Z_of_natural h e hz hk
      hnat (distance_gt_two h e hz hk) p hforward,a,ha,ha2,heven⟩
  · exact critical_radius_restricted_even_actor h e hz hk hcore p hforward

include h e hz hk in
/-- Radius centrality for the original cubic action, with no remaining
restricted-actor or commutator-control premise. -/
theorem radius_commutator_central :
    ⁅V T (alpha T),Q T (alpha T)⁆ ≤
      centralizer (V T (alpha T) : Set (FreeAmalgam T)) := by
  by_contra hn
  have hb := distance_gt_two h e hz hk
  have hfour := CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.distance_eq_four_of_radius_commutator_not_central
    T (sourceGeometry h) hb rfl hn
  obtain ⟨c,p,hforward⟩ := exists_base_large_critical_path (h := h) hfour hn
  apply hn
  obtain ⟨W,hW,hcomm,a,haW,ha,heven⟩ := critical_radius_even_actor h e hz hk p hforward
  exact critical_radius_central_of_marked_subactor h e hz hk p W
    (hW.trans (DistanceEight.U_le_Z T c)) a ha heven haW hcomm

include h e hz hk in
/-- All three source radius conclusions hold at every component vertex,
with the actual cubic action and whole moving cover retained. -/
theorem radius_bounds_at (a : Vertex T) (ha : color T a = false) (a' c : Vertex T) :
    ⁅V T a,Q T a⁆ ≤ centralizer (V T a : Set (FreeAmalgam T)) ∧
      ⁅V T a,V T a⁆ ≤ X T a ∧
      ⁅⁅X T a' ⊓ Q T a,V T a ⊓ Q T c⁆,V T a ⊓ Q T c⁆ = ⊥ :=
  radius_bounds_at_of_base h (distance_gt_two h e hz hk)
    (radius_commutator_central h e hz hk) a ha a' c

omit hk in
include h e hz in
/-- The whole intrinsic-core alternative now has all radius centrality
premises discharged. Its remaining cubic branch requires terminal exclusion. -/
theorem coreExhaustion_or_cubic_central_radius :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      ∀ a : Vertex T, color T a = false → ∀ a' c : Vertex T,
        ⁅V T a,Q T a⁆ ≤ centralizer (V T a : Set (FreeAmalgam T)) ∧
        ⁅V T a,V T a⁆ ≤ X T a ∧
        ⁅⁅X T a' ⊓ Q T a,V T a ⊓ Q T c⁆,V T a ⊓ Q T c⁆ = ⊥ := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,radius_bounds_at h e hz hk⟩

omit hk in
include h e hz in
/-- The literal C.1.32 application retains only terminal cubic paths after
all radius-control premises have been discharged. -/
theorem rankTwo_or_cubic_central_radius :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      ∀ a : Vertex T, color T a = false → ∀ a' c : Vertex T,
        ⁅V T a,Q T a⁆ ≤ centralizer (V T a : Set (FreeAmalgam T)) ∧
        ⁅V T a,V T a⁆ ≤ X T a ∧
        ⁅⁅X T a' ⊓ Q T a,V T a ⊓ Q T c⁆,V T a ⊓ Q T c⁆ = ⊥ :=
  (coreExhaustion_or_cubic_central_radius h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
