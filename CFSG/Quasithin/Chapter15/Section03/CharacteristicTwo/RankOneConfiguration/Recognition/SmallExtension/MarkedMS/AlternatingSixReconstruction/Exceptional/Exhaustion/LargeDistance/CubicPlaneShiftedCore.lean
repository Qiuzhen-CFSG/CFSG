module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedAttachment
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneBackward

/-!
# Backward-core movement of the actual endpoint attachment

Retain the overlapping critical paths a--v--c--t--z and d--s--a--v--c,
strict forward and backward Baumann slices, and the generating edge cores
at a. A failed shifted comparison already forces an order-two central
attachment C in U_z. The backward strict slice gives Z_d intersect Z_a = Z_s.
Since C lies in Z_a and is disjoint from Z_s, it is disjoint from Z_d.
On the other hand C lies in Z_c and centralizes Z_d, so the literal critical
seed-centralizer equality places it in Q_d. Full omega at d equals Z_d;
hence Q_d must move C. This commutator lies in U_a intersect Z_s and is
centralized by Q_d. In particular Q_d does not normalize C.

The actual paired selector supplies the backward strict slice on either
retained branch. Its application keeps the same walks and both generation
equations. The whole-core and C.1.32 consumers retain the original cubic
projection with kernel E, its odd quotient E/Q, both moving-cover alternatives,
and the original radical without a Sylow assumption. This controls the
backward core's action; the terminal contradiction is still required.

The internal imports reuse the edge commutator bound and selector transport
without changing their public interfaces.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the shifted comparison and center analysis in (5.12)(1), printed
pp.924--925; Aschbacher--Smith C.1.31--32, printed pp.135--136.
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
/-- The strict backward slice places the endpoint attachment in the backward
two-core, outside its omega-center. Its nontrivial commutator is central
in that core and lies in the original starting moving subgroup. -/
theorem plane_shifted_failure_attachment_core
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
      (U Rg (p.walk.getVert 2)))
    (hd : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) :
    let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
    Nat.card (U Rg z) = 32 ∧ Nat.card C = 2 ∧
      C ≤ Q Rg d ∧ C ⊓ Z Rg d = ⊥ ∧
      ⁅C,Q Rg d⁆ ≠ ⊥ ∧ ⁅C,Q Rg d⁆ ≤ U Rg a ⊓ Z Rg (q.walk.getVert 1) ∧
      ⁅⁅C,Q Rg d⁆,Q Rg d⁆ = ⊥ ∧
      ¬ Q Rg d ≤ normalizer (C : Set (FreeAmalgam Rg)) := by
  let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  obtain ⟨hn,hcard,_,_,hCv,_,_,_,hmoveS,hCdis,_⟩ :=
    plane_shifted_failure_attachment h e hz hk u hR hb4 hsmall p q hqa
      hescape K hK hfail hgen hs
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb4
  have hav : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hds : Adjacent Rg d (q.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (by omega)
  have has : Adjacent Rg a (q.walk.getVert 1) := by
    have hh := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
    simpa only [hqa] using hh
  have hCa : C ≤ Z Rg a := hCv.trans (adjacent_Z_le Rg p.start_color hav)
  have hCc : C ≤ Z Rg (p.walk.getVert 2) :=
    hCv.trans (adjacent_Z_le Rg q.end_color hcv)
  have hslice := (plane_strict_slice_eq_edge h e hz hk u hR
    p.start_color q.start_color has hds hd).2.1
  have hCdisD : C ⊓ Z Rg d = ⊥ := by
    apply bot_unique
    calc
      C ⊓ Z Rg d ≤ C ⊓ (Z Rg d ⊓ Z Rg a) :=
        le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hCa))
      _ = ⊥ := by rw [hslice,hCdis]
  have hZdQa : Z Rg d ≤ Q Rg a := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ q.start_color)
    have hda : (cosetGraph Rg).dist d a = 2 := by
      have hh : (cosetGraph Rg).dist d (q.walk.getVert 2) = 2 := q.dist_start (by omega)
      simpa only [hqa] using hh
    rw [hda,(sourceGeometry h).distance_constant _ q.start_color]
    exact distance_gt_two h e hz hk
  have hCfix : C ≤ centralizer (Z Rg d : Set (FreeAmalgam Rg)) :=
    (hCa.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a p.start_color))).trans (centralizer_le hZdQa)
  have hCQd : C ≤ Q Rg d := by
    have hh := le_inf hCc hCfix
    rw [critical_seed_centralizer_intersection h e
      (CriticalPath.ofPair q.end_color (reverse_pair h e q))] at hh
    exact hh.trans inf_le_right
  have hne : ⁅C,Q Rg d⁆ ≠ ⊥ := by
    intro he
    have hCZd : C ≤ Z Rg d := by
      rw [←(plane_small_four_omega_generated h e hz hk u hR hb4 hsmall d q.start_color).2]
      have hZX := (sourceGeometry h).omega_bound a p.start_color (by
        rw [(sourceGeometry h).distance_constant _ p.start_color]
        exact sourceDistance_pos h)
      intro x hx
      exact mem_omegaCenter_iff.mpr ⟨hCQd hx,
        (mem_omegaCenter_iff.mp (hZX (hCa hx))).2.1,
        (commutator_eq_bot_iff_le_centralizer.mp he) hx⟩
    have hb : C = ⊥ := by simpa only [inf_eq_left.mpr hCZd] using hCdisD
    have hc : Nat.card C = 2 := hcard
    rw [hb,Subgroup.card_bot] at hc
    omega
  have hsc : color Rg (q.walk.getVert 1) = true := by
    have hh := adjacent_color_ne Rg hds
    rw [q.start_color] at hh
    cases he : color Rg (q.walk.getVert 1) <;> simp_all
  have hQds := Q_le_adjacent_h Rg hsc hds
  have hmove : ⁅C,Q Rg d⁆ ≤ U Rg a ⊓ Z Rg (q.walk.getVert 1) :=
    le_inf ((commutator_mono hCa hQds).trans
      (full_seed_edge_commutator_le_moving h e hz p.start_color has))
      ((commutator_mono le_rfl hQds).trans hmoveS)
  have hquad : ⁅⁅C,Q Rg d⁆,Q Rg d⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (hmove.trans (inf_le_right.trans (adjacent_Z_le Rg q.start_color hds))).trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg d q.start_color))
  refine ⟨hn,hcard,hCQd,hCdisD,hne,hmove,hquad,?_⟩
  intro hnorm
  exact hne (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (hnorm.trans (normalizer_le_centralizer_of_card_two C hcard))))


include h e hz hk in
/-- The original paired selector retains both generation equations and the
same paths. Its backward slice places the actual endpoint attachment in the
backward two-core and forces that core to move it. -/
theorem plane_selected_strict_forward_attachment_core
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hescape : ¬ ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg (alpha Rg))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
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
                (¬ ⁅K,Z Rg w⁆ ≤ ⁅K,Z Rg w ⊓ Q Rg (alpha Rg)⁆ ⊔ ⁅Z Rg (alpha Rg),Z Rg w⁆) →
                let C := U Rg w ⊓ centralizer (stabilizer Rg w : Set (FreeAmalgam Rg))
                Nat.card (U Rg w) = 32 ∧ Nat.card C = 2 ∧
                  C ≤ Q Rg d ∧ C ⊓ Z Rg d = ⊥ ∧
                  ⁅C,Q Rg d⁆ ≠ ⊥ ∧ ⁅C,Q Rg d⁆ ≤ U Rg (alpha Rg) ⊓ Z Rg (q.walk.getVert 1) ∧
                  ⁅⁅C,Q Rg d⁆,Q Rg d⁆ = ⊥ ∧
                  ¬ Q Rg d ≤ normalizer (C : Set (FreeAmalgam Rg))
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
    intro K hK hfail
    apply plane_shifted_failure_attachment_core h e hz hk u hR hb4 hsmall
      p q' (by simpa only [SimpleGraph.Walk.getVert_zero] using hqv' 0 (by omega))
      hescape K hK hfail
    · rw [hq1']
      exact hfirst
    · exact hs
    · exact hstrict
  · obtain ⟨q',hq'⟩ := cast_end q (show p'.walk.getVert (p'.walk.length-2) =
        p'.walk.getVert 2 by rw [hl'])
    have hqv' : ∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i :=
      fun i hi => (hq' (i+2)).trans (hqv i (by omega))
    have hq1' := (hq' 1).trans hq1
    refine Or.inr ⟨q',hq1',hqv',?_⟩
    intro K hK hfail
    apply plane_shifted_failure_attachment_core h e hz hk u hR hb4 hsmall
      p' q' (by simpa only [SimpleGraph.Walk.getVert_zero] using hqv' 0 (by omega))
      hescape' K hK hfail
    · rw [hq1',hQfirst]
      exact hfirst
    · exact hs'
    · exact hstrict

omit hk in
include h e hz in
/-- Whole-core application on the actual selected paths, with no additional
backward-slice premise. The original cubic projection and both covers remain. -/
theorem coreExhaustion_or_cubic_shifted_attachment_core :
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
          ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            (¬ ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg (alpha Rg)) →
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) →
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
                    (¬ ⁅K,Z Rg w⁆ ≤ ⁅K,Z Rg w ⊓ Q Rg (alpha Rg)⁆ ⊔ ⁅Z Rg (alpha Rg),Z Rg w⁆) →
                    let C := U Rg w ⊓ centralizer (stabilizer Rg w : Set (FreeAmalgam Rg))
                    Nat.card (U Rg w) = 32 ∧ Nat.card C = 2 ∧
                      C ≤ Q Rg d ∧ C ⊓ Z Rg d = ⊥ ∧
                      ⁅C,Q Rg d⁆ ≠ ⊥ ∧ ⁅C,Q Rg d⁆ ≤ U Rg (alpha Rg) ⊓ Z Rg (q.walk.getVert 1) ∧
                      ⁅⁅C,Q Rg d⁆,Q Rg d⁆ = ⊥ ∧
                      ¬ Q Rg d ≤ normalizer (C : Set (FreeAmalgam Rg))
              comparison z p ∨ comparison (act Rg x z) p')) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    intro hb4 hsmall z p hescape hstrict
    exact plane_selected_strict_forward_attachment_core h e hz hk u hplane hb4 hsmall
      p hescape hstrict

omit hk in
include h e hz in
/-- Literal C.1.32 application of backward-core movement on the same selected
paths, retaining the full central attachment and the proper odd-index radical. -/
theorem rankTwo_or_cubic_shifted_attachment_core :
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
          ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            (¬ ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg (alpha Rg)) →
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) →
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
                    (¬ ⁅K,Z Rg w⁆ ≤ ⁅K,Z Rg w ⊓ Q Rg (alpha Rg)⁆ ⊔ ⁅Z Rg (alpha Rg),Z Rg w⁆) →
                    let C := U Rg w ⊓ centralizer (stabilizer Rg w : Set (FreeAmalgam Rg))
                    Nat.card (U Rg w) = 32 ∧ Nat.card C = 2 ∧
                      C ≤ Q Rg d ∧ C ⊓ Z Rg d = ⊥ ∧
                      ⁅C,Q Rg d⁆ ≠ ⊥ ∧ ⁅C,Q Rg d⁆ ≤ U Rg (alpha Rg) ⊓ Z Rg (q.walk.getVert 1) ∧
                      ⁅⁅C,Q Rg d⁆,Q Rg d⁆ = ⊥ ∧
                      ¬ Q Rg d ≤ normalizer (C : Set (FreeAmalgam Rg))
              comparison z p ∨ comparison (act Rg x z) p')) :=
  (coreExhaustion_or_cubic_shifted_attachment_core h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
