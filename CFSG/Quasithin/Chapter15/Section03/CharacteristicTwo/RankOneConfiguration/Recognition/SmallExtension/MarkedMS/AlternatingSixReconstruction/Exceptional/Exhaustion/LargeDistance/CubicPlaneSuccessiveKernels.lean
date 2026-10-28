module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSuccessiveComparison
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusAlignment
/-!
# Full shifted kernels controlled by the selected midpoint

Retain the critical paths a--v--c--t--z and d--s--a--v--c, the generating
edge cores at a and c, and the actual element of G_a carrying c to d.
Set H = [Z_d intersect Q_c, Z_z intersect Q_a]. The plane core-action bound
puts H in Z_a, while the two edge-action bounds put H in Z_s and Z_t.
The strict backward slice at c identifies Z_a intersect Z_c with Z_v.
Thus H lies in both generating edge-seed intersections and is central in
G_a and G_c. The retained transporter makes it central in G_d as well.
The full-cover fixed-hyperplane theorem now forces H = 1. Consequently
every subgroup of Z_d intersect Q_c moves Z_z only along [Z_a,Z_z].

The outer paired selector supplies the needed midpoint slice and generation
on its retained backward path. Its next comparison therefore needs neither
an escape hypothesis nor an additional slice inequality. The next backward
critical path, its generating edges and its transporter remain explicit.
The terminal exclusion, both core exhaustions and unconditional reconstruction
still require proof. Whole-core and literal C.1.32 applications preserve
the original cubic projection, odd E/Q and both full moving covers.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the center argument in (5.12)(1), printed pp.924--925;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
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
private theorem full_shifted_kernel_noncentral
    (hb4 : sourceDistance h = 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hq : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4) :
    ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆ ≠ ⊥ →
      ¬ ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆ ≤
        centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let t := q.walk.getVert 1
  let F := Z Rg z ⊓ Q Rg a
  let A := Z Rg c
  let D := Z Rg d ⊓ Q Rg c
  let H := ⁅D,F⁆
  let P := F ⊔ A
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb4
  have hdt : Adjacent Rg d t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent Rg a t := by
    rw [←hqa]
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hdt
    rw [q.start_color] at hh
    cases he : color Rg t <;> simp_all
  have hAt : A ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ q.end_color)
    rw [(sourceGeometry h).distance_constant _ q.end_color]
    have hh := q.dist_end 1
    rw [hql] at hh
    change (cosetGraph Rg).dist c t < sourceDistance h
    rw [SimpleGraph.dist_comm,hh,hb4]
    decide
  have hFt : F ≤ Q Rg t := inf_le_right.trans (Q_le_adjacent_h Rg ht hat)
  have hPt : P ≤ Q Rg t := sup_le hFt hAt
  have hfixed : D = Z Rg d ⊓ centralizer (A : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e q).symm
  let qr := CriticalPath.ofPair (geometry := sourceGeometry h) q.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      d q.start_color (by
        rw [(sourceGeometry h).distance_constant d q.start_color]
        exact sourceDistance_pos h) c q.end_color q.critical)
  have hDP : ⁅D,P⁆ = H := by
    have hDA : ⁅D,A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (hfixed ▸ inf_le_right)
    have hFA : F ≤ centralizer (A : Set (FreeAmalgam Rg)) := by
      have hzc : Z Rg z ≤ Q Rg c := by
        apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
        rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,
          p.dist_end,hl]
        exact hb
      exact (inf_le_left.trans hzc).trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q Rg c q.end_color)))
    rw [commutator_comm]
    rw [show P = F ⊔ A from rfl,
      commutator_sup_of_commuting_factors F A D hFA
        ((show D ≤ centralizer (A : Set (FreeAmalgam Rg)) from hfixed ▸ inf_le_right).trans
          (Subgroup.centralizer_le_normalizer _)),commutator_comm F D,
      commutator_comm A D,show ⁅D,F⁆ = H from rfl,hDA,sup_bot_eq]
  intro hne
  change ¬ H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg))
  let := finite_Z Rg d
  let : Finite (U Rg d) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg d)) (inclusion_injective _)
  have hidx : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg d) ≤ 2 :=
    ((relIndex_le_of_le_left
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg c q.end_color))) index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg d) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk q hq).1
  have hn := full_seed_fixed_commutator_noncentral h e hz hk q.start_color hdt
    A P hAt hPt le_sup_right qr.critical.2 hidx
  rw [←hfixed,hDP] at hn
  exact hn hne

include h e hz hk in
/-- The full shifted kernels commute when the retained edge cores generate
at the start and midpoint and the backward midpoint slice is strict.
Every subgroup of the backward kernel moves the endpoint seed only along
the original critical line. Both full covers are included. -/
theorem plane_shifted_kernels_of_midpoint_generation
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (K : Subgroup (FreeAmalgam Rg)) (hK : K ≤ Z Rg d ⊓ Q Rg (p.walk.getVert 2))
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a)
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg a)
    (hgd : act Rg g (p.walk.getVert 2) = d)
    (hmidgen : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a)) :
    ⁅K,Z Rg z ⊓ Q Rg a⁆ = ⊥ ∧ ⁅K,Z Rg z⁆ ≤ ⁅Z Rg a,Z Rg z⁆ := by
  let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb4
  have hda : (cosetGraph Rg).dist d a ≤ 2 := by
    rw [←hqa,q.dist_start (by omega)]
  have hDV : Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≤ V Rg a :=
    inf_le_left.trans (le_iSup_of_le d (le_iSup_of_le hda le_rfl))
  have hHa : H ≤ Z Rg a :=
    (commutator_mono hDV inf_le_right).trans
      (plane_radius_core_commutator h e hz hk u hR p.start_color)
  have hav : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg (p.walk.getVert 3) <;> simp_all
  have hDt : Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≤ Q Rg (p.walk.getVert 3) :=
    inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hHt : H ≤ Z Rg (p.walk.getVert 3) := by
    rw [show H = ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆ from rfl,
      commutator_comm]
    exact (commutator_mono inf_le_left hDt).trans
      (plane_edge_seed_commutator h e hz hk u hR p.end_color hzt)
  have hHc : H ≤ Z Rg (p.walk.getVert 2) := hHt.trans
    (adjacent_Z_le Rg q.end_color hct)
  have hHz : H ≤ Z Rg z := hHt.trans (adjacent_Z_le Rg p.end_color hzt)
  have hHv : H ≤ Z Rg (p.walk.getVert 1) :=
    (le_inf hHa hHc).trans_eq
      (plane_strict_slice_eq_edge h e hz hk u hR q.end_color p.start_color hcv hav hback).2.1
  have has : Adjacent Rg a (q.walk.getVert 1) := by
    have hh := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by
        have hql := q.length_eq_b.trans hb4
        omega)))
    simpa only [hqa] using hh
  have hds : Adjacent Rg d (q.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (by omega)
  have hsc : color Rg (q.walk.getVert 1) = true := by
    have hh := adjacent_color_ne Rg hds
    rw [q.start_color] at hh
    cases he : color Rg (q.walk.getVert 1) <;> simp_all
  have hHs : H ≤ Z Rg (q.walk.getVert 1) :=
    (commutator_mono inf_le_left (inf_le_right.trans (Q_le_adjacent_h Rg hsc has))).trans
      (plane_edge_seed_commutator h e hz hk u hR q.start_color hds)
  have hcA : H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :=
    (le_inf hHs hHv).trans
      ((plane_generating_edge_seed_intersection h e hz hk u hR p.start_color
        has hav hgen).le.trans inf_le_right)
  have hcC : H ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) :=
    (le_inf hHv hHt).trans
      ((plane_generating_edge_seed_intersection h e hz hk u hR q.end_color hcv hct hmidgen).le.trans
        inf_le_right)
  have hm : H.map (MulAut.conj g⁻¹).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp
      ((le_centralizer_iff.mp hcA).trans (Subgroup.centralizer_le_normalizer _)
        ((stabilizer Rg a).inv_mem hg))
  have hcD := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcC).trans
    (map_centralizer_le_centralizer_image _ _)
  change H.map (MulAut.conj g⁻¹).toMonoidHom ≤
    centralizer (((stabilizer Rg (p.walk.getVert 2)).map
      (MulAut.conj g⁻¹).toMonoidHom) : Set (FreeAmalgam Rg)) at hcD
  rw [hm,←stabilizer_act,hgd] at hcD
  have he : H = ⊥ := by
    by_contra hn
    exact full_shifted_kernel_noncentral h e hz hk hb4 p q hqa (hsmall _ _ q) hn hcD
  have hKF : ⁅K,Z Rg z ⊓ Q Rg a⁆ = ⊥ :=
    bot_unique ((commutator_mono hK le_rfl).trans_eq he)
  have hKG : K ≤ stabilizer Rg z :=
    (hK.trans hDt).trans (fun _ hx => hx.2 _ (adjacent_symm Rg hzt))
  exact ⟨hKF,small_critical_kernel_commutator h e hz hk p (hsmall _ _ p) K hKG
    (commutator_eq_bot_iff_le_centralizer.mp hKF)⟩

include h e hz hk in
/-- On the outer selector's same retained backward path, the next shifted
comparison has no escape or additional slice premise. Only the next
backward configuration, generation and transporter remain to be supplied. -/
theorem plane_selected_successive_comparison_from_generation
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
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
              ∀ b (q' : CriticalPath Rg (sourceGeometry h) b (q.walk.getVert 2)),
                q'.walk.getVert 2 = d →
                Q Rg (q'.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d →
                ∀ k ∈ stabilizer Rg d, act Rg k (q.walk.getVert 2) = b →
                ∀ K : Subgroup (FreeAmalgam Rg), K ≤ Z Rg b ⊓ Q Rg (q.walk.getVert 2) →
                  ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg d⁆ = ⊥ ∧
                    ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤ ⁅Z Rg d,Z Rg (v.walk.getVert 2)⁆
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
  refine ⟨t,hat,r,hr,p',hverts,hgen,hpair,g,hg,hgt,?_⟩
  have hl' : p'.walk.length = 4 := p'.length_eq_b.trans hb4
  have cast_end {d v w : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) d v)
      (he : v = w) : ∃ q' : CriticalPath Rg (sourceGeometry h) d w,
        ∀ i, q'.walk.getVert i = q.walk.getVert i := by
    subst w
    exact ⟨q,fun _ => rfl⟩
  have finish {w : Vertex Rg}
      (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2)) (v.walk.getVert 2))
      (hq1 : q.walk.getVert 1 = t)
      (hqv : ∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i)
      (hgenq : Q Rg t ⊔ Q Rg (v.walk.getVert 1) = stabilizer Rg (alpha Rg))
      (b : Vertex Rg) (q' : CriticalPath Rg (sourceGeometry h) b (q.walk.getVert 2))
      (hq'd : q'.walk.getVert 2 = act Rg g (p.walk.getVert 2))
      (hgg : Q Rg (q'.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 1) =
        stabilizer Rg (act Rg g (p.walk.getVert 2)))
      (k : FreeAmalgam Rg) (hkG : k ∈ stabilizer Rg (act Rg g (p.walk.getVert 2)))
      (hkb : act Rg k (q.walk.getVert 2) = b)
      (K : Subgroup (FreeAmalgam Rg)) (hK : K ≤ Z Rg b ⊓ Q Rg (q.walk.getVert 2)) :
      ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg (act Rg g (p.walk.getVert 2))⁆ = ⊥ ∧
        ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤
          ⁅Z Rg (act Rg g (p.walk.getVert 2)),Z Rg (v.walk.getVert 2)⁆ := by
    have hqa : q.walk.getVert 2 = alpha Rg := by
      simpa only [SimpleGraph.Walk.getVert_zero] using hqv 0 (by omega)
    apply plane_shifted_kernels_of_midpoint_generation h e hz hk u hR hb4 hsmall
      q q' hq'd K hK hgg k hkG hkb
    · rw [hqa,hq1,hqv 1 (by omega)]
      exact hgenq
    · simpa only [hqa] using hstrict
  rcases halt with ⟨q,hq1,hqv⟩ | ⟨q,hq1,hqv⟩
  · obtain ⟨q',hq'⟩ := cast_end q (show p.walk.getVert (p.walk.length-2) =
        p.walk.getVert 2 by rw [hl])
    have hqv' : ∀ i ≤ 2, q'.walk.getVert (i+2) = p.walk.getVert i :=
      fun i hi => (hq' (i+2)).trans (hqv i (by omega))
    have hq1' := (hq' 1).trans hq1
    exact Or.inl ⟨q',hq1',hqv',finish p q' hq1' hqv' hfirst⟩
  · obtain ⟨q',hq'⟩ := cast_end q (show p'.walk.getVert (p'.walk.length-2) =
        p'.walk.getVert 2 by rw [hl'])
    have hqv' : ∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i :=
      fun i hi => (hq' (i+2)).trans (hqv i (by omega))
    have hq1' := (hq' 1).trans hq1
    exact Or.inr ⟨q',hq1',hqv',finish p' q' hq1' hqv' (by rwa [hQfirst])⟩

omit hk in
include h e hz in
/-- The original whole-core reduction supplies the outer selection and its
midpoint conditions for the next comparison, on both full moving covers. -/
theorem coreExhaustion_or_cubic_successive_midpoint_comparison :
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
                  ∀ b (q' : CriticalPath Rg (sourceGeometry h) b (q.walk.getVert 2)),
                    q'.walk.getVert 2 = d →
                    Q Rg (q'.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d →
                    ∀ k ∈ stabilizer Rg d, act Rg k (q.walk.getVert 2) = b →
                    ∀ K : Subgroup (FreeAmalgam Rg), K ≤ Z Rg b ⊓ Q Rg (q.walk.getVert 2) →
                      ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg d⁆ = ⊥ ∧
                        ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤ ⁅Z Rg d,Z Rg (v.walk.getVert 2)⁆
              comparison z p ∨ comparison (act Rg x z) p')) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    intro hb4 hsmall z p hstrict
    exact plane_selected_successive_comparison_from_generation h e hz hk u hplane hb4 hsmall p hstrict

omit hk in
include h e hz in
/-- Literal C.1.32 application of the successive comparison, with the
original projection, radical, full attachments and both covers retained. -/
theorem rankTwo_or_cubic_successive_midpoint_comparison :
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
                  ∀ b (q' : CriticalPath Rg (sourceGeometry h) b (q.walk.getVert 2)),
                    q'.walk.getVert 2 = d →
                    Q Rg (q'.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d →
                    ∀ k ∈ stabilizer Rg d, act Rg k (q.walk.getVert 2) = b →
                    ∀ K : Subgroup (FreeAmalgam Rg), K ≤ Z Rg b ⊓ Q Rg (q.walk.getVert 2) →
                      ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg d⁆ = ⊥ ∧
                        ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤ ⁅Z Rg d,Z Rg (v.walk.getVert 2)⁆
              comparison z p ∨ comparison (act Rg x z) p')) :=
  (coreExhaustion_or_cubic_successive_midpoint_comparison h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
