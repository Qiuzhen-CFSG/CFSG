module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSubactorGeneration
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration

/-!
# Shifted full-seed slices in the original cubic plane graph

Consider two critical paths a--z and a--z' sharing their first edge and
midpoint c, together with an earlier critical path d--c through a. At
critical distance four, the kernel K = Z_d intersect Q_c lies in both V_a
and G_z. The full-omega control alternative at z then puts [K,X_z] in Z_a:
the critical line lies there, and plane-edge control puts the reverse-kernel
term there too. This uses no small-slice assumption and retains all of Z_d.

Suppose the earlier first edge and the shared forward first edge generate
G_a, and the joint endpoint image has order greater than two. The proved
large-subactor theorem gives generation by the earlier edge and Z_z join
Z_z'. First-edge normality on d--c and the two full-omega estimates make
K join Z_a normal in G_a. The actual cubic normal-section theorem puts K
in B_a. The full critical index and predecessor-slice theorem now identify
Z_d intersect B_a with K and give index exactly two, for both Z_d and U_d.
All statements hold at every original component vertex.

The remaining alternative is central generation of full omega at every
component vertex; only in that alternative is X identified with Z. The
simultaneous critical-path placements, their generating edges, their small
individual images and large joint image remain explicit. The source's
centrally generated case, construction of this configuration from the
original selector, both actual end-slice bounds, larger-distance and Borel
exclusions, and both core exhaustions remain necessary. This does not assert
unconditional MS93 (5.12)(3) or the final reconstruction.

The whole-core and literal C.1.32 applications preserve the projection with
kernel E, its nontrivial odd quotient E/Q, the specified nonsylow radical,
and both full moving covers of orders sixteen and thirty-two. The internal
import reuses only the already proved omega-generation covariance.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii) and (5.12)(1),(3), printed pp.866--867,924--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- The noncentral full-omega alternative controls the full earlier seed kernel,
without a Baumann-slice hypothesis. -/
theorem plane_shifted_kernel_control_or_omega
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {a z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4) :
    (X Rg z = U Rg z ⊔
      (X Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) ∨
    ⁅Z Rg d ⊓ Q Rg c,X Rg z⁆ ≤ Z Rg a := by
  let pr : CriticalPath Rg (sourceGeometry h) z a :=
    CriticalPath.ofPair p.end_color (reverse_pair h e p)
  have hpr : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk p hp).2]
    decide
  rcases small_critical_omega_generation_or_control_at h e hz hk pr hpr with hgen | hcontrol
  · exact Or.inl hgen
  right
  let Y := Z Rg d ⊓ Q Rg c
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb4
  have hda : (cosetGraph Rg).dist d a ≤ 2 := by
    rw [←hqa,q.dist_start (by omega)]
  have hYV : Y ≤ V Rg a := inf_le_left.trans
    (le_iSup_of_le d (le_iSup_of_le hda le_rfl))
  have hYQ : Y ≤ Q Rg a := hYV.trans
    ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a p.start_color)
  have hYG : Y ≤ stabilizer Rg z := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two c z q.end_color p.end_color (by
      rw [←hpc,p.dist_end,hl]))
  have hRZ : ⁅X Rg z,Z Rg a⁆ ≤ Z Rg a :=
    le_normalizer_iff_commutator_le_right.mp
      ((critical_X_le_vertex h e z p.end_color a pr.critical).trans (Z_normalized Rg a))
  have hZaX : Z Rg a ≤ X Rg a := (sourceGeometry h).omega_bound a p.start_color (by
    rw [(sourceGeometry h).distance_constant _ p.start_color]
    exact sourceDistance_pos h)
  have hYR : Y ≤ centralizer ((⁅X Rg z,Z Rg a⁆ : Subgroup (FreeAmalgam Rg)) :
      Set (FreeAmalgam Rg)) :=
    (hYQ.trans (Q_le_centralizer_X Rg a)).trans (centralizer_le (hRZ.trans hZaX))
  exact (hcontrol Y hYG hYR).trans (sup_le hRZ
    ((commutator_mono hYV inf_le_right).trans
      (plane_radius_core_commutator h e hz hk u hR p.start_color)))

include h e hz in
private theorem shifted_normalized_radius_le_slice
    (hb : 2 < sourceDistance h) {a z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (N : Subgroup (FreeAmalgam Rg)) (hNV : N ≤ V Rg a)
    (hNn : stabilizer Rg a ≤ normalizer (N : Set (FreeAmalgam Rg)))
    (hm : ⁅N,Z Rg z⁆ ≤ Z Rg a) :
    N ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color Rg p.start_color
  have hback : act Rg g⁻¹ a = alpha Rg := by
    rw [hga]
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  let f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  have hNp : N.map f ≤ V Rg (act Rg g⁻¹ a) := by
    rw [V_act]
    exact map_mono hNV
  have hn : stabilizer Rg (act Rg g⁻¹ a) ≤ normalizer (N.map f : Set (FreeAmalgam Rg)) := by
    rw [stabilizer_act,←map_normalizer_eq_of_bijective N (MulAut.conj (g⁻¹)⁻¹).bijective]
    exact map_mono hNn
  have hm' : ⁅N.map f,Z Rg (act Rg g⁻¹ z)⁆ ≤ Z Rg (act Rg g⁻¹ a) := by
    rw [Z_act,Z_act,←map_commutator]
    exact map_mono hm
  have q : Nonempty (CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg g⁻¹ z)) := by
    rw [←hback]
    exact ⟨p.act g⁻¹⟩
  obtain ⟨q⟩ := q
  rw [hback] at hNp hn hm'
  have hs := normalized_radius_le_slice_of_critical_commutator h e hz hb q (N.map f) hNp hn hm'
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) hb g⁻¹ a p.start_color
  rw [hback] at hB
  rw [hB] at hs
  exact (map_le_map_iff_of_injective (MulAut.conj (g⁻¹)⁻¹).injective).mp hs

include h e hz hk in
/-- Paired shifted endpoints give the actual earlier Baumann slice unless
full omega is centrally generated. The first-edge kernel normality is proved,
and large-subactor generation supplies the whole stabilizer. -/
theorem plane_shifted_small_slice_or_omega
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {a z z' c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (p' : CriticalPath Rg (sourceGeometry h) a z')
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hpc' : p'.walk.getVert 2 = c)
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hp' : (Q Rg z').relIndex (Z Rg a) < 4)
    (hq : (Q Rg c).relIndex (Z Rg d) < 4)
    (hfirst : p'.walk.getVert 1 = p.walk.getVert 1)
    (hpair : Q Rg (q.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 1) =
      stabilizer Rg a)
    (hlarge : 2 < (Q Rg a).relIndex (Z Rg z ⊔ Z Rg z')) :
    (∀ v : Vertex Rg, color Rg v = false →
      (X Rg v = U Rg v ⊔
        (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
      X Rg v = Z Rg v) ∨
    (stabilizer Rg a ≤ normalizer
        ((Z Rg d ⊓ Q Rg c ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      Z Rg d ⊓ B Rg a ((sourceGeometry h).Z_normal _) = Z Rg d ⊓ Q Rg c ∧
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) = 2 ∧
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) = 2) := by
  have finish (w : Vertex Rg) (hw : color Rg w = false)
      (hc : X Rg w = U Rg w ⊔
        (X Rg w ⊓ centralizer (stabilizer Rg w : Set (FreeAmalgam Rg)))) :
      ∀ v : Vertex Rg, color Rg v = false →
        (X Rg v = U Rg v ⊔
          (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
        X Rg v = Z Rg v := by
    intro v hv
    have hh := omega_generation_transport hw hv hc
    exact ⟨hh,omega_eq_seed_of_central_generation h v hv hh⟩
  rcases plane_shifted_kernel_control_or_omega h e hz hk u hR hb4 p q hpc hqa hp with hc | hmove
  · exact Or.inl (finish z p.end_color hc)
  rcases plane_shifted_kernel_control_or_omega h e hz hk u hR hb4 p' q hpc' hqa hp' with hc | hmove'
  · exact Or.inl (finish z' p'.end_color hc)
  right
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hl' : p'.walk.length = 4 := p'.length_eq_b.trans hb4
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb4
  let K := Z Rg d ⊓ Q Rg c
  let N := K ⊔ Z Rg a
  let A := Z Rg z ⊔ Z Rg z'
  let s := q.walk.getVert 1
  let t := p.walk.getVert 1
  have has : Adjacent Rg a s := by
    rw [←hqa]
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have hat : Adjacent Rg a t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have endpoint_le {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) a w)
      (hrt : r.walk.getVert 1 = t) : Z Rg w ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg w ((sourceGeometry h).exists_critical w r.end_color)
    rw [←hrt,SimpleGraph.dist_comm,r.dist_end,
      (sourceGeometry h).distance_constant w r.end_color]
    have hh : r.walk.length = sourceDistance h := r.length_eq_b
    change r.walk.length-1 < sourceDistance h
    omega
  have hgen : Q Rg s ⊔ A = stabilizer Rg a :=
    plane_edge_pair_large_subactor_generates h e hz hk u hR p.start_color has hat hpair A
      (sup_le (endpoint_le p rfl) (endpoint_le p' hfirst)) hlarge
  have hda : (cosetGraph Rg).dist d a ≤ 2 := by
    rw [←hqa,q.dist_start (by omega)]
  have hKV : K ≤ V Rg a := inf_le_left.trans
    (le_iSup_of_le d (le_iSup_of_le hda le_rfl))
  have hNV : N ≤ V Rg a := sup_le hKV (Z_le_VBall Rg _ 2)
  have hNG : N ≤ stabilizer Rg a :=
    hNV.trans ((sourceGeometry h).V_local _ p.start_color (by
      rw [(sourceGeometry h).distance_constant _ p.start_color]; exact hb))
  have hKN : Q Rg s ≤ normalizer (K : Set (FreeAmalgam Rg)) :=
    plane_small_critical_first_edge_normalizes_kernel h e hz hk u hR q hq
  have hNs : Q Rg s ≤ normalizer (N : Set (FreeAmalgam Rg)) :=
    (le_inf hKN ((show Q Rg s ≤ stabilizer Rg a from
      fun _ hx => hx.2 _ (adjacent_symm Rg has)).trans (Z_normalized Rg _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have move {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) a w)
      (hm : ⁅K,X Rg w⁆ ≤ Z Rg a) :
      ⁅N,Z Rg w⁆ ≤ Z Rg a := by
    have hZX : Z Rg w ≤ X Rg w := (sourceGeometry h).omega_bound w r.end_color (by
      rw [(sourceGeometry h).distance_constant _ r.end_color]
      exact sourceDistance_pos h)
    apply commutator_sup_le_of_relative_normal (stabilizer Rg a)
      K (Z Rg a) (Z Rg w) (Z Rg a) (Z_normalized Rg _)
      (le_sup_left.trans hNG) (Z_le_stabilizer Rg _)
      ((commutator_mono le_rfl hZX).trans hm)
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
        (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h) r.critical).trans (Z_normalized Rg _))
  have hpN := move p hmove
  have hpN' := move p' hmove'
  have hNn : stabilizer Rg a ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le hNs (sup_le
      (le_normalizer_iff_commutator_le_left.mpr (hpN.trans le_sup_right))
      (le_normalizer_iff_commutator_le_left.mpr (hpN'.trans le_sup_right)))
  have hKB : K ≤ B Rg a ((sourceGeometry h).Z_normal _) :=
    le_sup_left.trans (shifted_normalized_radius_le_slice h e hz hb p N hNV hNn hpN)
  let := finite_Z Rg d
  let : Finite (U Rg d) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg d)) (inclusion_injective _)
  have hindex : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ≤ 2 := by
    have hi := relIndex_le_of_le_left hKB
      (index_ne_zero_of_finite (H := K.subgroupOf (Z Rg d)))
    change (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) ≤
      (Z Rg d ⊓ Q Rg c).relIndex (Z Rg d) at hi
    rw [inf_relIndex_left,(small_critical_indices h e hz hk q hq).1] at hi
    exact (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg d) index_ne_zero_of_finite).trans hi
  let qr : CriticalPath Rg (sourceGeometry h) c d :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],reverse_pair h e q⟩
  have hqra : qr.walk.getVert (qr.walk.length-2) = a := by
    change q.walk.reverse.getVert (q.walk.reverse.length-2) = a
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,hql]
    exact hqa
  have hslice := critical_predecessor_small_slice h e hz hk hb qr
    (by simpa only [hqra] using hindex)
  have heq : Z Rg d ⊓ B Rg a ((sourceGeometry h).Z_normal _) = Z Rg d ⊓ Q Rg c := by
    simpa only [hqra] using hslice.1
  have hfull : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) = 2 := by
    rw [←inf_relIndex_left,heq,inf_relIndex_left,(small_critical_indices h e hz hk q hq).1]
  have hlo := critical_start_slice_index_two_le h e hz hb q
  rw [hqa] at hlo
  exact ⟨hNn,heq,hfull,Nat.le_antisymm hindex hlo⟩

omit hk in
include h e hz in
/-- Whole-core application of shifted slice normality and the exact full-seed
index. The centrally generated omega case and the actual path premises remain. -/
theorem coreExhaustion_or_cubic_plane_shifted_slices :
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
        (sourceDistance h = 4 → ∀ a z z' c d : Vertex Rg,
          ∀ (p : CriticalPath Rg (sourceGeometry h) a z)
            (p' : CriticalPath Rg (sourceGeometry h) a z')
            (q : CriticalPath Rg (sourceGeometry h) d c),
          p.walk.getVert 2 = c → p'.walk.getVert 2 = c → q.walk.getVert 2 = a →
          (Q Rg z).relIndex (Z Rg a) < 4 →
          (Q Rg z').relIndex (Z Rg a) < 4 →
          (Q Rg c).relIndex (Z Rg d) < 4 →
          p'.walk.getVert 1 = p.walk.getVert 1 →
          Q Rg (q.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a →
          2 < (Q Rg a).relIndex (Z Rg z ⊔ Z Rg z') →
          (∀ v : Vertex Rg, color Rg v = false →
            (X Rg v = U Rg v ⊔
              (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
            X Rg v = Z Rg v) ∨
          (stabilizer Rg a ≤ normalizer
              ((Z Rg d ⊓ Q Rg c ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
            Z Rg d ⊓ B Rg a ((sourceGeometry h).Z_normal _) = Z Rg d ⊓ Q Rg c ∧
            (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) = 2 ∧
            (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) = 2))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 _ _ _ _ _ p p' q hpc hpc' hqa hp hp' hq hfirst hpair hlarge =>
        plane_shifted_small_slice_or_omega h e hz hk u hplane hb4 p p' q
          hpc hpc' hqa hp hp' hq hfirst hpair hlarge⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 consumer, with both covers and the actual cubic projection. -/
theorem rankTwo_or_cubic_plane_shifted_slices :
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
        (sourceDistance h = 4 → ∀ a z z' c d : Vertex Rg,
          ∀ (p : CriticalPath Rg (sourceGeometry h) a z)
            (p' : CriticalPath Rg (sourceGeometry h) a z')
            (q : CriticalPath Rg (sourceGeometry h) d c),
          p.walk.getVert 2 = c → p'.walk.getVert 2 = c → q.walk.getVert 2 = a →
          (Q Rg z).relIndex (Z Rg a) < 4 →
          (Q Rg z').relIndex (Z Rg a) < 4 →
          (Q Rg c).relIndex (Z Rg d) < 4 →
          p'.walk.getVert 1 = p.walk.getVert 1 →
          Q Rg (q.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a →
          2 < (Q Rg a).relIndex (Z Rg z ⊔ Z Rg z') →
          (∀ v : Vertex Rg, color Rg v = false →
            (X Rg v = U Rg v ⊔
              (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
            X Rg v = Z Rg v) ∨
          (stabilizer Rg a ≤ normalizer
              ((Z Rg d ⊓ Q Rg c ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
            Z Rg d ⊓ B Rg a ((sourceGeometry h).Z_normal _) = Z Rg d ⊓ Q Rg c ∧
            (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) = 2 ∧
            (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) = 2))) :=
  (coreExhaustion_or_cubic_plane_shifted_slices h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
