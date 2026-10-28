module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicAttachmentMovement
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallRadius

/-!
# Full midpoint cores on the original cubic critical paths

In the point-core branch, the whole midpoint two-core has image of order
four or eight at each critical endpoint. The original full midpoint radius
has image two. If the core image also had order two, the critical seed and
the common core would supplement the midpoint core. Both centralize the
reverse critical kernel, contradicting its nonzero core commutator. The
upper bound comes from the literal oriented edge: its quotient by either
component core has order eight, and that core is normal in the edge group.
Only the proved two-subgroup index comparison is used at the cubic
projection; its kernel remains E, with nontrivial E/Q.

The radius joined to either endpoint core cannot contain the midpoint
core, since both factors centralize the corresponding reverse kernel.
Reversing the same backward path also proves that the nonzero shifted
kernel line is noncentral at the backward endpoint. The whole-core and
literal C.1.32 applications retain the original strict paths, generating
edge, both commutator identities, full augmentation cover and moving
central attachment. They do not assert centrality in the whole midpoint
stabilizer or the remaining full-X control inequality.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the whole-core comparisons in (5.12), printed pp.924--927;
Aschbacher--Smith C.1.31--32, pp.135--136. The lower-bound idea also occurs
in Natural.Exhaustion.LargeDistance.SectionFive.AttachmentMovement; here
all comparisons use the original cubic graph and its literal cores.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- A nonzero reverse-kernel commutator excludes a whole midpoint core
image of order at most two, without identifying the cubic kernel with Q. -/
theorem four_midpoint_core_large_of_kernel_nonzero
    (hb : sourceDistance h = 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hs : (Q Rg z).relIndex (Z Rg a) < 4)
    (hne : ⁅Z Rg z ⊓ Q Rg a,Q Rg (p.walk.getVert 2)⁆ ≠ ⊥) :
    2 < (Q Rg z).relIndex (Q Rg (p.walk.getVert 2)) := by
  by_contra! hsmall
  let c := p.walk.getVert 2
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hZa : Z Rg a ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg a ((sourceGeometry h).exists_critical a p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    change 2 < sourceDistance h
    omega
  let := finite_stabilizer Rg c
  let : Finite (Q Rg c) := Finite.of_injective
    (inclusion (show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1)) (inclusion_injective _)
  change (Q Rg z).relIndex (Q Rg c) ≤ 2 at hsmall
  have hindex : (Q Rg z).relIndex (Q Rg c) = 2 := by
    have hh := relIndex_le_of_le_right hZa
      (index_ne_zero_of_finite (H := (Q Rg z).subgroupOf (Q Rg c)))
    rw [(small_critical_indices h e hz hk p hs).1] at hh
    omega
  have hsupp := index_two_supplement (Z Rg a) (Q Rg z) (Q Rg c) hZa hindex p.critical.2
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  rw [←hsupp]
  apply sup_le
  · exact (inf_le_right.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg z p.end_color)))).trans
        (centralizer_le inf_le_left)
  · exact (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a p.start_color)).trans (centralizer_le inf_le_right)

include h e hz hk in
private theorem point_edge_core_index_eight
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t) :
    (Q Rg c).relIndex (Q Rg t) = 8 := by
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common Rg c t).mp hct
  · rcases hg with ⟨rfl,rfl⟩
    have hm : Q Rg (mVertex Rg g) = (Q Rg (alpha Rg)).map (MulAut.conj g⁻¹).toMonoidHom := by
      simpa only [alpha,act_mVertex,one_mul] using Q_act Rg g (alpha Rg)
    have ht : Q Rg (hVertex Rg g) = (Q Rg (beta Rg)).map (MulAut.conj g⁻¹).toMonoidHom := by
      simpa only [beta,act_hVertex,one_mul] using Q_act Rg g (beta Rg)
    rw [hm,ht,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective,
      Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le,Q_beta,
      relIndex_map_map_of_injective _ _ (embedM_injective Rg),
      ←CubicAction.permutation_image_card_of_two h e hz hk Rg h.relative_radical.isPGroup,
      full_point_image_of_contained h e hz hk u hR,
      card_map_of_injective (MulAut.conj u).injective,pointCore_card]
  · rw [hg.1] at hc
    cases hc

include h e hz hk in
/-- At distance two, the actual relative core index divides the marked
point-core order eight. Normality is only needed inside the common edge. -/
theorem point_two_step_core_index_dvd_eight
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c z : Vertex Rg} (hc : color Rg c = false) (hzcol : color Rg z = false)
    (hd : (cosetGraph Rg).dist c z = 2) :
    (Q Rg z).relIndex (Q Rg c) ∣ 8 := by
  obtain ⟨t,hct,hzt⟩ := exists_common_neighbor_of_dist_two Rg c z hd
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hc] at hh
    cases he : color Rg t <;> simp_all
  have hQc : Q Rg c ≤ Q Rg t := Q_le_adjacent_h Rg ht hct
  have hQz : Q Rg z ≤ Q Rg t := Q_le_adjacent_h Rg ht hzt
  let : ((Q Rg z).subgroupOf (Q Rg t)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQz).mpr
      ((show Q Rg t ≤ stabilizer Rg z from fun _ hx => hx.2 z (adjacent_symm Rg hzt)).trans
        (Q_normalized Rg z))
  have hi := relIndex_dvd_index_of_normal ((Q Rg z).subgroupOf (Q Rg t))
    ((Q Rg c).subgroupOf (Q Rg t))
  rw [relIndex_subgroupOf hQc] at hi
  change (Q Rg z).relIndex (Q Rg c) ∣ (Q Rg z).relIndex (Q Rg t) at hi
  rwa [point_edge_core_index_eight h e hz hk u hR hzcol hzt] at hi

include h e hz hk in
private theorem point_four_midpoint_core_cases
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hne : ⁅Z Rg z ⊓ Q Rg a,Q Rg (p.walk.getVert 2)⁆ ≠ ⊥) :
    (Q Rg z).relIndex (Q Rg (p.walk.getVert 2)) = 4 ∨
      (Q Rg z).relIndex (Q Rg (p.walk.getVert 2)) = 8 := by
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hs : (Q Rg z).relIndex (Z Rg a) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR p).1]
    decide
  have hlarge := four_midpoint_core_large_of_kernel_nonzero h e hz hk hb p hs hne
  have hd := point_two_step_core_index_dvd_eight h e hz hk u hR
    (c := p.walk.getVert 2) (z := z) ((p.vertex_color (by omega)).mpr (by decide)) p.end_color (by rw [p.dist_end,hl])
  have hi := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
    (show (Q Rg z).relIndex (Q Rg (p.walk.getVert 2)) ∣ 2^3 from hd)
  obtain ⟨k,hk,he⟩ := hi
  interval_cases k <;> simp only [Nat.reducePow] at he <;> omega


include h e hz hk in
/-- The whole midpoint core has image four or eight at each critical endpoint,
although the full midpoint radius has image two there. The radius and the
endpoint core therefore do not supplement the midpoint core. -/
theorem point_critical_midpoint_core_bounds
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    let c := p.walk.getVert 2
    ((Q Rg a).relIndex (Q Rg c) = 4 ∨ (Q Rg a).relIndex (Q Rg c) = 8) ∧
    ((Q Rg z).relIndex (Q Rg c) = 4 ∨ (Q Rg z).relIndex (Q Rg c) = 8) ∧
    (Q Rg a).relIndex (V Rg c) = 2 ∧
    (Q Rg z).relIndex (V Rg c) = 2 ∧
    ¬ Q Rg c ≤ Q Rg a ⊔ V Rg c ∧
    ¬ Q Rg c ≤ Q Rg z ⊔ V Rg c := by
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let pr : CriticalPath Rg (sourceGeometry h) z a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) a p.start_color
        (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
        z p.end_color p.critical⟩
  have hpr : pr.walk.getVert 2 = p.walk.getVert 2 := by
    change p.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,hl]
  have hnon (x y : Vertex Rg) (r : CriticalPath Rg (sourceGeometry h) x y) :
      ⁅Z Rg y ⊓ Q Rg x,Q Rg (r.walk.getVert 2)⁆ ≠ ⊥ := by
    intro he
    have hh := (point_critical_radius_cross_kernel_line_at h e hz hk u hR r).1
    rw [he,card_bot] at hh
    omega
  have ha := point_four_midpoint_core_cases h e hz hk u hR pr (hnon _ _ pr)
  rw [hpr] at ha
  have hnosupp (x y : Vertex Rg) (r : CriticalPath Rg (sourceGeometry h) x y) :
      ¬ Q Rg (r.walk.getVert 2) ≤ Q Rg y ⊔ V Rg (r.walk.getVert 2) := by
    intro hsupp
    apply hnon x y r
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    apply hsupp.trans
    apply sup_le
    · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg y r.end_color))).trans (centralizer_le inf_le_left)
    · exact le_centralizer_iff.mp
        (point_critical_kernels_centralize_midpoint_radius h e hz hk u hR r).2
  have hna := hnosupp _ _ pr
  rw [hpr] at hna
  exact ⟨ha,point_four_midpoint_core_cases h e hz hk u hR p (hnon _ _ p),
    (point_critical_midpoint_radius_indices h e hz hk u hR p).1,
    (point_critical_midpoint_radius_indices h e hz hk u hR p).2,hna,hnosupp _ _ p⟩


include h e hz hk in
/-- The same nonzero shifted kernel is noncentral at the backward endpoint,
using the reversed original path rather than a second graph or core marking. -/
theorem point_shifted_kernel_noncentral_at_backward_endpoint
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = a)
    (hne : ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆ ≠ ⊥) :
    ¬ ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆ ≤
      centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) := by
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  let qr : CriticalPath Rg (sourceGeometry h) c d :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) d q.start_color
        (by rw [(sourceGeometry h).distance_constant _ q.start_color]; exact sourceDistance_pos h)
        c q.end_color q.critical⟩
  have hqr : qr.walk.getVert 2 = a := by
    change q.walk.reverse.getVert 2 = a
    rw [SimpleGraph.Walk.getVert_reverse,hl]
    exact hqa
  have he := (point_shifted_omega_kernel_line h e hz hk u hR p q hpc hqa).2.2.1.resolve_left hne
  have hs : (Q Rg d).relIndex (Z Rg c) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR qr).1]
    decide
  rw [he,←hqr] at hne ⊢
  exact four_kernel_core_noncentral h e hz hk hb qr hs hne

omit hk in
include h e hz in
/-- Whole-core application with both full midpoint core images and the same moving attachment. -/
theorem coreExhaustion_or_cubic_midpoint_core :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (let := h.relative_normal
           ∃ E : Additive W ≃ₗ[ZMod 2] core (Fin 6),
             ∀ (g : M) (v : Additive W),
               E (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
                 coreRepresentation (Fin 6) (CubicAction.projection h e hz hk g) (E v)) ∧
          (∀ a : Vertex Rg, color Rg a = false →
            Nat.card (U Rg a) = 32 ∧
            Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
              Subgroup (FreeAmalgam Rg)) = 2) ∧
          (∀ a : Vertex Rg, color Rg a = false →
            X Rg a = U Rg a ⊔
              (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
            X Rg a = Z Rg a) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∧
            ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
                (p.walk.getVert (p.walk.length-2)),
              q.walk.getVert 2 = alpha Rg ∧
              Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
              let c := p.walk.getVert (p.walk.length-2)
              let H := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
              let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
              H = ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆ ∧
              H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆ ∧
              Nat.card H = 2 ∧
              H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) ∧
              C ≤ Z Rg (alpha Rg) ∧
              ¬ C ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              ⁅C,Q Rg (q.walk.getVert 1)⁆ ≠ ⊥ ∧
              ¬ H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) ∧
              ((Q Rg z).relIndex (Q Rg c) = 4 ∨ (Q Rg z).relIndex (Q Rg c) = 8) ∧
              ((Q Rg d).relIndex (Q Rg (alpha Rg)) = 4 ∨
                (Q Rg d).relIndex (Q Rg (alpha Rg)) = 8) ∧
              (Q Rg z).relIndex (V Rg c) = 2 ∧
              (Q Rg d).relIndex (V Rg (alpha Rg)) = 2 ∧
              ¬ Q Rg c ≤ Q Rg z ⊔ V Rg c ∧
              ¬ Q Rg (alpha Rg) ≤ Q Rg d ⊔ V Rg (alpha Rg))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_attachment_movement h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · rcases hpoint with ⟨hpoint,hb4,hmodel,hsize,hX,z,p,hstrict,d,q,hqa,hgen,
      hback,hfull,hcard,hcentral,hnon,hCZ,hCn,hmove⟩
    have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
    have hpc : p.walk.getVert 2 = p.walk.getVert (p.walk.length-2) := by rw [hl]
    have hne : ⁅U Rg d ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),
        X Rg z ⊓ Q Rg (alpha Rg)⁆ ≠ ⊥ := by
      intro he
      rw [he,card_bot] at hcard
      omega
    have hdnon := point_shifted_kernel_noncentral_at_backward_endpoint h e hz hk u
      hpoint.le p q hpc hqa hne
    have hpb := point_critical_midpoint_core_bounds h e hz hk u hpoint.le p
    have hqb := point_critical_midpoint_core_bounds h e hz hk u hpoint.le q
    dsimp only at hpb hqb
    rw [hpc] at hpb
    rw [hqa] at hqb
    exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint,hb4,hmodel,hsize,hX,
      z,p,hstrict,d,q,hqa,hgen,hback,hfull,hcard,hcentral,hnon,hCZ,hCn,hmove,
      hdnon,hpb.2.1,hqb.1,hpb.2.2.2.1,hqb.2.2.1,hpb.2.2.2.2.2,hqb.2.2.2.2.1⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application with the exact core/radius gap on the same strict paths. -/
theorem rankTwo_or_cubic_midpoint_core :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (let := h.relative_normal
           ∃ E : Additive W ≃ₗ[ZMod 2] core (Fin 6),
             ∀ (g : M) (v : Additive W),
               E (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
                 coreRepresentation (Fin 6) (CubicAction.projection h e hz hk g) (E v)) ∧
          (∀ a : Vertex Rg, color Rg a = false →
            Nat.card (U Rg a) = 32 ∧
            Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
              Subgroup (FreeAmalgam Rg)) = 2) ∧
          (∀ a : Vertex Rg, color Rg a = false →
            X Rg a = U Rg a ⊔
              (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
            X Rg a = Z Rg a) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∧
            ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
                (p.walk.getVert (p.walk.length-2)),
              q.walk.getVert 2 = alpha Rg ∧
              Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
              let c := p.walk.getVert (p.walk.length-2)
              let H := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
              let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
              H = ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆ ∧
              H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆ ∧
              Nat.card H = 2 ∧
              H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) ∧
              C ≤ Z Rg (alpha Rg) ∧
              ¬ C ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              ⁅C,Q Rg (q.walk.getVert 1)⁆ ≠ ⊥ ∧
              ¬ H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) ∧
              ((Q Rg z).relIndex (Q Rg c) = 4 ∨ (Q Rg z).relIndex (Q Rg c) = 8) ∧
              ((Q Rg d).relIndex (Q Rg (alpha Rg)) = 4 ∨
                (Q Rg d).relIndex (Q Rg (alpha Rg)) = 8) ∧
              (Q Rg z).relIndex (V Rg c) = 2 ∧
              (Q Rg d).relIndex (V Rg (alpha Rg)) = 2 ∧
              ¬ Q Rg c ≤ Q Rg z ⊔ V Rg c ∧
              ¬ Q Rg (alpha Rg) ≤ Q Rg d ⊔ V Rg (alpha Rg))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_midpoint_core h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
