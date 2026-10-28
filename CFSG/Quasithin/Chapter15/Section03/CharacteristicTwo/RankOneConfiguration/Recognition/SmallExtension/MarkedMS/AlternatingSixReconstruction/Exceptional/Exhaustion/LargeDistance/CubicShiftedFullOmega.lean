module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicReciprocalAttachment
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFullCoreMovement

/-!
# The full opposite omega action on the shifted cubic kernel

Let a--z and d--c be the retained critical paths with midpoints c and a.
Put Y = U_d intersect Q_c, H = [Y,X_z intersect Q_a], and T = [Y,X_z].
The original natural quotient detects every actor whose movement lies in
[Z_a,Z_z] joined with the endpoint attachment: such an actor fixes the
entire opposite omega kernel. The projection kernel remains E, and the
odd quotient E/Q is removed only for two-subgroups.

Consequently the full-X inequality in MS93 (5.12)(1) on these paths is
equivalent to H = 1. When H is nonzero, the actual full opposite action T
strictly contains H, has order four, eight or sixteen, and lies in
U_z intersect Q_a. Its next midpoint-core commutator lies in H, and T fixes
the whole midpoint radius. The selected-path application supplies H of
order two and hence exposes failure of that inequality in the remaining
point branch. This is a necessary configuration under that branch, not a
counterexample to the source theorem. Proving the source comparison with
its simultaneous selectors would eliminate this configuration.

The whole-core and literal C.1.32 applications preserve the original
conjugator, generating edge, common attachment plane and reciprocal slices.
They leave the point contradiction, the plane/Sylow image branches and
both final reconstruction outcomes open. No natural replacement graph is
identified with the cubic graph.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), pp.866--867, and (5.12)(1), pp.924--925;
Aschbacher--Smith C.1.31--32, pp.135--136.
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
/-- An actor whose full movement stays in the critical attachment plane
fixes the entire opposite omega kernel. The quotient still has kernel E. -/
theorem point_full_omega_plane_control
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (Y : Subgroup (FreeAmalgam Rg)) (hYG : Y ≤ stabilizer Rg z)
    (hbound : ⁅X Rg z,Y⁆ ≤
      ⁅Z Rg a,Z Rg z⁆ ⊔
        (U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) :
    ⁅Y,X Rg z ⊓ Q Rg a⁆ = ⊥ := by
  have hAG := critical_Z_le_stabilizer Rg (sourceGeometry h) z p.end_color
    (by rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h)
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      z p.end_color p.critical)
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,_⟩ := graph_cover h e hz hk z p.end_color
  let A := (Z Rg a).comap i
  let B := Y.comap i
  have hmA : A.map i = Z Rg a := map_comap_eq_self (hAG.trans_eq hir.symm)
  have hmB : B.map i = Y := map_comap_eq_self (hYG.trans_eq hir.symm)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  have hAp : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 (Z Rg a)).comap_of_injective i hi
  have hAn : ¬ A ≤ pCore 2 M := by
    intro hle
    exact p.critical.2 (by
      have hh := map_mono (f := i) hle
      rwa [hmA,hiQ] at hh)
  have hidx : (centralizer (A : Set M)).relIndex W ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,
      ←map_inf_centralizer_of_injective i hi,hiU,hmA,inf_relIndex_left]
    have hQC : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a p.start_color))
    let := finite_Z Rg z
    let : Finite (U Rg z) := Finite.of_injective (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (point_image_critical_indices_two h e hz hk u hR p).2.1
  let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      z p.end_color p.critical)
  have hline : ⁅U Rg z,Z Rg a⁆ = ⁅Z Rg a,Z Rg z⁆ := by
    rw [small_critical_moving_commutator_eq h e hz hk pr (by
      rw [(point_image_critical_indices_two h e hz hk u hR p).2.1]; decide),commutator_comm]
  have hcent : (W ⊓ center M).map i =
      U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
    rw [show center M = centralizer ((⊤ : Subgroup M) : Set M) by
      rw [coe_top,centralizer_univ],←map_inf_centralizer_of_injective i hi,
      hiU,←MonoidHom.range_eq_map,hir]
  have hcomm : ⁅W,B⁆ ≤ ⁅W,A⁆ ⊔ (W ⊓ center M) := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [Subgroup.map_sup,map_commutator (W),map_commutator (W),hiU,hmA,hmB,hline,hcent]
    exact (commutator_mono (DistanceEight.U_le_Z Rg z |>.trans
      ((point_omega_eq_seed h e hz hk u hR z p.end_color).symm.le)) le_rfl).trans hbound
  have hle := cover_actor_le_of_central_displacement h e hz hk A B hAp hAn hidx hcomm
  have hm := map_mono (f := i) hle
  rw [hmB,Subgroup.map_sup,hiE,hmA] at hm
  have hs : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR p).2.1]
    decide
  rw [←small_critical_omega_kernel_centralizer h e hz hk pr hs] at hm
  exact commutator_eq_bot_iff_le_centralizer.mpr (hm.trans inf_le_right)

include h e hz hk in
/-- On the same consecutive paths, the full-X inequality of (5.12)(1)
holds exactly when the shifted kernel commutator vanishes. -/
theorem point_shifted_full_omega_control_iff
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = a) :
    let Y := U Rg d ⊓ Q Rg c
    let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
    ⁅Y,X Rg z⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔ H ↔ H = ⊥ := by
  let Y := U Rg d ⊓ Q Rg c
  let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
  have hl : p.walk.length = 4 :=
    p.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
  have hYG : Y ≤ stabilizer Rg z :=
    inf_le_right.trans (Q_le_stabilizer_of_dist_le_two c z q.end_color p.end_color (by
      rw [←hpc,p.dist_end,hl]))
  constructor
  · intro hbound
    by_contra hn
    have hd := point_shifted_omega_kernel_line h e hz hk u hR p q hpc hqa
    have he : H = ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆ :=
      (hd.2.2.1.resolve_left hn).trans (hd.2.2.2.2.2.2.2.2 hn)
    have hplane := (point_critical_midpoint_attachment_plane h e hz hk u hR p).2.1
    rw [hpc] at hplane
    have hbound' : ⁅X Rg z,Y⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔
        (U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) := by
      rw [commutator_comm]
      apply hbound.trans
      change ⁅Z Rg a,Z Rg z⁆ ⊔ H ≤ _
      rw [he,sup_comm (⁅Z Rg a,Z Rg z⁆) (⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆)]
      exact hplane.le
    exact hn (point_full_omega_plane_control h e hz hk u hR p Y hYG hbound')
  · intro hzero
    rw [hzero,sup_bot_eq]
    exact small_critical_omega_kernel_control h e hz hk p (by
      rw [(point_image_critical_indices_two h e hz hk u hR p).1]; decide)
      Y hYG (commutator_eq_bot_iff_le_centralizer.mp hzero)

include h e hz hk in
/-- The actual full opposite action moves the backward kernel into the
forward moving kernel. Its order is four, eight or sixteen, and its next
midpoint-core commutator lies in the original shifted line. -/
theorem point_shifted_full_omega_movement
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = a)
    (hne : ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆ ≠ ⊥) :
    let Y := U Rg d ⊓ Q Rg c
    let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
    let T := ⁅Y,X Rg z⁆
    H < T ∧ T ≤ U Rg z ⊓ Q Rg a ∧
      (Nat.card T = 4 ∨ Nat.card T = 8 ∨ Nat.card T = 16) ∧
      ⁅T,Q Rg c⁆ ≤ H ∧
      T ≤ centralizer (V Rg c : Set (FreeAmalgam Rg)) ∧
      ¬ T ≤ ⁅Z Rg a,Z Rg z⁆ ⊔ H := by
  let Y := U Rg d ⊓ Q Rg c
  let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
  let T := ⁅Y,X Rg z⁆
  let F := ⁅X Rg z,Q Rg c⁆
  have hd := point_shifted_omega_kernel_line h e hz hk u hR p q hpc hqa
  have he : H = ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆ :=
    (hd.2.2.1.resolve_left hne).trans (hd.2.2.2.2.2.2.2.2 hne)
  have hHcard : Nat.card H = 2 := by
    change Nat.card (⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆ : Subgroup (FreeAmalgam Rg)) = 2
    rw [hd.2.2.1.resolve_left hne]
    exact hd.1
  have hnot : ¬ T ≤ ⁅Z Rg a,Z Rg z⁆ ⊔ H :=
    fun hb => hne ((point_shifted_full_omega_control_iff h e hz hk u hR p q hpc hqa).mp hb)
  have hHT : H ≤ T := commutator_mono le_rfl inf_le_left
  have hstrict : H < T := lt_of_le_not_ge hHT (fun ht => hnot (ht.trans le_sup_right))
  have hTF : T ≤ F := by
    dsimp only [T,F]
    rw [commutator_comm Y]
    exact commutator_mono le_rfl inf_le_right
  have hm := point_full_omega_midpoint_core_movement h e hz hk u hR p
  have hg := (point_full_omega_midpoint_core_growth h e hz hk u hR p).2
  dsimp only at hm hg
  rw [hpc,←he] at hm
  rw [hpc] at hg
  have hTK : T ≤ U Rg z ⊓ Q Rg a := hTF.trans hm.1
  let := finite_Z Rg z
  let : Finite (U Rg z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
  let : Finite F := Finite.of_injective
    (inclusion (hm.1.trans inf_le_left)) (inclusion_injective _)
  let : Finite T := Finite.of_injective (inclusion hTF) (inclusion_injective _)
  have hlo : 2 < Nat.card T := by
    by_contra! hno
    exact hstrict.ne (eq_of_le_of_card_ge hHT (by omega))
  have hup : Nat.card T ≤ 16 :=
    (card_le_of_le hTF).trans (by rcases hg with he|he <;> change Nat.card F = _ at he <;> omega)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  obtain ⟨k,hkcard⟩ := ((IsElementaryAbelian.isPGroup 2 (Z Rg z)).to_le
    (hTK.trans (inf_le_left.trans (DistanceEight.U_le_Z Rg z)))).exists_card_eq
  change Nat.card T = 2^k at hkcard
  have hk4 : k ≤ 4 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (show 2^k ≤ 2^4 by omega)
  have hcard : Nat.card T = 4 ∨ Nat.card T = 8 ∨ Nat.card T = 16 := by
    interval_cases k <;> simp only [Nat.reducePow] at hkcard <;> omega
  have hcentral := (point_critical_omega_kernels_centralize_midpoint_radius h e hz hk u hR p).2
  rw [hpc] at hcentral
  have hTX : T ≤ X Rg z ⊓ Q Rg a := hTK.trans (inf_le_inf_right _
    ((DistanceEight.U_le_Z Rg z).trans ((point_omega_eq_seed h e hz hk u hR z p.end_color).symm.le)))
  exact ⟨hstrict,hTK,hcard,(commutator_mono hTF le_rfl).trans hm.2.1,
    hTX.trans hcentral,hnot⟩

omit hk in
include h e hz in
/-- Whole-core application of the full opposite omega movement, on the
same paths and with the original conjugator and reciprocal slices. -/
theorem coreExhaustion_or_cubic_shifted_full_omega :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ a : Vertex Rg, color Rg a = false →
            Nat.card (U Rg a) = 32 ∧
            Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
              Subgroup (FreeAmalgam Rg)) = 2) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∧
            ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
                (p.walk.getVert (p.walk.length-2)),
              ∃ x : FreeAmalgam Rg, x ∈ stabilizer Rg (alpha Rg) ∧
              act Rg x (p.walk.getVert 2) = d ∧
              q.walk.getVert 2 = alpha Rg ∧
              Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
              let c := p.walk.getVert (p.walk.length-2)
              let H := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
              let D₀ := ⁅Z Rg d,Z Rg c⁆
              let C := fun v => U Rg v ⊓
                centralizer (stabilizer Rg v : Set (FreeAmalgam Rg))
              Nat.card H = 2 ∧
              H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              C d = C c ∧
              H ⊔ D₀ = D₀ ⊔ C c ∧
              Nat.card (H ⊔ D₀ : Subgroup (FreeAmalgam Rg)) = 4 ∧
              H ⊔ D₀ ≤ U Rg d ⊓ U Rg c ⊓
                centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) = 2 ∧
              (B Rg c ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) = 2 ∧
              (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (Z Rg (alpha Rg)) = 2 ∧
              (B Rg c ((sourceGeometry h).Z_normal _)).relIndex (Z Rg (alpha Rg)) = 2 ∧
              let T := ⁅U Rg d ⊓ Q Rg c,X Rg z⁆
              H < T ∧ T ≤ U Rg z ⊓ Q Rg (alpha Rg) ∧
                (Nat.card T = 4 ∨ Nat.card T = 8 ∨ Nat.card T = 16) ∧
                ⁅T,Q Rg c⁆ ≤ H ∧
                T ≤ centralizer (V Rg c : Set (FreeAmalgam Rg)) ∧
                ¬ T ≤ ⁅Z Rg (alpha Rg),Z Rg z⁆ ⊔ H)) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_full_core_movement h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hex
  · rcases hpoint with ⟨hpoint,hb4,hmodel,hsize,hX,hplanes,z,p,hstrict,
      d,q,x,hx,hxc,hqa,hgen,hback,hfull,hcard,hcentral,hnon,hCZ,hCn,hmove,
      hdnon,hpb,hqb,hpV,hqV,hpn,hqn,hattach,hplane,hplaneCard,hplaneLe,hcores⟩
    have hslices := point_common_attachment_reciprocal_slices h e hz hk u hpoint.le q hqa hattach
    have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
    have hpc : p.walk.getVert 2 = p.walk.getVert (p.walk.length-2) := by rw [hl]
    have hne : ⁅U Rg d ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),
        X Rg z ⊓ Q Rg (alpha Rg)⁆ ≠ ⊥ := by
      intro he
      rw [he,card_bot] at hcard
      omega
    have hmovement := point_shifted_full_omega_movement h e hz hk u hpoint.le p q hpc hqa hne
    exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint,hb4,hsize,z,p,hstrict,d,q,x,
      hx,hxc,hqa,hgen,hcard,hcentral,hattach,hplane,hplaneCard,hplaneLe,
      hslices.1,hslices.2.1,hslices.2.2.1,hslices.2.2.2,hmovement⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the full opposite omega calculation,
retaining the original radical and both moving covers in the other branches. -/
theorem rankTwo_or_cubic_shifted_full_omega :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ a : Vertex Rg, color Rg a = false →
            Nat.card (U Rg a) = 32 ∧
            Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
              Subgroup (FreeAmalgam Rg)) = 2) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∧
            ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
                (p.walk.getVert (p.walk.length-2)),
              ∃ x : FreeAmalgam Rg, x ∈ stabilizer Rg (alpha Rg) ∧
              act Rg x (p.walk.getVert 2) = d ∧
              q.walk.getVert 2 = alpha Rg ∧
              Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
              let c := p.walk.getVert (p.walk.length-2)
              let H := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
              let D₀ := ⁅Z Rg d,Z Rg c⁆
              let C := fun v => U Rg v ⊓
                centralizer (stabilizer Rg v : Set (FreeAmalgam Rg))
              Nat.card H = 2 ∧
              H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              C d = C c ∧
              H ⊔ D₀ = D₀ ⊔ C c ∧
              Nat.card (H ⊔ D₀ : Subgroup (FreeAmalgam Rg)) = 4 ∧
              H ⊔ D₀ ≤ U Rg d ⊓ U Rg c ⊓
                centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
              (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) = 2 ∧
              (B Rg c ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) = 2 ∧
              (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (Z Rg (alpha Rg)) = 2 ∧
              (B Rg c ((sourceGeometry h).Z_normal _)).relIndex (Z Rg (alpha Rg)) = 2 ∧
              let T := ⁅U Rg d ⊓ Q Rg c,X Rg z⁆
              H < T ∧ T ≤ U Rg z ⊓ Q Rg (alpha Rg) ∧
                (Nat.card T = 4 ∨ Nat.card T = 8 ∨ Nat.card T = 16) ∧
                ⁅T,Q Rg c⁆ ≤ H ∧
                T ≤ centralizer (V Rg c : Set (FreeAmalgam Rg)) ∧
                ¬ T ≤ ⁅Z Rg (alpha Rg),Z Rg z⁆ ⊔ H)) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_shifted_full_omega h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
