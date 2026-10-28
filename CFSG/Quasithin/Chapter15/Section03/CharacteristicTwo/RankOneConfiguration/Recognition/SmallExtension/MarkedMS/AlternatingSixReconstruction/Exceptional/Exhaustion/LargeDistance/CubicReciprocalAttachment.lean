module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFullCoreMovement

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicMidpointSlices

/-!
# Reciprocal index-two slices from the common cubic attachment

For a critical four-edge path a--z, a central endpoint attachment forces
the forward moving slice at a to have index exactly two. Otherwise the
generating backward configuration from the strict slice makes that same
attachment noncentral in G_a. The original escape theorem excludes index
one. Conjugation transports the attachment, path and Baumann slice together.

Apply this to both orientations of the already selected path d--c through a.
Its endpoint attachments coincide by the common-plane theorem, so both
B_d and B_c cut U_a in index two. The full seed is U_a joined with the
incident edge seed, which lies in the corresponding Baumann slice. Thus
both indices on Z_a are also exactly two. The original forward slice of
U_c at a remains strict; this gives an asymmetric pair of slices on the
same original cubic graph, without identifying it with the natural graph.

The whole-core and literal C.1.32 consumers retain the actual selected
paths and conjugator, the central four-group, the original cubic kernel E
with its nontrivial E/Q, and both cover sizes in the other image branches.
The full-X control and terminal contradiction in MS93 (5.12), the remaining
radical images, natural exhaustion and final reconstruction remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the attachment and reciprocal-slice arguments in (5.12), printed
pp.924--927; Aschbacher--Smith C.1.31--32, printed pp.135--136.
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
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem point_base_slice_le_two_of_central_attachment
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hcentral : U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) :
    (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2 := by
  by_contra! hlarge
  obtain ⟨d,q,hqa,hgen,hback,hfull,hcard,hcent,hnon,hCZ,hCn,hmove⟩ :=
    point_strict_forward_attachment h e hz hk u hR p hlarge
  exact hCn hcentral

include h e hz hk in
/-- A central endpoint attachment forces a forward moving slice of index two.
The attachment and the slice are transported by the same graph action. -/
theorem point_forward_slice_eq_two_of_central_attachment
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hcentral : U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) :
    (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) = 2 := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hcen :
      U Rg (act Rg g⁻¹ z) ⊓
        centralizer (stabilizer Rg (act Rg g⁻¹ z) : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (act Rg g⁻¹ a) : Set (FreeAmalgam Rg)) := by
    have hm := (map_mono (f := (MulAut.conj g).toMonoidHom) hcentral).trans
      (map_centralizer_le_centralizer_image _ _)
    rw [←map_inf_centralizer_of_injective _ (MulAut.conj g).injective] at hm
    simpa only [U_act,stabilizer_act,inv_inv,Subgroup.coe_map] using hm
  have hpact : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ a) (act Rg g⁻¹ z),
      p₀.walk.getVert 2 = act Rg g⁻¹ (p.walk.getVert 2) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hpact hcen
  obtain ⟨p₀,hvert⟩ := hpact
  have hi := point_base_slice_le_two_of_central_attachment h e hz hk u hR p₀ hcen
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) (distance_gt_two h e hz hk) g⁻¹ a p.start_color
  rw [hbase,inv_inv] at hB
  rw [hvert,U_act,inv_inv,hB,
    relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  let := finite_Z Rg (p.walk.getVert 2)
  let : Finite (U Rg (p.walk.getVert 2)) :=
    Finite.of_injective (inclusion (DistanceEight.U_le_Z Rg _)) (inclusion_injective _)
  have hne0 : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≠ 0 := index_ne_zero_of_finite
  have hne1 : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≠ 1 := by
    intro he
    exact full_point_critical_forward_eligible h e hz hk (distance_gt_two h e hz hk) u
      (full_point_image_of_contained h e hz hk u hR) p (relIndex_eq_one.mp he)
  exact le_antisymm hi (by omega)


include h e hz hk in
private theorem point_forward_seed_slice_eq_moving_slice
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (Z Rg (p.walk.getVert 2)) =
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let Ba := B Rg a ((sourceGeometry h).Z_normal _)
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 :=
    p.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg a t := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hZtB : Z Rg t ≤ Ba :=
    (adjacent_Z_le Rg p.start_color hat).trans (Escape.EdgeTransfer.Z_le_B hb a p.start_color)
  have hZcV : Z Rg c ≤ V Rg a :=
    le_iSup_of_le c (le_iSup_of_le (by
      rw [SimpleGraph.dist_comm,p.dist_start (by omega)]) le_rfl)
  have hZcG : Z Rg c ≤ stabilizer Rg a :=
    hZcV.trans ((sourceGeometry h).V_local _ p.start_color (by
      rw [(sourceGeometry h).distance_constant _ p.start_color]
      exact hb))
  have hBn := Escape.Propagation.Rigidity.B_normalized
    (geometry := sourceGeometry h) hb a p.start_color
  have hjoin : Ba ⊔ Z Rg c = Ba ⊔ U Rg c := by
    rw [vertex_seed_eq_moving_sup_edge h e hz hc hct,←sup_assoc,
      sup_of_le_left (hZtB.trans le_sup_left)]
  calc
    _ = Ba.relIndex (Ba ⊔ Z Rg c) :=
      (relIndex_sup_of_normalized _ _ (hZcG.trans hBn)).symm
    _ = Ba.relIndex (Ba ⊔ U Rg c) := congrArg (fun A => Ba.relIndex A) hjoin
    _ = _ := relIndex_sup_of_normalized _ _
      (((DistanceEight.U_le_Z Rg c).trans hZcG).trans hBn)


include h e hz hk in
/-- On a critical four-edge path whose endpoint attachments coincide,
both endpoint slices of its midpoint moving subgroup and full seed have index two. -/
theorem point_common_attachment_reciprocal_slices
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {d c a : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) d c)
    (hqa : q.walk.getVert 2 = a)
    (hsame : U Rg d ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) =
      U Rg c ⊓ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))) :
    (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) = 2 ∧
      (B Rg c ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) = 2 ∧
      (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (Z Rg a) = 2 ∧
      (B Rg c ((sourceGeometry h).Z_normal _)).relIndex (Z Rg a) = 2 := by
  have hd := point_forward_slice_eq_two_of_central_attachment h e hz hk u hR q
    (hsame.symm.le.trans inf_le_right)
  rw [hqa] at hd
  have hl : q.walk.length = 4 :=
    q.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
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
  have hc := point_forward_slice_eq_two_of_central_attachment h e hz hk u hR qr
    (hsame.le.trans inf_le_right)
  rw [hqr] at hc
  have hZd := point_forward_seed_slice_eq_moving_slice h e hz hk u hR q
  have hZc := point_forward_seed_slice_eq_moving_slice h e hz hk u hR qr
  rw [hqa] at hZd
  rw [hqr] at hZc
  exact ⟨hd,hc,hZd.trans hd,hZc.trans hc⟩


omit hk in
include h e hz in
/-- Whole-core application: the retained backward path has two reciprocal
index-two slices, for both the moving subgroup and the full midpoint seed. -/
theorem coreExhaustion_or_cubic_reciprocal_attachment :
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
              (B Rg c ((sourceGeometry h).Z_normal _)).relIndex (Z Rg (alpha Rg)) = 2)) ∨
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
    exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint,hb4,hsize,z,p,hstrict,d,q,x,
      hx,hxc,hqa,hgen,hcard,hcentral,hattach,hplane,hplaneCard,hplaneLe,hslices⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the two simultaneous reciprocal slices,
with the original radical, cubic kernel and full moving covers retained. -/
theorem rankTwo_or_cubic_reciprocal_attachment :
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
              (B Rg c ((sourceGeometry h).Z_normal _)).relIndex (Z Rg (alpha Rg)) = 2)) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_reciprocal_attachment h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
