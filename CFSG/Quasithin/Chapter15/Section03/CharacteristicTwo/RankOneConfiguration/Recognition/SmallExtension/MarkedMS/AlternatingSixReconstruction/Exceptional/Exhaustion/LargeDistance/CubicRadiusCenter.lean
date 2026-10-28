module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicTerminal

/-!
# Central involutions in the remaining cubic strict-slice branch

At a critical four-edge path, the intersection of the full endpoint seed
with the midpoint radius center is exactly its opposite critical kernel,
of index two. The selected span's derived line also bounds its moving
seed's displacement on the full original radius. The checked six-letter
cover calculation turns this into a centralizer index at most two for
both orders 16 and 32.

Consequently both reciprocal moving subgroups have index at most two
modulo the opposite radius centers. The terminal strict-slice alternative
therefore supplies a moving vector in one of these centers outside its
Baumann slice, on the same selected path. This vector is an involution.
Conjugation transports the obstruction to the base vertex: the original
component moves Omega_1 Z(V_alpha) nontrivially modulo Z_alpha.
This subgroup is distinct from X_alpha = Omega_1 Z(Q_alpha).

The whole-core and literal C.1.32 applications retain the original cubic
projection, its kernel E, both full moving covers, the selected derived
line and the plane/Sylow radical alternatives. Excluding the elementary
radius-center movement still requires the remaining source comparison;
this reduction does not complete MS93 (5.12), exceptional exhaustion or
the natural reconstruction branch.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the reciprocal slices in (3.10), pp.879--881, and (5.12)(3),
pp.926--927; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open CFSG.Quasithin.ChapterB.Offenders.Six
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
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
private theorem relative_center_eq_inf {F : Type*} [Group F] (A : Subgroup F) :
    (center A).map A.subtype = A ⊓ centralizer (A : Set F) := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a.property,fun b hb => congrArg Subtype.val (mem_center_iff.mp ha ⟨b,hb⟩)⟩
  · rintro ⟨hx,hc⟩
    exact ⟨⟨x,hx⟩,mem_center_iff.mpr (fun b => Subtype.ext (hc b b.property)),rfl⟩

include h e hz hk in
/-- The full seed's intersection with the midpoint radius center is exactly
its opposite critical kernel. In particular its index is two, with the
original full seed and odd extension kernel retained. -/
theorem point_critical_seed_radius_center
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    let Vc := V Rg (p.walk.getVert 2)
    Z Rg a ⊓ (center Vc).map Vc.subtype = Z Rg a ⊓ Q Rg a' ∧
      ((center Vc).map Vc.subtype).relIndex (Z Rg a) = 2 := by
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let Vc := V Rg (p.walk.getVert 2)
  have hZa : Z Rg a ≤ Vc :=
    le_iSup_of_le a (le_iSup_of_le (by rw [p.dist_start (by omega)]) le_rfl)
  have hZe : Z Rg a' ≤ Vc :=
    le_iSup_of_le a' (le_iSup_of_le (by rw [SimpleGraph.dist_comm,p.dist_end,hl]) le_rfl)
  have hfixed : Z Rg a ⊓ centralizer (Z Rg a' : Set (FreeAmalgam Rg)) =
      Z Rg a ⊓ Q Rg a' :=
    critical_seed_centralizer_intersection h e p
  have heq : Z Rg a ⊓ (center Vc).map Vc.subtype = Z Rg a ⊓ Q Rg a' := by
    rw [relative_center_eq_inf]
    apply le_antisymm
    · exact (inf_le_inf_left _ (inf_le_right.trans (centralizer_le hZe))).trans_eq hfixed
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans hZa)
        (point_critical_kernels_centralize_midpoint_radius h e hz hk u hR p).1)
  refine ⟨heq,?_⟩
  rw [←inf_relIndex_left,heq,inf_relIndex_left]
  exact (point_image_critical_indices_two h e hz hk u hR p).1

include h e hz hk in
/-- Both reciprocal moving subgroups have index at most two modulo the
center of the opposite full radius. The forward estimate uses the actual
selected derived line; the reverse estimate uses the original critical pair. -/
theorem point_selected_radius_center_indices
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hcard : Nat.card (⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ : Subgroup (FreeAmalgam Rg)) = 2)
    (hradius : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),V Rg (alpha Rg)⁆ =
      ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
        localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆) :
    ((center (V Rg (alpha Rg))).map (V Rg (alpha Rg)).subtype).relIndex
        (U Rg (p.walk.getVert 2)) ≤ 2 ∧
      ((center (V Rg (p.walk.getVert 2))).map (V Rg (p.walk.getVert 2)).subtype).relIndex
        (U Rg (alpha Rg)) ≤ 2 := by
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let c := p.walk.getVert 2
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  have hct : Adjacent Rg c (p.walk.getVert 1) := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg (p.walk.getVert 1) = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg (p.walk.getVert 1) at hh
    cases he : color Rg (p.walk.getVert 1) <;> simp_all
  have hVG : V Rg (alpha Rg) ≤ stabilizer Rg c :=
    ((sourceGeometry h).V_le_Q hb2 _ rfl).trans
      ((Q_le_adjacent_h Rg ht hat).trans (fun _ hx => hx.2 _ (adjacent_symm Rg hct)))
  have hUcP : U Rg c ≤ localZSpan Rg c (alpha Rg) :=
    (DistanceEight.U_le_Z Rg c).trans (Z_le_localZSpan Rg _ _)
  have hUcV : U Rg c ≤ V Rg (alpha Rg) := hUcP.trans
    (localZSpan_le_V Rg (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)]))
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite (localZSpan Rg c (alpha Rg)) := Finite.of_injective
    (inclusion ((localZSpan_le_V Rg (by
      rw [SimpleGraph.dist_comm,p.dist_start (by omega)])).trans
      ((sourceGeometry h).V_local _ rfl hb2))) (inclusion_injective _)
  let : Finite (⁅localZSpan Rg c (alpha Rg),localZSpan Rg c (alpha Rg)⁆ :
      Subgroup (FreeAmalgam Rg)) := Finite.of_injective
    (inclusion (commutator_le_self _)) (inclusion_injective _)
  have hcomm : Nat.card (⁅U Rg c,V Rg (alpha Rg)⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
    apply (card_le_of_le ((commutator_mono hUcP le_rfl).trans_eq hradius)).trans_eq hcard
  have hi := moving_small_commutator_fixed_index h e hz hk hc _ hVG hcomm
  constructor
  · have he : U Rg c ⊓ (center (V Rg (alpha Rg))).map (V Rg (alpha Rg)).subtype =
        U Rg c ⊓ centralizer (V Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
      rw [relative_center_eq_inf,←inf_assoc,inf_eq_left.mpr hUcV]
    rw [←inf_relIndex_left,he,inf_relIndex_left]
    exact hi
  · have hZa := (point_critical_seed_radius_center h e hz hk u hR p).2
    let := finite_Z Rg (alpha Rg)
    exact (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg _)
      index_ne_zero_of_finite).trans_eq hZa

include h e hz hk in
/-- A strict reciprocal Baumann slice contains an actual moving vector in
the opposite radius center outside that Baumann slice. This is on the same
selected path, not on a natural replacement graph. -/
theorem point_selected_radius_center_escape
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hcard : Nat.card (⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ : Subgroup (FreeAmalgam Rg)) = 2)
    (hradius : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),V Rg (alpha Rg)⁆ =
      ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
        localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆) :
    (¬ U Rg (p.walk.getVert 2) ⊓
        (center (V Rg (alpha Rg))).map (V Rg (alpha Rg)).subtype ≤
          B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) ∨
      (¬ U Rg (alpha Rg) ⊓
        (center (V Rg (p.walk.getVert 2))).map (V Rg (p.walk.getVert 2)).subtype ≤
          B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)) := by
  have hn : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hcard
    omega
  have hi := point_selected_radius_center_indices h e hz hk u hR p hcard hradius
  have hs := point_selected_reciprocal_slice_alternative h e hz hk u hR p hn
  let := finite_Z Rg (p.walk.getVert 2)
  let := finite_Z Rg (alpha Rg)
  let : Finite (U Rg (p.walk.getVert 2)) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg _)) (inclusion_injective _)
  let : Finite (U Rg (alpha Rg)) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg _)) (inclusion_injective _)
  rcases hs with hs | hs
  · left
    intro hh
    have he := relIndex_le_of_le_left (L := U Rg (p.walk.getVert 2)) hh index_ne_zero_of_finite
    rw [inf_relIndex_left] at he
    exact (not_lt_of_ge (he.trans hi.1)) hs
  · right
    intro hh
    have he := relIndex_le_of_le_left (L := U Rg (alpha Rg)) hh index_ne_zero_of_finite
    rw [inf_relIndex_left] at he
    exact (not_lt_of_ge (he.trans hi.2)) hs

include h in
private theorem moving_inf_radius_center_le_omega {a c : Vertex Rg}
    (hc : color Rg c = false) :
    U Rg c ⊓ (center (V Rg a)).map (V Rg a).subtype ≤
      Stellmacher.omegaOneCenterAmbient (V Rg a) := by
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c hc
  rintro z ⟨hz,⟨v,hv,rfl⟩⟩
  exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨v.property,elemPow_eq_one_of_isElementaryAbelian _ ((DistanceEight.U_le_Z Rg c) hz),
      fun w hw => congrArg Subtype.val (mem_center_iff.mp hv ⟨w,hw⟩)⟩

include h e hz hk in
/-- The obstruction already lies in the elementary abelian involution
subgroup of the radius center, not merely in the possibly larger center.
This is Omega_1 Z(V_alpha), distinct from X_alpha = Omega_1 Z(Q_alpha). -/
theorem point_radius_omega_center_not_le_slice
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    ¬ Stellmacher.omegaOneCenterAmbient (V Rg (alpha Rg)) ≤
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  obtain ⟨a',p,hcard,_,hradius⟩ := point_image_selected_span_radius_line h e hz hk u hR
  have hs := point_selected_radius_center_escape h e hz hk u hR p hcard hradius
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  intro hbase
  rcases hs with hs | hs
  · exact hs ((moving_inf_radius_center_le_omega h hc).trans hbase)
  · obtain ⟨x,hx⟩ := exists_mVertex_of_color Rg hc
    have hxbase : act Rg x (alpha Rg) = p.walk.getVert 2 := by
      rw [hx]
      change act Rg x (mVertex Rg 1) = mVertex Rg x
      rw [act_mVertex,one_mul]
    have hm := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hbase
    rw [←Stellmacher.omegaOneCenterAmbient_map_injective _ (MulAut.conj x⁻¹).injective,
      ←V_act,←Escape.PairingControl.FirstPairing.B_act (by omega : 2 < sourceDistance h)
        x (alpha Rg) rfl,hxbase] at hm
    exact hs ((moving_inf_radius_center_le_omega h rfl).trans hm)

include h e hz hk in
/-- The original component moves the canonical elementary radius center
nontrivially modulo the original seed. This is the remaining comparison
needed by the point-core exclusion. -/
theorem point_radius_omega_center_component_movement
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    ¬ ⁅Stellmacher.omegaOneCenterAmbient (V Rg (alpha Rg)),
        Ltilde Rg (alpha Rg)⁆ ≤ Z Rg (alpha Rg) := by
  intro hc
  apply point_radius_omega_center_not_le_slice h e hz hk u hR
  have hb := distance_gt_two h e hz hk
  intro z hz
  apply (mem_B_iff Rg (alpha Rg) _ ((sourceGeometry h).V_local _ rfl hb) z).mpr
  refine ⟨((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).1,?_⟩
  intro l hl
  rw [commutator_comm] at hc
  exact hc (commutator_mem_commutator hl hz)

omit hk in
include h e hz in
/-- Whole-core application: the selected radius-line span has small
reciprocal radius-center indices, but a moving central vector escapes one
of the two Baumann slices. Both covers and all radical-image branches remain. -/
theorem coreExhaustion_or_cubic_radius_center :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (¬ ⁅Stellmacher.omegaOneCenterAmbient (V Rg (alpha Rg)),
              Ltilde Rg (alpha Rg)⁆ ≤ Z Rg (alpha Rg)) ∧
          ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
            let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
            let Ca := (center (V Rg (alpha Rg))).map (V Rg (alpha Rg)).subtype
            let Cc := (center (V Rg (p.walk.getVert 2))).map (V Rg (p.walk.getVert 2)).subtype
            Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
            Ca.relIndex (U Rg (p.walk.getVert 2)) ≤ 2 ∧
            Cc.relIndex (U Rg (alpha Rg)) ≤ 2 ∧
            ((¬ U Rg (p.walk.getVert 2) ⊓ Ca ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) ∨
              (¬ U Rg (alpha Rg) ⊓ Cc ≤ B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_radical_cases h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint.2,hpoint.1,
      point_radius_omega_center_component_movement h e hz hk u hpoint.2.le,?_⟩⟩
    obtain ⟨a',p,hcard,hcentral,hradius⟩ :=
      point_image_selected_span_radius_line h e hz hk u hpoint.2.le
    have hi := point_selected_radius_center_indices h e hz hk u hpoint.2.le p hcard hradius
    exact ⟨a',p,hcard,hcentral,hradius,hi.1,hi.2,
      point_selected_radius_center_escape h e hz hk u hpoint.2.le p hcard hradius⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application retaining the whole-core radius-center
obstruction and the unchanged plane and Sylow alternatives. -/
theorem rankTwo_or_cubic_radius_center :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (¬ ⁅Stellmacher.omegaOneCenterAmbient (V Rg (alpha Rg)),
              Ltilde Rg (alpha Rg)⁆ ≤ Z Rg (alpha Rg)) ∧
          ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
            let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
            let Ca := (center (V Rg (alpha Rg))).map (V Rg (alpha Rg)).subtype
            let Cc := (center (V Rg (p.walk.getVert 2))).map (V Rg (p.walk.getVert 2)).subtype
            Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
            Ca.relIndex (U Rg (p.walk.getVert 2)) ≤ 2 ∧
            Cc.relIndex (U Rg (alpha Rg)) ≤ 2 ∧
            ((¬ U Rg (p.walk.getVert 2) ⊓ Ca ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) ∨
              (¬ U Rg (alpha Rg) ⊓ Cc ≤ B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_radius_center h e hz).imp (rankTwo_of_exhaustion h e hz) id


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
