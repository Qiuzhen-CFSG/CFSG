module
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadius
public import Theory.Representation.NormalElementaryQuotient.SubgroupSpaceTransport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePredecessor
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRemainingRadicals
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardFixedCore
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicResidualShift

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePredecessor

/-!
# The same critical actor on the original cubic cover

In the plane branch, the actual paired selector retains an orientation whose
full-seed commutator escapes the starting seed. Both its reverse-kernel
commutator and its original critical line lie in that starting seed. Thus the
moving displacement cannot be controlled by their join. Removing the last-edge
seed uses its actual centralization of the predecessor actors and preserves all
central attachments.

One last-edge chart contains the original critical actor, the selected actor
and its residual conjugate. All three images lie in the same marked three-pair
group. The critical image is a transposition; its fixed space is precisely the
moving reverse kernel, and its displacement is the original critical line.
The predecessor residual identity transports the same kernel commutator.
Consequently the shifted actor has the same nonzero displacement on the full
cover and on that fixed space, while the control alternative is excluded.

The final whole-core and literal C.1.32 applications separate actual radius
escape from this explicit finite-cover obstruction. They do not infer trapping
from uniformly small slices. Excluding the finite obstruction still needs the
six-letter alignment and aligned-displacement theorems on both permitted
covers. The Borel and terminal branches and both final reconstructions remain.
The projection is the original cubic projection with kernel E, including its
nontrivial odd quotient over Q; it is not the natural replacement projection.

The internal imports reuse the original cubic selector and path proofs and the
private cover abbreviation in proofs only. Public action statements use the
literal normal-elementary quotient representation.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.0), printed p.859, and (5.8), printed p.920; Aschbacher--Smith,
C.1.31--32, printed pp.135--136. The source comparison is with the original
critical commutator times the endpoint center, not with the center alone.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.NormalElementaryQuotient
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

omit hk hz in
include h e in
/-- The moving part of the reverse kernel is the actual fixed subgroup of
the original critical seed, with the full seed attachment retained separately. -/
theorem critical_moving_kernel_eq_fixed
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    U Rg z ⊓ Q Rg a = U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) := by
  let q := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by
        rw [(sourceGeometry h).distance_constant a p.start_color]
        exact sourceDistance_pos h) z p.end_color p.critical)
  have hfixed := critical_seed_centralizer_intersection h e q
  calc
    _ = U Rg z ⊓ (Z Rg z ⊓ Q Rg a) := by
      rw [←inf_assoc,inf_eq_left.mpr (DistanceEight.U_le_Z Rg z)]
    _ = U Rg z ⊓ (Z Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg))) := by
      rw [hfixed]
    _ = _ := by rw [←inf_assoc,inf_eq_left.mpr (DistanceEight.U_le_Z Rg z)]

omit hk in
include h e hz in
private theorem critical_predecessor_seed_movement
    (hb : 2 < sourceDistance h)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (T : Subgroup (FreeAmalgam Rg))
    (hT : T ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    ⁅Z Rg z,T⁆ = ⁅U Rg z,T⁆ := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let t := p.walk.getVert (p.walk.length-1)
  have hzt : Adjacent Rg z t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hpre : Adjacent Rg (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hTt := hT.trans (Q_le_adjacent_h Rg ht hpre)
  have hh := full_fixed_seed_edge_commutator (h := h) (e := e) (hz := hz)
    p.end_color hzt ⊥ bot_le T hTt
  have hbot : centralizer (↑(⊥ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) = ⊤ := by
    ext x
    simp [mem_centralizer_iff]
  simpa only [hbot,inf_top_eq] using hh

include h e hz hk in
/-- The original critical line and the full reverse-kernel commutator cannot
control the selected moving displacement: that would contradict the literal
full-seed escape. No fixed-space vanishing or new normalization is assumed. -/
theorem plane_critical_kernel_control_escape
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z c : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hca : (cosetGraph Rg).dist c a ≤ 2)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hescape : ¬ ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg a) :
    ¬ ⁅U Rg z,Z Rg c⁆ ≤
      ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),Z Rg c⁆ ⊔
        ⁅U Rg z,Z Rg a⁆ := by
  have hb := distance_gt_two h e hz hk
  have hZV : Z Rg c ≤ V Rg a :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hca)
  have hH : ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≤ Z Rg a := by
    rw [commutator_comm]
    exact (commutator_mono hZV inf_le_right).trans
      (plane_radius_core_commutator h e hz hk u hR p.start_color)
  have hF : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),Z Rg c⁆ =
      ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ := by
    rw [←critical_moving_kernel_eq_fixed h e p]
    exact ((critical_kernel_predecessor_moving h e hz hb p).2.2 _ hbad).symm
  have hRcrit : ⁅U Rg z,Z Rg a⁆ ≤ Z Rg a := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (DistanceEight.U_le_Z Rg z)).trans
      (critical_seed_commutator_le h p)
  intro hcontrol
  apply hescape
  rw [commutator_comm,critical_predecessor_seed_movement h e hz hb p _ hbad]
  apply hcontrol.trans
  rw [hF]
  exact sup_le hH hRcrit

include h e hz hk in
/-- One literal last-edge chart carries the critical actor and both residual
actors into the same three-pair group. It identifies the original moving
kernel with the fixed space of that critical actor, without collapsing E to Q. -/
theorem plane_predecessor_cover_chart
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (T : Subgroup (FreeAmalgam Rg))
    (hT : T ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (k : FreeAmalgam Rg) (hkm : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2))) :
    let := h.relative_normal
    ∃ i : M →* FreeAmalgam Rg, Function.Injective i ∧
      i.range = stabilizer Rg z ∧
      (Rg).map i = Q Rg (p.walk.getVert (p.walk.length-1)) ∧
      (pCore 2 M).map i = Q Rg z ∧ (W₀).map i = U Rg z ∧
      let A := (Z Rg a).comap i
      let P := T.comap i
      let J := (T.map (MulAut.conj k).toMonoidHom).comap i
      A.map i = Z Rg a ∧ P.map i = T ∧
      J.map i = T.map (MulAut.conj k).toMonoidHom ∧
      A ≤ Rg ∧ P ≤ Rg ∧ J ≤ Rg ∧
      A.map π ≤ D.map (MulAut.conj u).toMonoidHom ∧
      P.map π ≤ D.map (MulAut.conj u).toMonoidHom ∧
      J.map π ≤ D.map (MulAut.conj u).toMonoidHom ∧
      (W₀ ⊓ centralizer (A : Set M)).map i = U Rg z ⊓ Q Rg a ∧
      ∀ v : Additive W₀,
        v ∈ fixedSpace (NormalElementaryQuotient.representation W₀ π
          (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)) (A.map π) ↔
          i v.toMul ∈ Q Rg a := by
  let := h.relative_normal
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let t := p.walk.getVert (p.walk.length-1)
  have hzt : Adjacent Rg z t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hpre : Adjacent Rg (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hpred := Q_le_adjacent_h Rg ht hpre
  have hAt : Z Rg a ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-1 < sourceDistance h
    omega
  have hJ : T.map (MulAut.conj k).toMonoidHom ≤
      Q Rg (p.walk.getVert (p.walk.length-2)) := by
    apply (map_mono hT).trans_eq
    exact mem_normalizer_iff_map_conj_eq.mp
      ((Q_normalized Rg _) (Ltilde_le_stabilizer _ hkm))
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := remaining_edge_coordinates h e hz p.end_color hzt
  have inside (B : Subgroup (FreeAmalgam Rg)) (hB : B ≤ Q Rg t) :
      (B.comap i).map i = B ∧ B.comap i ≤ Rg := by
    have hmap : (B.comap i).map i = B :=
      map_comap_eq_self (hB.trans (hiR ▸ map_le_range i _))
    refine ⟨hmap,?_⟩
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmap,hiR]
  obtain ⟨hA,hAr⟩ := inside _ hAt
  obtain ⟨hP,hPr⟩ := inside _ (hT.trans hpred)
  obtain ⟨hJmap,hJr⟩ := inside _ (hJ.trans hpred)
  have hfixed : (W₀ ⊓ centralizer ((Z Rg a).comap i : Set M)).map i = U Rg z ⊓ Q Rg a := by
    rw [←map_inf_centralizer_of_injective i hi,hiU,hA,
      ←critical_moving_kernel_eq_fixed h e p]
  refine ⟨i,hi,hir,hiR,hiQ,hiU,hA,hP,hJmap,hAr,hPr,hJr,
    (map_mono hAr).trans_eq hR,(map_mono hPr).trans_eq hR,
    (map_mono hJr).trans_eq hR,hfixed,?_⟩
  intro v
  rw [NormalElementaryQuotient.mem_fixedSpace_image W₀ π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)]
  constructor
  · intro hv
    have hh : i v.toMul ∈ (W₀ ⊓ centralizer ((Z Rg a).comap i : Set M)).map i :=
      mem_map_of_mem i (show (v.toMul : M) ∈ W₀ ⊓ centralizer ((Z Rg a).comap i : Set M) from ⟨v.toMul.property,hv⟩)
    rw [hfixed] at hh
    exact hh.2
  · intro hv
    have hU : i v.toMul ∈ U Rg z := hiU ▸ mem_map_of_mem i v.toMul.property
    have hh : i v.toMul ∈ (W₀ ⊓ centralizer ((Z Rg a).comap i : Set M)).map i :=
      hfixed ▸ ⟨hU,hv⟩
    obtain ⟨w,hw,he⟩ := hh
    exact (hi he) ▸ hw.2

include h e hz hk in
/-- On the same residual rotation, both the full moving cover and the fixed
hyperplane have the retained displacement. The seed attachment is removed
only by its proved centralization of the actual predecessor actors. -/
theorem plane_residual_fixed_displacements
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z c : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hindex : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (k : FreeAmalgam Rg) (hkm : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)))
    (hmove : ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ = ⁅U Rg z,Z Rg (act Rg k⁻¹ c)⁆) :
    let H := ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆
    let F := U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg))
    Z Rg (act Rg k⁻¹ c) ≤ Q Rg (p.walk.getVert (p.walk.length-2)) ∧
      ⁅Z Rg z ⊓ Q Rg a,Z Rg (act Rg k⁻¹ c)⁆ = H ∧
      ⁅Z Rg z,Z Rg (act Rg k⁻¹ c)⁆ = H ∧
      ⁅F,Z Rg c⁆ = H ∧ ⁅F,Z Rg (act Rg k⁻¹ c)⁆ = H := by
  have hb := distance_gt_two h e hz hk
  have hJ : Z Rg (act Rg k⁻¹ c) ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    rw [Z_act,inv_inv]
    apply (map_mono hbad).trans_eq
    exact mem_normalizer_iff_map_conj_eq.mp
      ((Q_normalized Rg _) (Ltilde_le_stabilizer _ hkm))
  have htrans : ⁅Z Rg z ⊓ Q Rg a,Z Rg (act Rg k⁻¹ c)⁆ =
      ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ := by
    rw [Z_act,inv_inv]
    exact plane_predecessor_slice_residual_transport h e hz hk u hR p hindex _ hbad k hkm
  refine ⟨hJ,htrans,?_,?_,?_⟩
  · exact (critical_predecessor_seed_movement h e hz hb p _ hJ).trans hmove.symm
  · rw [←critical_moving_kernel_eq_fixed h e p]
    exact ((critical_kernel_predecessor_moving h e hz hb p).2.2 _ hbad).symm
  · rw [←critical_moving_kernel_eq_fixed h e p]
    exact ((critical_kernel_predecessor_moving h e hz hb p).2.2 _ hJ).symm.trans htrans

include h e hz hk in
/-- The critical actor in a literal last-edge chart is a transposition on
both permitted covers. Its displacement is the original critical line. -/
theorem plane_small_critical_chart_actor
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4)
    (i : M →* FreeAmalgam Rg) (hi : Function.Injective i)
    (hiQ : (pCore 2 M).map i = Q Rg z)
    (hiU : (W₀).map i = U Rg z)
    (hA : ((Z Rg a).comap i).map i = Z Rg a)
    (hAr : (Z Rg a).comap i ≤ Rg) :
    let A := (Z Rg a).comap i
    (∃ τ ∈ A.map π, τ.IsSwap ∧ A.map π = zpowers τ) ∧
      (⁅W₀,A⁆).map i = ⁅Z Rg a,Z Rg z⁆ := by
  let := h.relative_normal
  let A := (Z Rg a).comap i
  have hne : ¬ A ≤ pCore 2 M := by
    intro hh
    apply p.critical.2
    have hm := map_mono (f := i) hh
    rwa [hA,hiQ] at hm
  have hn : A.map π ≠ ⊥ := by
    intro he
    exact hne (two_subgroup_le_core_of_le_extensionKernel h hz A
      (h.relative_radical.isPGroup.to_le hAr)
      (CubicAction.projection_kernel h e hz hk ▸ (map_eq_bot_iff A).mp he))
  have hQC : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a p.start_color))
  let := finite_Z Rg z
  let : Finite (U Rg z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
  have hindex : (centralizer (Z Rg a : Set (FreeAmalgam Rg))).relIndex (U Rg z) ≤ 2 :=
    ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p hsmall).2
  have hidx : (centralizer (A : Set M)).relIndex (W₀) ≤ 2 := by
    rw [←hiU,←hA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hcod : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim W₀ π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)] at hidx
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hidx
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk) (naturalRepresentation (Fin 6))
      (coverMap h e hz hk) (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (A.map π)).trans hcod
  refine ⟨PointCoreTranspositionFixed.small_image_eq_zpowers (A.map π) hn hnat,?_⟩
  rw [map_commutator,hiU,hA]
  let q := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by
        rw [(sourceGeometry h).distance_constant a p.start_color]
        exact sourceDistance_pos h) z p.end_color p.critical)
  have hqs : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk p hsmall).2]
    decide
  rw [small_critical_moving_commutator_eq h e hz hk q hqs,commutator_comm]

include h e hz hk in
/-- In the uniform-small case, the original paired selector constructs a
residual-shifted critical path. Every overlap and both generation identities
are retained. Its nonzero full reverse-kernel line is central at the original
second predecessor, but noncentral at the selected endpoint. The same chosen
orientation retains the full-seed escape and predecessor-core containment. -/
theorem plane_radius_failure_selected_escape
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hbad : V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
        ∃ c, Adjacent Rg c t ∧
          (¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) ∧
          ∃ z', ∃ s : CriticalPath Rg (sourceGeometry h) (alpha Rg) z',
          ((∀ i, s.walk.getVert i = p.walk.getVert i) ∨
           (∀ i, s.walk.getVert i = q.walk.getVert i)) ∧
          (¬ ⁅Z Rg c,Z Rg z'⁆ ≤ Z Rg (alpha Rg)) ∧
          Z Rg c ≤ Q Rg (s.walk.getVert (s.walk.length-2)) ∧
          ∃ k ∈ Ltilde Rg (s.walk.getVert (s.walk.length-2)),
            act Rg k (s.walk.getVert (s.walk.length-1)) = s.walk.getVert (s.walk.length-3) ∧
            ∃ b : CriticalPath Rg (sourceGeometry h) c (act Rg k z'),
              b.walk.getVert 1 = t ∧
              (∀ i ≤ s.walk.length-3, b.walk.getVert (i+2) = s.walk.getVert i) ∧
              Nat.card (⁅Z Rg z' ⊓ Q Rg (alpha Rg),Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
              ⁅Z Rg z' ⊓ Q Rg (alpha Rg),Z Rg c⁆ = ⁅U Rg z',Z Rg (act Rg k⁻¹ c)⁆ ∧
              ⁅Z Rg z' ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
                centralizer (stabilizer Rg (s.walk.getVert (s.walk.length-2)) : Set (FreeAmalgam Rg)) ∧
              ¬ ⁅Z Rg z' ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
                centralizer (stabilizer Rg z' : Set (FreeAmalgam Rg)) := by
  have hb := distance_gt_two h e hz hk
  have hall := fun v c t hv hvt hct =>
    plane_radius_failure_uniform_slices h e hz hk u hR p hbad (v := v) (c := c) (t := t) hv hvt hct
  have hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [(plane_radius_failure_critical_kernels h e hz hk u hR p hbad p).2.2]
    decide
  obtain ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,_⟩ :=
    remaining_small_critical_paired_kernel_selectors h e hz hk u (Or.inl hR) p hp
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hqbad : V Rg (alpha Rg) ≤ Q Rg (q.walk.getVert (q.walk.length-2)) := by
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    rw [hlen,hqverts,Q_act]
    have hV : (V Rg (alpha Rg)).map (MulAut.conj x⁻¹).toMonoidHom =
        V Rg (alpha Rg) := mem_normalizer_iff_map_conj_eq.mp
      (DistanceEight.V_normalized Rg _ ((stabilizer Rg (alpha Rg)).inv_mem hx))
    rw [←hV]
    exact map_mono hbad
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge h e hz hk hb rfl hat
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct))
  have finish {w : Vertex Rg} (s : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hsbad : Z Rg c ≤ Q Rg (s.walk.getVert (s.walk.length-2)))
      (hnot : ¬ ⁅Z Rg c,Z Rg w⁆ ≤ Z Rg (alpha Rg)) :
      ∃ k ∈ Ltilde Rg (s.walk.getVert (s.walk.length-2)),
        act Rg k (s.walk.getVert (s.walk.length-1)) = s.walk.getVert (s.walk.length-3) ∧
        ∃ b : CriticalPath Rg (sourceGeometry h) c (act Rg k w),
          b.walk.getVert 1 = t ∧
          (∀ i ≤ s.walk.length-3, b.walk.getVert (i+2) = s.walk.getVert i) ∧
          Nat.card (⁅Z Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
          ⁅Z Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆ = ⁅U Rg w,Z Rg (act Rg k⁻¹ c)⁆ ∧
          ⁅Z Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
            centralizer (stabilizer Rg (s.walk.getVert (s.walk.length-2)) : Set (FreeAmalgam Rg)) ∧
          ¬ ⁅Z Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
            centralizer (stabilizer Rg w : Set (FreeAmalgam Rg)) := by
    have hs : (Q Rg w).relIndex (Z Rg (alpha Rg)) < 4 := by
      rw [(plane_uniform_slices_predecessor_control h e hz hk u hR hall s).2.2.1]
      decide
    have hne : ⁅Z Rg w ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≠ ⊥ := by
      intro he
      rw [commutator_comm] at he
      exact hnot (small_critical_predecessor_commutator h e hz hk hb s hs
        (Z Rg c) hsbad (commutator_eq_bot_iff_le_centralizer.mp he))
    have hl : 2 < s.walk.length := s.length_eq_b ▸ hb
    have hcol : color Rg (s.walk.getVert (s.walk.length-2)) = false := by
      apply (s.vertex_color (Nat.sub_le _ _)).mpr
      have he := sourceDistance_even h
      rw [Nat.even_iff] at he ⊢
      have hh : s.walk.length = sourceDistance h := s.length_eq_b
      omega
    have hct' : Adjacent Rg (s.walk.getVert (s.walk.length-2))
        (s.walk.getVert (s.walk.length-1)) := by
      have hh := s.walk.adj_getVert_succ (i := s.walk.length-2) (by omega)
      rw [show s.walk.length-2+1=s.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have hcv : Adjacent Rg (s.walk.getVert (s.walk.length-2))
        (s.walk.getVert (s.walk.length-3)) := by
      have hh := s.walk.adj_getVert_succ (i := s.walk.length-3) (by omega)
      rw [show s.walk.length-3+1=s.walk.length-2 by omega] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    obtain ⟨k,hkm,hkt⟩ := residual_neighbor_transporter (h := h) hcol hct' hcv
    exact ⟨k,hkm,hkt,plane_uniform_nonzero_residual_path h e hz hk u hR hall
      s hat hct hsbad hne k hkm hkt⟩
  refine ⟨t,hat,r,hr,q,hqverts,hgen,hpair,hnorm,hinside,c,hct,hel,?_⟩
  rcases plane_paired_eligible_commutator_escape h e hz hk u hR p q hat hct hgen hel with hn | hn
  · exact ⟨z,p,Or.inl (fun _ => rfl),hn,hZV.trans hbad,finish p (hZV.trans hbad) hn⟩
  · exact ⟨act Rg x z,q,Or.inr (fun _ => rfl),hn,hZV.trans hqbad,finish q (hZV.trans hqbad) hn⟩

include h e hz hk in
private theorem plane_cover_commutator_obstruction
    {a z c : Vertex Rg}
    (k : FreeAmalgam Rg)
    (i : M →* FreeAmalgam Rg) (hi : Function.Injective i)
    (hiU : (W₀).map i = U Rg z)
    (hA : ((Z Rg a).comap i).map i = Z Rg a)
    (hP : ((Z Rg c).comap i).map i = Z Rg c)
    (hJ : ((Z Rg (act Rg k⁻¹ c)).comap i).map i = Z Rg (act Rg k⁻¹ c))
    (hne : ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≠ ⊥)
    (hfixed : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),Z Rg c⁆ =
      ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆)
    (hfixedJ : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),Z Rg (act Rg k⁻¹ c)⁆ =
      ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆)
    (hmovedJ : ⁅U Rg z,Z Rg (act Rg k⁻¹ c)⁆ = ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆)
    (hcontrol : ¬ ⁅U Rg z,Z Rg c⁆ ≤
      ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),Z Rg c⁆ ⊔ ⁅U Rg z,Z Rg a⁆) :
    let := h.relative_normal
    let σ := NormalElementaryQuotient.representation W₀ π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)
    let A := ((Z Rg a).comap i).map π
    let P := ((Z Rg c).comap i).map π
    let J := ((Z Rg (act Rg k⁻¹ c)).comap i).map π
    let F := fixedSpace σ A
    let H := subspaceCommutator σ F P
    H ≠ ⊥ ∧ subspaceCommutator σ F J = H ∧
      subspaceCommutator σ ⊤ J = H ∧
      ¬ subspaceCommutator σ ⊤ P ≤ H ⊔ subspaceCommutator σ ⊤ A := by
  let := h.relative_normal
  let A := (Z Rg a).comap i
  let P := (Z Rg c).comap i
  let J := (Z Rg (act Rg k⁻¹ c)).comap i
  let F := W₀ ⊓ centralizer (A : Set M)
  let H := ⁅F,P⁆
  have hFW : F ≤ W₀ := inf_le_left
  have hHW : H ≤ W₀ := (commutator_mono hFW le_rfl).trans (commutator_le_left _ _)
  have hFi : F.map i = U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) := by
    dsimp only [F,A]
    rw [←map_inf_centralizer_of_injective i hi,hiU,hA]
  have hHi : H.map i = ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ := by
    change (⁅F,P⁆).map i = _
    rw [map_commutator,hFi,hP,hfixed]
  have hFJ : ⁅F,J⁆ = H := by
    apply (map_injective hi)
    rw [map_commutator,hFi,hJ,hfixedJ,hHi]
  have hWJ : ⁅W₀,J⁆ = H := by
    apply (map_injective hi)
    rw [map_commutator,hiU,hJ,hmovedJ,hHi]
  have hn : ¬ ⁅W₀,P⁆ ≤ H ⊔ ⁅W₀,A⁆ := by
    intro hh
    apply hcontrol
    have hm := map_mono (f := i) hh
    rwa [Subgroup.map_sup,map_commutator W₀ P i,map_commutator W₀ A i,hiU,hP,hA,hHi,←hfixed] at hm
  let σ := coverAction h e hz hk
  have hspace : subgroupSpace W₀ F = fixedSpace σ (A.map π) := by
    ext v
    change ((v.toMul : M) ∈ W₀ ∧ (v.toMul : M) ∈ centralizer (A : Set M)) ↔ _
    rw [NormalElementaryQuotient.mem_fixedSpace_image W₀ π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)]
    exact and_iff_right v.toMul.property
  have htop : subgroupSpace W₀ W₀ = ⊤ := by
    ext v
    exact iff_of_true v.toMul.property (Submodule.mem_top)
  have hcomm (B C : Subgroup M) (hB : B ≤ W₀) :
      subspaceCommutator σ (subgroupSpace W₀ B) (C.map π) = subgroupSpace W₀ ⁅B,C⁆ :=
    (subgroupSpace_commutator W₀ π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) B C hB).symm
  change subspaceCommutator σ (fixedSpace σ (A.map π)) (P.map π) ≠ ⊥ ∧ _
  rw [←hspace,←htop,hcomm F P hFW,hcomm F J hFW,hcomm W₀ J le_rfl,
    hcomm W₀ P le_rfl,hcomm W₀ A le_rfl,hFJ,hWJ]
  refine ⟨?_,rfl,rfl,?_⟩
  · intro he
    apply hne
    rw [←hHi]
    have hb : H = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hv : Additive.ofMul (⟨x,hHW hx⟩ : W₀) ∈ subgroupSpace W₀ H := hx
      rw [he] at hv
      have hv0 := (Submodule.mem_bot (ZMod 2)).mp hv
      exact Subgroup.mem_bot.mpr (congrArg (fun v : Additive W₀ => (v.toMul : M)) hv0)
    rw [hb,Subgroup.map_bot]
  · intro hh
    apply hn
    rw [←subgroupSpace_sup W₀ hHW (commutator_le_left _ _)] at hh
    intro x hx
    exact hh (show Additive.ofMul (⟨x,commutator_le_left W₀ P hx⟩ : W₀) ∈
      subgroupSpace W₀ ⁅W₀,P⁆ from hx)

/-- The precise obstruction on the original full cubic cover. The two actors
are in the same marked three-pair group as the critical transposition. -/
@[expose] def PlaneCoverObstruction (u : S) : Prop :=
  let := h.relative_normal
  let σ := NormalElementaryQuotient.representation W₀ π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)
  SixCover.IsNaturalOrCore σ (MonoidHom.id S) ∧
  ∃ τ : S, ∃ P J : Subgroup S,
    τ ∈ D.map (MulAut.conj u).toMonoidHom ∧ τ.IsSwap ∧
    P ≤ D.map (MulAut.conj u).toMonoidHom ∧
    J ≤ D.map (MulAut.conj u).toMonoidHom ∧
    let F := fixedSpace σ (zpowers τ)
    let H := subspaceCommutator σ F P
    H ≠ ⊥ ∧ subspaceCommutator σ F J = H ∧
      subspaceCommutator σ ⊤ J = H ∧
      ¬ subspaceCommutator σ ⊤ P ≤ H ⊔ subspaceCommutator σ ⊤ (zpowers τ)

include h e hz hk in
/-- A trapped radius produces the exact marked-cover obstruction from the
original paired selector, retaining its orientation, residual transporter and
critical actor throughout. The control alternative is excluded on the graph. -/
theorem plane_radius_failure_cover_obstruction
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hbad : V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    PlaneCoverObstruction h e hz hk u := by
  let := h.relative_normal
  obtain ⟨t,hat,r,hr,q,hqverts,hgen,hpair,hnorm,hinside,c,hct,hel,z',s,
    hs,hescape,hsbad,k,hkm,hkt,b,hb1,hbverts,hcard,hmove,hcentral,hnoncentral⟩ :=
      plane_radius_failure_selected_escape h e hz hk u hR p hbad
  have hb := distance_gt_two h e hz hk
  have hl : 2 < s.walk.length := s.length_eq_b ▸ hb
  have hcol : color Rg (s.walk.getVert (s.walk.length-2)) = false := by
    apply (s.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : s.walk.length = sourceDistance h := s.length_eq_b
    omega
  have hlast : Adjacent Rg z' (s.walk.getVert (s.walk.length-1)) := by
    have hh := s.walk.adj_getVert_succ (i := s.walk.length-1) (by omega)
    rw [show s.walk.length-1+1=s.walk.length by omega,s.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hpre : Adjacent Rg (s.walk.getVert (s.walk.length-2))
      (s.walk.getVert (s.walk.length-1)) := by
    have hh := s.walk.adj_getVert_succ (i := s.walk.length-2) (by omega)
    rw [show s.walk.length-2+1=s.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hindex := plane_radius_failure_uniform_slices h e hz hk u hR p hbad hcol hpre hlast
  obtain ⟨hJcore,htrans,hfull,hfixed,hfixedJ⟩ :=
    plane_residual_fixed_displacements h e hz hk u hR s hindex hsbad k hkm hmove
  have hca := CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct
  have hcontrol := plane_critical_kernel_control_escape h e hz hk u hR s hca hsbad hescape
  obtain ⟨i,hi,hir,hiR,hiQ,hiU,hA,hP,hJ,hAr,hPr,hJr,hApi,hPpi,hJpi,hFi,hfix⟩ :=
    plane_predecessor_cover_chart h e hz hk u hR s (Z Rg c) hsbad k hkm
  have hZ : (Z Rg c).map (MulAut.conj k).toMonoidHom = Z Rg (act Rg k⁻¹ c) := by
    rw [Z_act,inv_inv]
  rw [hZ] at hJ hJr hJpi
  have hsmall : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [(plane_radius_failure_predecessor_control h e hz hk u hR p hbad s).2.2.1]
    decide
  obtain ⟨⟨τ,hτ,hτswap,hτeq⟩,hcrit⟩ :=
    plane_small_critical_chart_actor h e hz hk s hsmall i hi hiQ hiU hA hAr
  have hne : ⁅Z Rg z' ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≠ ⊥ := by
    intro he
    rw [he,Subgroup.card_bot] at hcard
    omega
  have hobs := plane_cover_commutator_obstruction h e hz hk k i hi hiU hA hP hJ
    hne hfixed hfixedJ hmove.symm hcontrol
  change SixCover.IsNaturalOrCore (coverAction h e hz hk) (MonoidHom.id S) ∧ _
  refine ⟨moved_subgroup_cover_model h e hz hk,τ,
    ((Z Rg c).comap i).map π,((Z Rg (act Rg k⁻¹ c)).comap i).map π,
    hApi hτ,hτswap,hPpi,hJpi,?_⟩
  simpa only [hτeq] using hobs

include h e hz hk in
/-- Radius trapping anywhere in the original component orbit has the same
finite-cover obstruction. The graph is transported by its actual action. -/
theorem plane_radius_failure_cover_obstruction_at
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hbad : V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    PlaneCoverObstruction h e hz hk u := by
  obtain ⟨f,hf⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg f⁻¹ a = alpha Rg := by
    rw [hf,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg f⁻¹ a) (act Rg f⁻¹ z),
      (∀ i, p₀.walk.getVert i = act Rg f⁻¹ (p.walk.getVert i)) ∧
      p₀.walk.length = p.walk.length :=
    ⟨p.act f⁻¹,fun i => by simp only [CriticalPath.act,actWalk_getVert],
      actWalk_length Rg f⁻¹ p.walk⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hverts,hlen⟩ := hpact
  apply plane_radius_failure_cover_obstruction h e hz hk u hR p₀
  rw [hlen,hverts,←hbase,V_act,Q_act]
  exact map_mono hbad

omit hk in
include h e hz in
/-- Whole-core assembly leaves either the original Borel branch, all actual
backward and forward paths, or the explicit finite-cover obstruction. Uniform
smallness is never treated as a trapped-radius witness. -/
theorem coreExhaustion_or_cubic_plane_cover_obstruction :
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
        ((∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
          (¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
          (∃ d, ∃ w : (cosetGraph Rg).Walk d a,
            ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
              w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
              ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          (∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
            q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a) ∧
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _)) ∨
          PlaneCoverObstruction h e hz hk u)) := by
  classical
  rcases coreExhaustion_or_cubic_plane_or_borel h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hplane | hborel⟩
  · exact Or.inl hex
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    by_cases escape : ∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
        ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))
    · left
      intro a z p
      have hprefix := reverse_prefix_of_radius_escape h e hb escape p
      refine ⟨escape _ _ p,backward_path_of_radius_escape h p (escape _ _ p) hb,hprefix,?_⟩
      obtain ⟨d,q,_,hqa⟩ := hprefix
      have hh := critical_start_not_le_second_slice h e hz hb q
      rwa [hqa] at hh
    · push Not at escape
      obtain ⟨a,z,p,hbad⟩ := escape
      exact Or.inr (plane_radius_failure_cover_obstruction_at h e hz hk u hplane p hbad)
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩

omit hk in
include h e hz in
/-- The literal C.1.32 application retains both covers, the full cubic kernel,
the Borel branch and the remaining finite obstruction. -/
theorem rankTwo_or_cubic_plane_cover_obstruction :
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
        ((∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
          (¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
          (∃ d, ∃ w : (cosetGraph Rg).Walk d a,
            ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
              w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
              ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          (∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
            q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a) ∧
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _)) ∨
          PlaneCoverObstruction h e hz hk u)) :=
  (coreExhaustion_or_cubic_plane_cover_obstruction h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
