module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourTrapped
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.RestrictedMovement
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourMoverFixed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourStabilizers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward

/-!
# Distance-four normalization for every backward critical image

The full restricted kernel of any nontrivial elementary Borel actor has
mover-fixed movement and trivial intersection with the full stabilizer
centralizer. The six-letter calculation lives in RestrictedMovement; faithful
edge charts transport it through the original cubic projection. Its kernel
is still E, with the original odd quotient E/Q.

For the overlapping distance-four paths d--a--c, a--c--z and c--z--y,
this removes the backward small-image assumption from the compatible
normalization argument. A failure line is fixed by the backward mover and,
using distinctness and generation, by the backward residual. The actual
residual transporter carries mover fixedness to c. The same-path full
fixed-subgroup comparison makes the line central at c, then at d, where
the new zero-intersection calculation contradicts its order two.

The trapped-seed argument constructs backward criticality on the selected
edges. Residual selectors now give normalization on that actual path for
every backward image, retaining their next full fixed-subgroup comparison.
Both full covers of orders sixteen and thirty-two are included.

The initial forward generation and fixed-subgroup comparison, the forward
small image and distinct movers remain explicit. Equal movers, the other
forward images and the terminal contradiction are still needed for
CoreExhaustion and the entire exceptional block reconstruction. The literal
original c.L,d.S applications are in OriginalSylowExceptional.

Internal imports reuse the checked original graph charts, critical-kernel
identities, central generation and transporter calculations; they identify
no replacement graph and remove no central attachment.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)--(5.6), (5.12)(1), printed pp.915--918,924--925;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
local notation "borel" => Theory.SpecificGroups.SymmetricSix.borel
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
private theorem borel_cover_kernel_properties
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (A P : Subgroup M) (hAP : A ≤ P) [IsElementaryAbelian 2 P]
    (hPR : P ≤ Rg) (hne : ¬ A ≤ pCore 2 M) :
    (⁅W₀ ⊓ centralizer (A : Set M),P⁆ ≤
      centralizer (borelPlane h e hz hk u : Set M)) ∧
    (∀ v ∈ ⁅W₀ ⊓ centralizer (A : Set M),P⁆, v ∈ center M → v=1) := by
  let := h.relative_normal
  let F := W₀ ⊓ centralizer (A : Set M)
  let H := ⁅F,P⁆
  have hHW : H ≤ W₀ := (commutator_mono inf_le_left le_rfl).trans (commutator_le_left _ _)
  have hker := CubicAction.moved_projection_kernel h e hz hk
  have hnA : A.map π ≠ ⊥ := by
    intro he
    apply hne
    rw [←cubic_radical_projection_kernel h e hz hk]
    exact le_inf ((map_eq_bot_iff A).mp he) (hAP.trans hPR)
  have hP : P.map π ≤ borel.map (MulAut.conj u).toMonoidHom := (map_mono hPR).trans_eq hR
  let : IsElementaryAbelian 2 (P.map π) := IsElementaryAbelian.map π
  have hh := SixCover.BorelKernel.kernel_properties (coverAction h e hz hk)
    (moved_subgroup_cover_model h e hz hk) u (A.map π) (P.map π)
    (map_mono hAP) hP hnA
  have hF : subgroupSpace W₀ F = fixedSpace (coverAction h e hz hk) (A.map π) := by
    ext v
    change ((v.toMul : M) ∈ W₀ ∧ (v.toMul : M) ∈ centralizer (A : Set M)) ↔ _
    simp only [v.toMul.property,true_and]
    exact (mem_fixedSpace_image W₀ π (CubicEven.projection_surjective h e hz hk) hker A v).symm
  have hH : subgroupSpace W₀ H = subspaceCommutator (coverAction h e hz hk)
      (fixedSpace (coverAction h e hz hk) (A.map π)) (P.map π) := by
    rw [subgroupSpace_commutator W₀ π (CubicEven.projection_surjective h e hz hk) hker F P inf_le_left,hF]
  rw [←hH,←borelPlane_image h e hz hk u hR] at hh
  constructor
  · intro v hv
    let w : Additive W₀ := Additive.ofMul ⟨v,hHW hv⟩
    exact (mem_fixedSpace_image W₀ π (CubicEven.projection_surjective h e hz hk)
      hker (borelPlane h e hz hk u) w).mp (hh.1 hv)
  · intro v hv hc
    let w : Additive W₀ := Additive.ofMul ⟨v,hHW hv⟩
    have hf : w ∈ fixedSpace (coverAction h e hz hk) ((⊤ : Subgroup M).map π) :=
      (mem_fixedSpace_image W₀ π (CubicEven.projection_surjective h e hz hk)
        hker ⊤ w).mpr (fun m _ => mem_center_iff.mp hc m)
    have hfix (g : S) : coverAction h e hz hk g w=w := by
      obtain ⟨m,rfl⟩ := CubicEven.projection_surjective h e hz hk g
      exact hf ⟨π m,mem_map_of_mem π (mem_top m)⟩
    have he := hh.2 w hv hfix
    exact congrArg (fun w : Additive W₀ => (w.toMul : M)) he

include h e hz hk in
/-- For an arbitrary nontrivial elementary edge image, the full restricted
kernel movement is fixed by its proper mover and has no nonidentity
stabilizer-central element. Both entire covers are retained. -/
theorem borel_edge_kernel_properties
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t)
    (A P : Subgroup (FreeAmalgam Rg)) (hAP : A ≤ P) [IsElementaryAbelian 2 P]
    (hPT : P ≤ Q Rg t) (hne : ¬ A ≤ Q Rg c) :
    (⁅U Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),P⁆ ≤
      centralizer (edgeOffenderJoin c t : Set (FreeAmalgam Rg))) ∧
    (∀ v ∈ ⁅U Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),P⁆,
      v ∈ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) → v=1) := by
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := remaining_edge_coordinates h e hz hc hct
  have hPG : P ≤ stabilizer Rg c := hPT.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hPm : (P.comap i).map i = P := map_comap_eq_self (hPG.trans_eq hir.symm)
  have hAm : (A.comap i).map i = A := map_comap_eq_self ((hAP.trans hPG).trans_eq hir.symm)
  let : IsElementaryAbelian 2 (P.comap i) := IsElementaryAbelian.comap_of_injective i hi P
  have hPR : P.comap i ≤ Rg := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hPm,hiR]
  have hn : ¬ A.comap i ≤ pCore 2 M := by
    intro hh
    apply hne
    have hm := map_mono (f := i) hh
    rwa [hAm,hiQ] at hm
  have hh := borel_cover_kernel_properties h e hz hk u hR (A.comap i) (P.comap i)
    (comap_mono hAP) hPR hn
  have hmap : (⁅W₀ ⊓ centralizer (A.comap i : Set M),P.comap i⁆).map i =
      ⁅U Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),P⁆ := by
    rw [map_commutator,←map_inf_centralizer_of_injective i hi,hiU,hAm,hPm]
  constructor
  · have hm := congrArg (Subgroup.map i) (commutator_eq_bot_iff_le_centralizer.mpr hh.1)
    rw [map_commutator,hmap,Subgroup.map_bot] at hm
    rw [remaining_join_in_chart h e hz hk u (Or.inr hR) hc hct i hi hiR hiQ hiU]
    exact commutator_eq_bot_iff_le_centralizer.mp hm
  · intro v hv hvc
    rw [←hmap] at hv
    obtain ⟨m,hm,rfl⟩ := hv
    have hmC : m ∈ center M := by
      apply mem_center_iff.mpr
      intro k
      apply hi
      simp only [map_mul]
      exact hvc (i k) (hir ▸ ⟨k,rfl⟩)
    simpa only [map_one] using congrArg i (hh.2 m hm hmC)

include h e hz hk in
/-- On the actual overlapping distance-four paths, the full kernel
commutator is mover-fixed and has trivial intersection with the backward
stabilizer centralizer, with no backward critical-image bound. -/
theorem borel_four_kernel_properties
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a) :
    (⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆ ≤
      centralizer (edgeOffenderJoin d (q.walk.getVert 1) : Set (FreeAmalgam Rg))) ∧
    (∀ v ∈ ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆,
      v ∈ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) → v=1) := by
  let c := p.walk.getVert 2
  let t := q.walk.getVert 1
  let F := Z Rg z ⊓ Q Rg a
  let P := F ⊔ Z Rg c
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
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
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hFt : F ≤ Q Rg t := inf_le_right.trans (Q_le_adjacent_h Rg ht hat)
  have hZc : Z Rg z ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    change 4 - 2 < sourceDistance h
    omega
  have hAt : Z Rg c ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ q.end_color)
    rw [(sourceGeometry h).distance_constant _ q.end_color,SimpleGraph.dist_comm,q.dist_end,hql]
    change 4 - 1 < sourceDistance h
    omega
  have hAC : Z Rg c ≤ centralizer (F : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c q.end_color)).trans
      (centralizer_le (inf_le_left.trans hZc))
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c q.end_color
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.sup_of_le_centralizer hAC
  let qr := CriticalPath.ofPair (geometry := sourceGeometry h) q.end_color (reverse_pair h e q)
  have hh := borel_edge_kernel_properties h e hz hk u hR q.start_color hdt
    (Z Rg c) P le_sup_right (sup_le hFt hAt) qr.critical.2
  have hAF : Z Rg c ≤ centralizer
      (U Rg d ⊓ centralizer (Z Rg c : Set (FreeAmalgam Rg)) : Set _) :=
    le_centralizer_iff.mpr inf_le_right
  dsimp only [P] at hh
  rw [commutator_comm,commutator_sup_fixed F (Z Rg c) _
    (hAC.trans (Subgroup.centralizer_le_normalizer _)) hAF,commutator_comm,
    ←critical_moving_kernel_eq_fixed h e qr] at hh
  rw [(four_overlapping_kernel_pair h e hz hk hb p q hqa).2.2.1] at hh
  exact hh

include h e hz hk in
private theorem failure_backward_residual_central
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _))
    (hne : edgeOffenderJoin a (q.walk.getVert 1) ≠
      edgeOffenderJoin d (q.walk.getVert 1)) :
    ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆ ≤
      centralizer (Ltilde Rg a : Set (FreeAmalgam Rg)) := by
  let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆
  have hb := borel_distance_eq_four h e hz hk u hR
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hdt : Adjacent Rg d (q.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent Rg a (q.walk.getVert 1) := by
    have hh := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
    change Adjacent Rg (q.walk.getVert 2) (q.walk.getVert 1) at hh
    simpa only [hqa] using hh
  have hsplit := ((borel_four_kernel_omega_control h e hz hk u hR p q hqa hp).2
    hnorm a p.start_color).1
  have hcore : ¬ Q Rg a ≤ edgeOffenderJoin d (q.walk.getVert 1) := by
    intro hc
    exact borel_opposite_containing_core_nonsplit h e hz hk u hR
      p.start_color q.start_color hat hdt hne hc hsplit
  have hres := (borel_opposite_generation_of_core_not_le h e hz hk u hR
    p.start_color q.start_color hat hdt (Z Rg z) hgen hcore).2
  have hxz := ((borel_four_kernel_omega_control h e hz hk u hR p q hqa hp).2
    hnorm z p.end_color).2
  have hHJ : H ≤ centralizer (edgeOffenderJoin d (q.walk.getVert 1) : Set (FreeAmalgam Rg)) := by
    dsimp only [H]
    rw [hxz]
    exact (borel_four_kernel_properties h e hz hk u hR p q hqa).1
  have hHZ : H ≤ Z Rg z :=
    (borel_four_kernel_failure_midpoint h e hz hk u hR p q hqa hp hnorm).trans inf_le_right
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hHZfix : H ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) := hHZ.trans (Z Rg z).le_centralizer
  apply le_centralizer_iff.mpr
  exact hres.trans (sup_le (le_centralizer_iff.mp hHJ) (le_centralizer_iff.mp hHZfix))

include h e hz hk in
private theorem failure_middle_mover_fixed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ Ltilde Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d)
    (hxt : act Rg x (p.walk.getVert 1) = q.walk.getVert 1)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _))
    (hne : edgeOffenderJoin a (q.walk.getVert 1) ≠
      edgeOffenderJoin d (q.walk.getVert 1)) :
    ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆ ≤
      centralizer (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) :
        Set (FreeAmalgam Rg)) := by
  let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆
  have hres := failure_backward_residual_central h e hz hk u hR
    p q hqa hgen hp hnorm hne
  have hxz := ((borel_four_kernel_omega_control h e hz hk u hR p q hqa hp).2
    hnorm z p.end_color).2
  have hJd : H ≤ centralizer (edgeOffenderJoin d (q.walk.getVert 1) : Set (FreeAmalgam Rg)) := by
    dsimp only [H]
    rw [hxz]
    exact (borel_four_kernel_properties h e hz hk u hR p q hqa).1
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hJ := remaining_edge_join_act h e hz hk u (Or.inr hR) q.end_color hct x
  rw [hxd,hxt] at hJ
  intro v hv j hj
  have hvx : (MulAut.conj x⁻¹) v = v := by
    change x⁻¹*v*(x⁻¹)⁻¹=v
    rw [hres hv x⁻¹ ((Ltilde Rg a).inv_mem hx),mul_inv_cancel_right]
  have hjd : (MulAut.conj x⁻¹) j ∈ edgeOffenderJoin d (q.walk.getVert 1) := by
    rw [hJ]
    have hh := mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom hj
    simpa only [MulEquiv.coe_toMonoidHom] using hh
  apply (MulAut.conj x⁻¹).injective
  simpa only [map_mul,hvx] using hJd hv ((MulAut.conj x⁻¹) j) hjd

include h e hz hk in
/-- The compatible distinct-mover normalization of (5.12)(1) for every
backward critical image. The forward small image, actual residual
transporter and same-path full fixed-subgroup comparison remain explicit. -/
theorem borel_four_compatible_all_backward_images_normalized
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hgen' : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ Ltilde Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d)
    (hxt : act Rg x (p.walk.getVert 1) = q.walk.getVert 1)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1))
    (hfixed : Z Rg (p.walk.getVert 3) ⊓ centralizer
        (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) :
    X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _) := by
  by_contra hn
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hab : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcb : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hxG : x ∈ stabilizer Rg a := Ltilde_le_stabilizer a hx
  have hJa := remaining_edge_join_act h e hz hk u (Or.inr hR) p.start_color hab x
  have hJc := remaining_edge_join_act h e hz hk u (Or.inr hR) q.end_color hcb x
  rw [show act Rg x a = a from hxG,hxt] at hJa
  rw [hxd,hxt] at hJc
  have hne' : edgeOffenderJoin a (q.walk.getVert 1) ≠
      edgeOffenderJoin d (q.walk.getVert 1) := by
    intro he
    apply hne
    exact (map_injective (MulAut.conj x⁻¹).injective)
      (hJa.symm.trans (he.trans hJc))
  have hHt := (borel_four_failure_middle_central h e hz hk u hR
    p q hqa r hrz hgen hp hn hne).2
  have hHJ := failure_middle_mover_fixed h e hz hk u hR
    p q hqa hgen' x hx hxd hxt hp hn hne'
  let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆
  have hHC : H ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) :=
    (le_inf hHt hHJ).trans hfixed
  have hHL := failure_backward_residual_central h e hz hk u hR p q hqa hgen' hp hn hne'
  have hHd : H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) := by
    have hh := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hHC).trans
      (map_centralizer_le_centralizer_image _ _)
    rw [terminal_fixed_map H (Ltilde Rg a) hHL ((Ltilde Rg a).inv_mem hx)] at hh
    change H ≤ centralizer ((stabilizer Rg (p.walk.getVert 2)).map
      (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam Rg)) at hh
    rwa [←stabilizer_act,hxd] at hh
  have hcontrol := borel_four_kernel_omega_control h e hz hk u hR p q hqa hp
  have hxz := (hcontrol.2 hn z p.end_color).2
  have hline := borel_four_kernel_failure_line h e hz hk u hR p q hqa hp
    (fun hh => hn (hcontrol.1.mpr hh))
  have hcard : Nat.card H=2 := by simpa only [H,hxz] using hline.1
  have hbot : H=⊥ := by
    apply le_bot_iff.mp
    intro v hv
    have hv' : v ∈ ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆ := by
      simpa only [H,hxz] using hv
    exact (borel_four_kernel_properties h e hz hk u hR p q hqa).2 v hv' (hHd hv)
  rw [hbot,card_bot] at hcard
  omega
include h e hz hk in
/-- Selected distinct movers give normalization without a backward
criticality premise or a backward image-order bound. -/
theorem borel_four_selected_kernel_normalized
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d t y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (hgen' : Q Rg t ⊔ Z Rg z = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ Ltilde Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d)
    (hxt : act Rg x (p.walk.getVert 1) = t)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1))
    (hfixed : Z Rg (p.walk.getVert 3) ⊓ centralizer
        (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) :
    X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _) := by
  obtain ⟨q,hqt,hverts⟩ := borel_four_compatible_distinct_backward_path h e hz hk u hR
    p r hrz hgen hat hdt hgen' x hx hxd hxt hp hne hfixed
  have hqa : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hverts 0 (by decide)
  exact borel_four_compatible_all_backward_images_normalized h e hz hk u hR p q hqa r hrz hgen
    (hqt.symm ▸ hgen') x hx hxd (hxt.trans hqt.symm) hp hne hfixed

include h e hz hk in
/-- Construct the backward source choices from the residual selectors.
Their full fixed-subgroup comparison is retained for the next overlapping
step, and every backward image gives normalization on these very choices.
The initial forward comparison remains explicit. -/
theorem borel_four_distinct_normalized_backward_selection
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1))
    (hfixed : Z Rg (p.walk.getVert 3) ⊓ centralizer
        (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) :
    ∃ d t, ∃ x ∈ Ltilde Rg a,
      act Rg x (p.walk.getVert 2) = d ∧ act Rg x (p.walk.getVert 1) = t ∧
      Adjacent Rg a t ∧ Adjacent Rg d t ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg a ∧
      (Z Rg (p.walk.getVert 1) ⊓ centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
        q.walk.getVert 1 = t ∧ (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        X Rg z ≤ normalizer
            (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
              Subgroup (FreeAmalgam Rg)) : Set _) := by
  obtain ⟨t,hat,_,_,x,hx,hxt,_,_,hgen',_,hfix,_,_,_⟩ :=
    borel_small_residual_selectors h e hz hk u hR p hp
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcb : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  let d := act Rg x (p.walk.getVert 2)
  have hdt : Adjacent Rg d t := by
    rw [←hxt]
    exact (adjacent_act_iff Rg x _ _).mpr hcb
  obtain ⟨q,hqt,hover⟩ := borel_four_compatible_distinct_backward_path h e hz hk u hR
    p r hrz hgen hat hdt hgen' x hx rfl hxt hp hne hfixed
  refine ⟨d,t,x,hx,rfl,hxt,hat,hdt,hgen',hfix,q,hqt,hover,?_⟩
  have hqa : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
  exact borel_four_compatible_all_backward_images_normalized h e hz hk u hR p q hqa r hrz hgen
    (hqt.symm ▸ hgen') x hx rfl (hxt.trans hqt.symm) hp hne hfixed

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
