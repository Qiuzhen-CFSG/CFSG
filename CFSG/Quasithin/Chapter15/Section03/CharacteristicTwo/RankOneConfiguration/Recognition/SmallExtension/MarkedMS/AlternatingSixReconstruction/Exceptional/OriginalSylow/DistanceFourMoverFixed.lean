module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourAttachments
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer
import all CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneComparison
public import Theory.SpecificGroups.SymmetricSix.TranspositionCubic.CoreMovement

/-!
# Restricted-kernel fixedness on the original distance-four Borel paths

In the six-letter Borel, an involution commuting with a transposition moves
its fixed augmentation vectors only inside the proper plane mover's fixed
space. A small finite certificate proves the coordinate statement. The
literal core-to-natural quotient carries it to the sixteen-element cover;
no central attachment is removed from the thirty-two-element cover.

The full cubic action and faithful edge charts transport this calculation
to the original graph. On overlapping distance-four paths with a small
backward critical image, the whole kernel commutator is fixed by the
backward proper Thompson mover. If normalization fails and the backward
movers differ, central generation excludes core containment, and opposite
mover generation makes the failure line central under the backward residual.
A transporter in that residual carries fixedness to the middle mover.

With the fixed-subgroup comparison of MS93 (5.5)(b) on these same paths,
the failure line is central in the entire middle stabilizer, contradicting
the existing noncentrality theorem. This proves the compatible distinct-mover,
two-small-image normalization clause of (5.12)(1) on both covers. The
compatible selections, equal-mover and larger-image cases, and the subsequent
terminal contradiction still remain. CoreExhaustion and reconstruction are
not asserted. OriginalSylowExceptional supplies the literal c.L,d.S uses.

The internal imports reuse the cubic action, Borel coordinates, edge charts
and the general fixed-factor commutator identity. They neither identify a
replacement graph nor change the original projection kernel E or its odd
quotient E/Q.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(b,c) and (5.12)(1), printed pp.915--917,924--925;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelKernelModel
local notation "ρ" => coreRepresentation (Fin 6)
local notation "σ" => naturalRepresentation (Fin 6)
local notation "borel" => Theory.SpecificGroups.SymmetricSix.borel

private theorem fixed_displacement_cert : ∀ i j : Fin 16,
    (BorelCalculation.words i).cycleType = {2} →
    (BorelCalculation.words j)^2 = 1 →
    BorelCalculation.words i * BorelCalculation.words j =
      BorelCalculation.words j * BorelCalculation.words i →
    ∀ v : Fin 6 → ZMod 2, (∑ k, v k) = 0 →
    representation (Fin 6) (BorelCalculation.words i) v = v →
    ∀ k : Fin 8, representation (Fin 6) (dWords k)
        (representation (Fin 6) (BorelCalculation.words j) v - v) =
      representation (Fin 6) (BorelCalculation.words j) v - v := by
  decide +kernel

private theorem core_fixed_displacement (t g : S)
    (ht : t ∈ borel) (hs : t.IsSwap) (hg : g ∈ borel) (h2 : g^2=1)
    (hc : Commute t g) (v : core (Fin 6)) (hv : ρ t v = v) :
    ρ g v-v ∈ fixedSpace ρ D := by
  obtain ⟨i,rfl⟩ := BorelCalculation.words_complete t ht
  obtain ⟨j,rfl⟩ := BorelCalculation.words_complete g hg
  intro a
  let s : S := a.val
  have ha : s ∈ D := a.property
  rw [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] at ha
  obtain ⟨k,hk⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) s).mp ha
  apply Subtype.ext
  change representation (Fin 6) s
    (representation (Fin 6) (BorelCalculation.words j) v.val-v.val) = _
  rw [←hk]
  exact fixed_displacement_cert i j (Equiv.Perm.isSwap_iff_cycleType.mp hs) h2 hc.eq
    v.val ((mem_core (Fin 6) v.val).mp v.property) (congrArg Subtype.val hv) k

private theorem natural_fixed_displacement (t g : S)
    (ht : t ∈ borel) (hs : t.IsSwap) (hg : g ∈ borel) (h2 : g^2=1)
    (hc : Commute t g) (v : natural (Fin 6)) (hv : σ t v = v) :
    σ g v-v ∈ fixedSpace σ D := by
  obtain ⟨w,rfl⟩ := coreToNatural_surjective v
  have hw := TranspositionCubic.core_fixed_of_natural_fixed t hs w hv
  have hd := core_fixed_displacement t g ht hs hg h2 hc w hw
  intro a
  have hh := congrArg (coreToNatural (Fin 6)) (hd a)
  simpa only [MonoidHom.comp_apply,map_sub,coreToNatural_equivariant] using hh

private theorem cover_fixed_displacement
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (τ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore τ (MonoidHom.id S))
    (t g : S) (ht : t ∈ borel) (hs : t.IsSwap)
    (hg : g ∈ borel) (h2 : g^2=1) (hc : Commute t g)
    (v : Y) (hv : τ t v = v) : τ g v-v ∈ fixedSpace τ D := by
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
  · simp only [MonoidHom.id_apply] at hE
    have hf : σ t (E v) = E v := by rw [←hE,hv]
    have hh := natural_fixed_displacement t g ht hs hg h2 hc (E v) hf
    intro a
    apply E.injective
    simpa only [MonoidHom.comp_apply,hE,map_sub,MonoidHom.id_apply] using hh a
  · simp only [MonoidHom.id_apply] at hE
    have hf : ρ t (E v) = E v := by rw [←hE,hv]
    have hh := core_fixed_displacement t g ht hs hg h2 hc (E v) hf
    intro a
    apply E.injective
    simpa only [MonoidHom.comp_apply,hE,map_sub,MonoidHom.id_apply] using hh a

private theorem cover_conjugate_fixed_displacement
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (τ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore τ (MonoidHom.id S))
    (u t g : S) (ht : t ∈ borel.map (MulAut.conj u).toMonoidHom) (hs : t.IsSwap)
    (hg : g ∈ borel.map (MulAut.conj u).toMonoidHom) (h2 : g^2=1) (hc : Commute t g)
    (v : Y) (hv : τ t v = v) :
    τ g v-v ∈ fixedSpace τ (D.map (MulAut.conj u).toMonoidHom) := by
  obtain ⟨t₀,ht₀,rfl⟩ := ht
  obtain ⟨g₀,hg₀,rfl⟩ := hg
  have hs₀ : t₀.IsSwap := by
    have hh : IsConj t₀ ((MulAut.conj u) t₀) := isConj_iff.mpr ⟨u,rfl⟩
    exact Equiv.Perm.isSwap_iff_cycleType.mpr
      ((Equiv.Perm.isConj_iff_cycleType_eq.mp hh).trans (Equiv.Perm.isSwap_iff_cycleType.mp hs))
  change ((MulAut.conj u) g₀)^2=1 at h2
  change Commute ((MulAut.conj u) t₀) ((MulAut.conj u) g₀) at hc
  have h2₀ : g₀^2=1 := (MulAut.conj u).injective (by simpa only [map_pow,map_one] using h2)
  have hc₀ : Commute t₀ g₀ := by
    change t₀*g₀=g₀*t₀
    apply (MulAut.conj u).injective
    simpa only [map_mul] using hc.eq
  have hi (w : Y) : τ u⁻¹ (τ u w) = w := by
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hr (w : Y) : τ u (τ u⁻¹ w) = w := by
    rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  have hfv : τ t₀ (τ u⁻¹ v) = τ u⁻¹ v := by
    have hh := congrArg (τ u⁻¹) hv
    change τ u⁻¹ (τ (u*t₀*u⁻¹) v) = _ at hh
    simpa only [map_mul,Module.End.mul_apply,hi] using hh
  have hh := cover_fixed_displacement τ hm t₀ g₀ ht₀ hs₀ hg₀ h2₀ hc₀ (τ u⁻¹ v) hfv
  intro a
  obtain ⟨d,hd,he⟩ := a.property
  have heq := congrArg (τ u) (hh ⟨d,hd⟩)
  change τ a.val (τ (u*g₀*u⁻¹) v-v) = _
  rw [←he]
  change τ (u*d*u⁻¹) (τ (u*g₀*u⁻¹) v-v) = τ (u*g₀*u⁻¹) v-v
  simpa only [MonoidHom.comp_apply,Subgroup.coe_subtype,map_mul,Module.End.mul_apply,map_sub,hi,hr] using heq

/-- Restricted transposition-kernel displacement by an elementary Borel
actor is fixed by the proper plane mover, on either entire cover. -/
private theorem cover_kernel_fixed
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (τ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore τ (MonoidHom.id S))
    (u t : S) (ht : t ∈ borel.map (MulAut.conj u).toMonoidHom) (hs : t.IsSwap)
    (P : Subgroup S) (hP : P ≤ borel.map (MulAut.conj u).toMonoidHom)
    (h2 : ∀ g ∈ P, g^2=1) (hc : ∀ g ∈ P, Commute t g) :
    subspaceCommutator τ (fixedSpace τ (zpowers t)) P ≤
      fixedSpace τ (D.map (MulAut.conj u).toMonoidHom) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,v,hv,rfl⟩
  exact cover_conjugate_fixed_displacement τ hm u t g ht hs (hP hg) (h2 g hg)
    (hc g hg) v ((mem_fixedSpace_zpowers_iff τ t v).mp hv)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelKernelModel

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
private theorem borel_cover_kernel_mover_fixed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (A P : Subgroup M) (hAP : A ≤ P) [IsElementaryAbelian 2 P]
    (hPR : P ≤ Rg) (hne : ¬ A ≤ pCore 2 M)
    (hidx : (centralizer (A : Set M)).relIndex W₀ ≤ 2) :
    ⁅W₀ ⊓ centralizer (A : Set M),P⁆ ≤
      centralizer (borelPlane h e hz hk u : Set M) := by
  let := h.relative_normal
  let F := W₀ ⊓ centralizer (A : Set M)
  let H := ⁅F,P⁆
  have hHW : H ≤ W₀ := (commutator_mono inf_le_left le_rfl).trans (commutator_le_left _ _)
  have hker := CubicAction.moved_projection_kernel h e hz hk
  have hs : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact (cubic_cover_movement_bounds h e hz hk A).1.trans hidx
  have hnA : A.map π ≠ ⊥ := by
    intro he
    apply hne
    rw [←cubic_radical_projection_kernel h e hz hk]
    exact le_inf ((map_eq_bot_iff A).mp he) (hAP.trans hPR)
  obtain ⟨t,ht,hts,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers (A.map π) hnA hs
  have hP : P.map π ≤ borel.map (MulAut.conj u).toMonoidHom := (map_mono hPR).trans_eq hR
  let : IsElementaryAbelian 2 (P.map π) := IsElementaryAbelian.map π
  have htp : t ∈ P.map π := map_mono hAP ht
  have hc (g : S) (hg : g ∈ P.map π) : Commute t g := by
    exact congrArg Subtype.val (mul_comm (⟨t,htp⟩ : P.map π) ⟨g,hg⟩)
  have hh := BorelKernelModel.cover_kernel_fixed (coverAction h e hz hk)
    (moved_subgroup_cover_model h e hz hk) u t (hP htp) hts (P.map π) hP
    (fun g hg => elemPow_eq_one_of_isElementaryAbelian g hg) hc
  have hF : subgroupSpace W₀ F = fixedSpace (coverAction h e hz hk) (A.map π) := by
    ext v
    change ((v.toMul : M) ∈ W₀ ∧ (v.toMul : M) ∈ centralizer (A : Set M)) ↔ _
    simp only [v.toMul.property,true_and]
    exact (mem_fixedSpace_image W₀ π (CubicEven.projection_surjective h e hz hk) hker A v).symm
  have hH : subgroupSpace W₀ H = subspaceCommutator (coverAction h e hz hk)
      (fixedSpace (coverAction h e hz hk) (A.map π)) (P.map π) := by
    rw [subgroupSpace_commutator W₀ π (CubicEven.projection_surjective h e hz hk) hker F P inf_le_left,hF]
  rw [←he,←hH,←borelPlane_image h e hz hk u hR] at hh
  intro v hv
  let w : Additive W₀ := Additive.ofMul ⟨v,hHW hv⟩
  exact (mem_fixedSpace_image W₀ π (CubicEven.projection_surjective h e hz hk)
    hker (borelPlane h e hz hk u) w).mp (hh hv)

include h e hz hk in
/-- On the original full moving cover, an elementary edge actor containing
 a nontrivial small actor moves its fixed kernel only inside the fixed
 subgroup of the proper Thompson mover. -/
theorem borel_edge_kernel_mover_fixed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t)
    (A P : Subgroup (FreeAmalgam Rg)) (hAP : A ≤ P) [IsElementaryAbelian 2 P]
    (hPT : P ≤ Q Rg t) (hne : ¬ A ≤ Q Rg c)
    (hidx : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2) :
    ⁅U Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),P⁆ ≤
      centralizer (edgeOffenderJoin c t : Set (FreeAmalgam Rg)) := by
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
  have hiA : (centralizer (A.comap i : Set M)).relIndex W₀ ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,
      ←map_inf_centralizer_of_injective i hi,hiU,hAm,inf_relIndex_left]
    exact hidx
  have hh := commutator_eq_bot_iff_le_centralizer.mpr
    (borel_cover_kernel_mover_fixed h e hz hk u hR (A.comap i) (P.comap i)
      (comap_mono hAP) hPR hn hiA)
  have hm := congrArg (Subgroup.map i) hh
  rw [map_commutator,map_commutator,←map_inf_centralizer_of_injective i hi,
    hiU,hAm,hPm,Subgroup.map_bot] at hm
  rw [remaining_join_in_chart h e hz hk u (Or.inr hR) hc hct i hi hiR hiQ hiU]
  exact commutator_eq_bot_iff_le_centralizer.mp hm

include h e hz hk in
/-- On the actual overlapping distance-four paths, the full kernel
 commutator is fixed by the backward endpoint's proper mover. The backward
 critical image is small; no failure or order-sixteen assumption is used. -/
theorem borel_four_kernel_backward_mover_fixed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hq : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4) :
    ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆ ≤
      centralizer (edgeOffenderJoin d (q.walk.getVert 1) : Set (FreeAmalgam Rg)) := by
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
  have hidx : (centralizer (Z Rg c : Set (FreeAmalgam Rg))).relIndex (U Rg d) ≤ 2 := by
    let := finite_Z Rg d
    let : Finite (U Rg d) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z Rg d)) (inclusion_injective _)
    have hQC : Q Rg c ≤ centralizer (Z Rg c : Set (FreeAmalgam Rg)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c q.end_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg d) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk q hq).1
  have hh := borel_edge_kernel_mover_fixed h e hz hk u hR q.start_color hdt
    (Z Rg c) P le_sup_right (sup_le hFt hAt) qr.critical.2 hidx
  have hAF : Z Rg c ≤ centralizer
      (U Rg d ⊓ centralizer (Z Rg c : Set (FreeAmalgam Rg)) : Set _) :=
    le_centralizer_iff.mpr inf_le_right
  change ⁅U Rg d ⊓ centralizer (Z Rg c : Set (FreeAmalgam Rg)),F ⊔ Z Rg c⁆ ≤ _ at hh
  rw [commutator_comm,commutator_sup_fixed F (Z Rg c) _
    (hAC.trans (Subgroup.centralizer_le_normalizer _)) hAF,commutator_comm,
    ←critical_moving_kernel_eq_fixed h e qr] at hh
  rw [(four_overlapping_kernel_pair h e hz hk hb p q hqa).2.2.1] at hh
  exact hh

include h e hz hk in
/-- A failed full-omega normalization has a failure line fixed by the
 backward proper mover, including the full thirty-two cover. -/
theorem borel_four_failure_backward_mover_fixed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _)) :
    ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆ ≤
      centralizer (edgeOffenderJoin d (q.walk.getVert 1) : Set (FreeAmalgam Rg)) := by
  have hxz := ((borel_four_kernel_omega_control h e hz hk u hR p q hqa hp).2
    hnorm z p.end_color).2
  rw [hxz]
  exact borel_four_kernel_backward_mover_fixed h e hz hk u hR p q hqa hq

include h e hz hk in
/-- Distinct backward movers make the failure line central under the
 actual backward residual. Central generation is derived from the same
 failure, so the core-containment alternative cannot intervene. -/
theorem borel_four_failure_backward_residual_central
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4)
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
  have hHJ := borel_four_failure_backward_mover_fixed h e hz hk u hR p q hqa hp hq hnorm
  have hHZ : H ≤ Z Rg z :=
    (borel_four_kernel_failure_midpoint h e hz hk u hR p q hqa hp hnorm).trans inf_le_right
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hHZfix : H ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) := hHZ.trans (Z Rg z).le_centralizer
  apply le_centralizer_iff.mpr
  exact hres.trans (sup_le (le_centralizer_iff.mp hHJ) (le_centralizer_iff.mp hHZfix))

include h e hz hk in
/-- The actual backward residual transporter carries the fixed proper
 mover back to the middle vertex. No equality of graphs or attachment
 quotient is used; the failure line itself is fixed by that transporter. -/
theorem borel_four_failure_middle_mover_fixed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ Ltilde Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d)
    (hxt : act Rg x (p.walk.getVert 1) = q.walk.getVert 1)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _))
    (hne : edgeOffenderJoin a (q.walk.getVert 1) ≠
      edgeOffenderJoin d (q.walk.getVert 1)) :
    ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆ ≤
      centralizer (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) :
        Set (FreeAmalgam Rg)) := by
  let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆
  have hres := borel_four_failure_backward_residual_central h e hz hk u hR
    p q hqa hgen hp hq hnorm hne
  have hJd := borel_four_failure_backward_mover_fixed h e hz hk u hR p q hqa hp hq hnorm
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
/-- The distinct-mover, two-small-image case of MS93 (5.12)(1), with the
 literal compatible fixed-subgroup comparison from (5.5)(b). It covers
 both full moving modules. The comparison must be supplied on these same
 paths; it is not inferred for arbitrary critical paths. -/
theorem borel_four_compatible_kernel_normalized
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
    (hq : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4)
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
  have hHJ := borel_four_failure_middle_mover_fixed h e hz hk u hR
    p q hqa hgen' x hx hxd hxt hp hq hn hne'
  exact borel_four_failure_not_central_middle h e hz hk u hR
    p q hqa hgen' x hxG hxd hp hq hn hne' ((le_inf hHt hHJ).trans hfixed)

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
