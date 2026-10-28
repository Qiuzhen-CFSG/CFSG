module
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicAttachmentMovement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicMidpointCore
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardRigidity
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits
public import Theory.Representation.BinaryOffender.CommutingPerfectSupports
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The critical attachment plane in the full cubic augmentation cover

In the binary augmentation module, a point core moves the fixed hyperplane
of its unique transposition into vectors with zero coordinate on that duad.
The transposition's own displacement line meets this subspace trivially.
The proof tracks a coordinate and the three point-core generators; it does
not quotient out the constant vector or enumerate the module.

The original cubic augmentation marking and oriented edge embeddings carry
this disjointness to the full reverse seed kernel and the whole midpoint
core. At every critical path a--z with midpoint c, put
H = [Z_z intersect Q_a,Q_c], D = [Z_a,Z_z], and
C = U_z intersect C(G_z). The previously proved order-two bound and
H <= D join C now give H intersect D = 1 and H join D = D join C.
In particular the retained central attachment C lies in [U_z,Q_c].
Both commutators use the original full moving cover and literal cores.
The cubic projection still has kernel E, with its nontrivial odd E/Q.

The whole-core and literal C.1.32 applications retain the same strict paths,
generating edge and shifted kernel, alongside this comparison on every
critical path. This supplies the precise augmentation attachment comparison;
the full-X control and terminal contradiction of MS93 (5.12) remain open,
as do the other radical-image branches and final reconstruction assembly.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), pp.866--867, and the attachment comparison in the proof of
(5.12)(1), pp.924--925; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup BinaryPermutation Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CubicAugmentationModel
local notation "S" => Equiv.Perm (Fin 6)
local notation "ρ" => coreRepresentation (Fin 6)

private theorem core_preserves_pair (g : S) (hg : g ∈ pointCore) :
    g 4 = 4 ∨ g 4 = 5 := by
  let P : Subgroup S := MulAction.stabilizer S ({4,5} : Finset (Fin 6))
  have hc : pointCore ≤ P := by
    rw [pointCore_eq_closure,closure_le]
    rintro x (rfl|rfl|rfl) <;> change _ • ({4,5} : Finset (Fin 6)) = {4,5} <;> decide +kernel
  have hp : g • ({4,5} : Finset (Fin 6)) = {4,5} := hc hg
  have hh : g 4 ∈ g • ({4,5} : Finset (Fin 6)) := by
    exact Finset.smul_mem_smul_finset (by simp)
  rw [hp] at hh
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hh

private theorem fixed_displacement_zero (g : S) (hg : g ∈ pointCore)
    (v : core (Fin 6)) (hv : ρ swap45 v = v) :
    (ρ g v-v).val 4 = 0 := by
  have he : v.val 5 = v.val 4 := congrArg (fun w : core (Fin 6) => w.val 4) hv
  change v.val (g⁻¹ 4) - v.val 4 = 0
  rcases core_preserves_pair g⁻¹ (pointCore.inv_mem hg) with h4|h5
  · rw [h4,sub_self]
  · rw [h5,he,sub_self]

private theorem swap_displacement_zero (v : core (Fin 6))
    (hv : (ρ swap45 v-v).val 4 = 0) : ρ swap45 v-v = 0 := by
  have he : v.val 5 = v.val 4 := sub_eq_zero.mp hv
  apply Subtype.ext
  ext i
  fin_cases i <;> change v.val _ - v.val _ = 0
  all_goals first | exact sub_self _ | exact sub_eq_zero.mpr he | exact sub_eq_zero.mpr he.symm

private theorem canonical_disjoint :
    Disjoint (subspaceCommutator ρ (fixedSpace ρ (zpowers swap45)) pointCore)
      (subspaceCommutator ρ ⊤ (zpowers swap45)) := by
  apply Submodule.disjoint_def.mpr
  intro v hv hw
  have hzero : ∀ w ∈ subspaceCommutator ρ (fixedSpace ρ (zpowers swap45)) pointCore,
      w.val 4 = 0 := by
    intro w hw
    let f : core (Fin 6) →ₗ[ZMod 2] ZMod 2 :=
      (LinearMap.proj 4).comp (core (Fin 6)).subtype
    have hle : subspaceCommutator ρ (fixedSpace ρ (zpowers swap45)) pointCore ≤ f.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,z,hz,rfl⟩
      exact fixed_displacement_zero g hg z ((mem_fixedSpace_zpowers_iff ρ swap45 z).mp hz)
    exact hle hw
  rw [Representation.CyclicFixedRank.commutator_eq_range] at hw
  obtain ⟨w,rfl⟩ := hw
  exact swap_displacement_zero w (hzero _ hv)

private theorem marked_disjoint (u t : S)
    (ht : t ∈ pointCore.map (MulAut.conj u).toMonoidHom) (hs : t.IsSwap) :
    Disjoint (subspaceCommutator ρ (fixedSpace ρ (zpowers t))
      (pointCore.map (MulAut.conj u).toMonoidHom))
      (subspaceCommutator ρ ⊤ (zpowers t)) := by
  have he := PointCoreTranspositionFixed.swap_eq_conjugate u t ht hs
  subst t
  let f : S →* S := (MulAut.conj u).toMonoidHom
  let E : core (Fin 6) ≃ₗ[ZMod 2] core (Fin 6) :=
    { ρ u with
      invFun := ρ u⁻¹
      left_inv := (coreRepresentation (Fin 6)).inv_self_apply u
      right_inv := (coreRepresentation (Fin 6)).self_inv_apply u }
  have hE (g : S) (v : core (Fin 6)) : E (ρ g v) = ρ (f g) (E v) := by
    change ρ u (ρ g v) = ρ (u*g*u⁻¹) (ρ u v)
    simp only [map_mul,Module.End.mul_apply,(coreRepresentation (Fin 6)).inv_self_apply]
  have hfix := fixedSpace_map_equivariant ρ ρ f E hE (zpowers swap45)
  have hh := Submodule.disjoint_map (f := E.toLinearMap) E.injective canonical_disjoint
  have hmap (I : Submodule (ZMod 2) (core (Fin 6))) (A : Subgroup S) :
      (subspaceCommutator ρ I A).map E.toLinearMap =
        subspaceCommutator ρ (I.map E.toLinearMap) (A.map f) := by
    exact subspaceCommutator_map_conj ρ I A u
  rw [hmap,hmap,hfix,Submodule.map_top,E.range,MonoidHom.map_zpowers] at hh
  exact hh

end CubicAugmentationModel

open scoped commutatorElement IsMulCommutative Pointwise
open Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)

private theorem commutator_core_coordinates
    (E : Additive W ≃ₗ[ZMod 2] core (Fin 6))
    (hE : let := h.relative_normal
      ∀ (g : M) (v : Additive W), E (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        coreRepresentation (Fin 6) (π g) (E v))
    (P B : Subgroup M) (hPW : P ≤ W)
    (I : Submodule (ZMod 2) (core (Fin 6)))
    (hPI : ∀ v : W, (v : M) ∈ P → E (Additive.ofMul v) ∈ I)
    (v : W) (hv : (v : M) ∈ ⁅P,B⁆) :
    E (Additive.ofMul v) ∈ subspaceCommutator (coreRepresentation (Fin 6)) I (B.map π) := by
  let := h.relative_normal
  let D := subspaceCommutator (coreRepresentation (Fin 6)) I (B.map π)
  let T := (D.comap E.toLinearMap).toAddSubgroup.toSubgroup'.map (W).subtype
  have hbound : ⁅P,B⁆ ≤ T := by
    apply commutator_le.mpr
    intro x hx b hb
    have hc : ⁅x,b⁆ ∈ W := (commutator_le_left W B)
      (commutator_mem_commutator (hPW hx) hb)
    refine ⟨⟨⁅x,b⁆,hc⟩,?_,rfl⟩
    change E (Additive.ofMul (⟨⁅x,b⁆,hc⟩ : W)) ∈ D
    have he : Additive.ofMul (⟨⁅x,b⁆,hc⟩ : W) =
        Additive.ofMul (⟨x,hPW hx⟩ : W) -
          Additive.ofMul (MulAut.conjNormal b (⟨x,hPW hx⟩ : W)) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      simp [commutatorElement_def,div_eq_mul_inv,mul_assoc]
    have hcoord : E (Additive.ofMul (MulAut.conjNormal b (⟨x,hPW hx⟩ : W))) =
        coreRepresentation (Fin 6) (π b) (E (Additive.ofMul (⟨x,hPW hx⟩ : W))) :=
      hE b (Additive.ofMul (⟨x,hPW hx⟩ : W))
    rw [he,map_sub,hcoord]
    apply D.neg_mem_iff.mp
    rw [neg_sub]
    exact Submodule.subset_span ⟨π b,mem_map_of_mem π hb,
      E (Additive.ofMul (⟨x,hPW hx⟩ : W)),hPI _ hx,rfl⟩
  obtain ⟨w,hw,he⟩ := hbound hv
  have hwv : w = v := Subtype.ext he
  exact hwv ▸ hw

include h e hz hk in
/-- The fixed-hyperplane displacement and the transposition displacement
are disjoint on the entire augmentation cover. -/
theorem point_cover_fixed_edge_disjoint
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (hA : A ≤ Rg)
    (hne : ¬ A ≤ pCore 2 M)
    (hindex : (centralizer (A : Set M)).relIndex W ≤ 2) :
    ⁅W ⊓ centralizer (A : Set M),Rg⁆ ⊓ ⁅W,A⁆ = ⊥ := by
  let := h.relative_normal
  obtain ⟨E,hE⟩ := point_moved_core_model h e hz hk u hR
  have hnA : A.map π ≠ ⊥ := by
    intro he
    exact hne (two_subgroup_le_core_of_le_extensionKernel h hz A
      (h.relative_radical.isPGroup.to_le hA)
      ((CubicAction.projection_kernel h e hz hk) ▸ (map_eq_bot_iff A).mp he))
  have hsmall : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim W π
      (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk)
      (naturalRepresentation (Fin 6)) (coverMap h e hz hk) (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (A.map π)).trans hsmall
  obtain ⟨t,ht,hts,hAt⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers
    (A.map π) hnA hnat
  have htc := hR (map_mono hA ht)
  have hdis := CubicAugmentationModel.marked_disjoint u t htc hts
  apply le_bot_iff.mp
  intro x hx
  have hxW : x ∈ W := (commutator_le_left W A) hx.2
  let v : W := ⟨x,hxW⟩
  have hfix : ∀ w : W, (w : M) ∈ W ⊓ centralizer (A : Set M) →
      E (Additive.ofMul w) ∈ fixedSpace (coreRepresentation (Fin 6)) (zpowers t) := by
    intro w hw
    rw [←hAt]
    rintro ⟨_,a,ha,rfl⟩
    change coreRepresentation (Fin 6) (π a) (E (Additive.ofMul w)) = E (Additive.ofMul w)
    rw [←hE]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    change a*(w:M)*a⁻¹ = (w:M)
    rw [hw.2 a ha,mul_inv_cancel_right]
  have hvH := commutator_core_coordinates h e hz hk E hE
    (W ⊓ centralizer (A : Set M)) Rg inf_le_left _ hfix v hx.1
  have hvH' : E (Additive.ofMul v) ∈ subspaceCommutator (coreRepresentation (Fin 6))
      (fixedSpace (coreRepresentation (Fin 6)) (zpowers t))
      (pointCore.map (MulAut.conj u).toMonoidHom) :=
    (show subspaceCommutator (coreRepresentation (Fin 6))
      (fixedSpace (coreRepresentation (Fin 6)) (zpowers t)) ((Rg).map π) ≤ _ from by
        apply Submodule.span_le.mpr
        rintro _ ⟨g,hg,w,hw,rfl⟩
        exact Submodule.subset_span ⟨g,hR hg,w,hw,rfl⟩) hvH
  have hvD := commutator_core_coordinates h e hz hk E hE W A le_rfl ⊤
    (fun _ _ => Submodule.mem_top) v hx.2
  rw [hAt] at hvD
  have he : E (Additive.ofMul v) = 0 := Submodule.disjoint_def.mp hdis _ hvH' hvD
  have hzv : Additive.ofMul v = 0 := E.injective (he.trans E.map_zero.symm)
  exact congrArg (fun w : Additive W => (w.toMul : M)) hzv

include h e hz hk in
/-- Disjointness on the full seed through the same oriented edge embedding. -/
theorem point_edge_fixed_disjoint (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hcol : color Rg c = false)
    (hct : Adjacent Rg c t)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t)
    (hne : ¬ A ≤ Q Rg c)
    (hindex : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2) :
    ⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),Q Rg t⁆ ⊓
      ⁅U Rg c,A⁆ = ⊥ := by
  have hcoords : ∃ i : M →* FreeAmalgam Rg, Function.Injective i ∧ i.range = stabilizer Rg c ∧
      (Rg).map i = Q Rg t ∧ (pCore 2 M).map i = Q Rg c ∧
      (W).map i = U Rg c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common Rg c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM Rg)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective Rg),?_,?_,?_,?_⟩
      · have he := stabilizer_act Rg g (alpha Rg)
        rw [alpha,act_mVertex,one_mul,stabilizer_m_base] at he
        simpa only [i,MonoidHom.range_comp,Mbar] using he.symm
      · have he := Q_act Rg g (beta Rg)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
      · have he := Q_act Rg g (alpha Rg)
        rw [Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := U_act Rg g (alpha Rg)
        rw [←graph_U_map h e hz] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · rw [hg.1] at hcol
      cases hcol
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := hcoords
  have hAi : A ≤ i.range := hA.trans (hiR ▸ map_le_range i _)
  have hmA : (A.comap i).map i = A := map_comap_eq_self hAi
  have hAr : A.comap i ≤ Rg := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmA,hiR]
  have hAn : ¬ A.comap i ≤ pCore 2 M := by
    intro hh
    apply hne
    have hm := map_mono (f := i) hh
    rwa [hmA,hiQ] at hm
  have hidx : (centralizer (A.comap i : Set M)).relIndex W ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hdis := congrArg (Subgroup.map i)
    (point_cover_fixed_edge_disjoint h e hz hk u hR (A.comap i) hAr hAn hidx)
  rw [Subgroup.map_inf _ _ i hi,map_commutator,
    ←map_inf_centralizer_of_injective i hi,hiU,hmA,hiR,
    map_commutator,hiU,hmA,Subgroup.map_bot] at hdis
  rw [full_fixed_seed_edge_commutator h e hz hcol hct A hA (Q Rg t) le_rfl]
  exact hdis

include h e hz hk in
/-- The full reverse-kernel predecessor commutator misses the critical line. -/
theorem point_critical_kernel_disjoint_line
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4) :
    ⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆ ⊓
      ⁅Z Rg a,Z Rg a'⁆ = ⊥ := by
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let t := p.walk.getVert (p.walk.length-1)
  have hat : Adjacent Rg a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hpred : Q Rg (p.walk.getVert (p.walk.length-2)) ≤ Q Rg t := by
    apply Q_le_adjacent_h Rg ht
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hZt : Z Rg a ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-1 < sourceDistance h
    omega
  have hfixed : Z Rg a' ⊓ Q Rg a =
      Z Rg a' ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) := by
    let q := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
      (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h) a' p.end_color p.critical)
    exact (critical_seed_centralizer_intersection h e q).symm
  let := finite_Z Rg a'
  let : Finite (U Rg a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg a')) (inclusion_injective _)
  have hindex : (centralizer (Z Rg a : Set (FreeAmalgam Rg))).relIndex
      (U Rg a') ≤ 2 := by
    have hQC : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg a') index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p hsmall).2
  have hd := point_edge_fixed_disjoint h e hz hk u hR p.end_color hat
    (Z Rg a) hZt p.critical.2 hindex
  rw [←hfixed] at hd
  let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by
        rw [(sourceGeometry h).distance_constant _ p.start_color]
        exact sourceDistance_pos h) a' p.end_color p.critical)
  have hsr : (Q Rg a).relIndex (Z Rg a') < 4 := by
    rw [(small_critical_indices h e hz hk p hsmall).2]
    decide
  rw [small_critical_moving_commutator_eq h e hz hk pr hsr,
    commutator_comm (Z Rg a')] at hd
  exact le_bot_iff.mp ((inf_le_inf_right _ (commutator_mono le_rfl hpred)).trans_eq hd)


include h e hz hk in
/-- At every critical pair, the reverse-kernel line and the critical line
are the two distinct noncentral lines of the endpoint attachment plane.
The whole midpoint core moves the full cover onto a subgroup containing
that attachment; no injectivity on the natural quotient is used. -/
theorem point_critical_midpoint_attachment_plane
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    let c := p.walk.getVert 2
    let H := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
    let D := ⁅Z Rg a,Z Rg z⁆
    let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
    H ⊓ D = ⊥ ∧ H ⊔ D = D ⊔ C ∧ C ≤ ⁅U Rg z,Q Rg c⁆ := by
  let c := p.walk.getVert 2
  let H := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
  let D := ⁅Z Rg a,Z Rg z⁆
  let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hs : (Q Rg z).relIndex (Z Rg a) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR p).1]
    decide
  have hdis : H ⊓ D = ⊥ := by
    simpa only [hl,Nat.reduceSub] using point_critical_kernel_disjoint_line h e hz hk u hR p hs
  have hHD : H ≤ D ⊔ C := by
    simpa only [hl,Nat.reduceSub] using
      critical_kernel_predecessor_le_line_sup_attachment h e hz hk u hR p hs
  have hHcard : Nat.card H = 2 := (point_critical_radius_cross_kernel_line_at h e hz hk u hR p).1
  have hCc : Nat.card C = 2 := point_graph_central_attachment_card_two h e hz hk u hR z p.end_color
  let : Finite C := Nat.finite_of_card_ne_zero (by rw [hCc]; decide)
  let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by
        rw [(sourceGeometry h).distance_constant _ p.start_color]
        exact sourceDistance_pos h) z p.end_color p.critical)
  have hsr : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR p).2.1]
    decide
  have hDm : D = ⁅U Rg z,Z Rg a⁆ := by
    rw [small_critical_moving_commutator_eq h e hz hk pr hsr,commutator_comm]
  have hDG : D ≤ stabilizer Rg z := by
    rw [show D = ⁅Z Rg a,Z Rg z⁆ from rfl,commutator_comm]
    exact (critical_seed_commutator_le h pr).trans (Z_le_stabilizer Rg z)
  have hDN : D ≤ normalizer (C : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp ((inf_le_right : C ≤ centralizer
      (stabilizer Rg z : Set (FreeAmalgam Rg))).trans (centralizer_le hDG))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hnot : ¬ H ≤ D := by
    intro he
    have hzero : H = ⊥ := (inf_eq_left.mpr he).symm.trans hdis
    rw [hzero,card_bot] at hHcard
    omega
  have hC : C ≤ H ⊔ D := two_line_exchange H C D hCc
    (hHD.trans_eq (sup_comm D C)) hDN hnot
  refine ⟨hdis,le_antisymm (sup_le hHD le_sup_left) (sup_le le_sup_right hC),?_⟩
  apply hC.trans
  apply sup_le
  · have he := (critical_kernel_predecessor_moving h e hz (distance_gt_two h e hz hk) p).2.2
      (Q Rg c) (by simp only [hl,Nat.reduceSub]; exact le_rfl)
    change H ≤ ⁅U Rg z,Q Rg c⁆
    rw [show H = ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆ from rfl,he]
    exact commutator_mono inf_le_left le_rfl
  · rw [hDm]
    apply commutator_mono le_rfl
    apply Z_le_Q_of_dist_lt Rg a ((sourceGeometry h).exists_critical a p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    change 2 < sourceDistance h
    omega


omit hk in
include h e hz in
/-- Whole-core application of the exact augmentation attachment plane on every critical path. -/
theorem coreExhaustion_or_cubic_augmentation_lines :
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
          (∀ a z : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) a z,
            let c := p.walk.getVert 2
            let H := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
            let D := ⁅Z Rg a,Z Rg z⁆
            let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
            H ⊓ D = ⊥ ∧ H ⊔ D = D ⊔ C ∧ C ≤ ⁅U Rg z,Q Rg c⁆) ∧
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
  rcases coreExhaustion_or_cubic_midpoint_core h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · rcases hpoint with ⟨hpoint,hb4,hmodel,hsize,hX,hpaths⟩
    exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint,hb4,hmodel,hsize,hX,
      fun _ _ p => point_critical_midpoint_attachment_plane h e hz hk u hpoint.le p,hpaths⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application, retaining the strict paths and the full endpoint attachment. -/
theorem rankTwo_or_cubic_augmentation_lines :
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
          (∀ a z : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) a z,
            let c := p.walk.getVert 2
            let H := ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆
            let D := ⁅Z Rg a,Z Rg z⁆
            let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
            H ⊓ D = ⊥ ∧ H ⊔ D = D ⊔ C ∧ C ≤ ⁅U Rg z,Q Rg c⁆) ∧
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
  (coreExhaustion_or_cubic_augmentation_lines h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
