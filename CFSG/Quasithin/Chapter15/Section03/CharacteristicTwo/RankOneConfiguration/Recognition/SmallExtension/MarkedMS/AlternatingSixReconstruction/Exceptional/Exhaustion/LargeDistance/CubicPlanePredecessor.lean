module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRemainingRadicals
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOppositeTransfer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardFixedCore
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicResidualShift

/-!
# Predecessor control in the original cubic plane branch

For a small critical path, the full reverse seed kernel has commutator of
order at most four with the second predecessor core. The three-pair cover
calculation gives this bound on both the natural quotient and the augmentation
cover; the incident central seed contributes no further movement. A small
predecessor Baumann slice puts the commutator in the last edge seed. Residual
normalization and the original cubic small-normal-subgroup action then make
it central in the entire predecessor stabilizer. This gives an exact identity
when a predecessor residual element transports the second commutator entry.

One trapped radius supplies all these slice premises throughout the original
graph. The actual paired selector produces a nonzero reverse-kernel line and
a residual-shifted critical path, retaining the selected edge, original switch,
both generation identities, and every overlapping vertex. This line equals
the transported endpoint movement. It is central at the second predecessor
and noncentral at the endpoint. The further source comparison with the
original critical line and endpoint center is still needed to exclude this
configuration. Whole-core and literal C.1.32 consumers retain that uniform-small
plane alternative, the Borel alternative, and both full cover orders.

The internal imports deliberately reuse the cubic coordinate, normal-action,
normalization and path implementations. Only the six-letter representation
calculation is reused from `Natural/.../CubeSmallKernel`; no identification
with that branch's graph or quotient kernel is assumed. Throughout, the cubic
projection retains its full extension kernel and its nontrivial odd central
quotient over the two-core.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), printed pp.866--867, and the predecessor/residual part of
(5.8), printed p.920; Aschbacher--Smith, C.1.31--32, printed pp.135--136.
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

include h e hz hk in
/-- The full cover's fixed hyperplane has at most four commutators with a
three-pair radical, retaining the possible central line. -/
private theorem plane_cover_small_fixed_edge_card (u : S)
    (hR : (Rg).map π ≤ D.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (hA : A ≤ Rg)
    (hne : ¬ A ≤ pCore 2 M)
    (hindex : (centralizer (A : Set M)).relIndex (W₀) ≤ 2) :
    Nat.card (⁅W₀ ⊓ centralizer (A : Set M),Rg⁆ :
      Subgroup M) ≤ 4 := by
  let := h.relative_normal
  let U := W₀
  let W := subspaceCommutator (coverAction h e hz hk) (fixedSpace (coverAction h e hz hk) (A.map π))
    ((CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom)
  let T := W.toAddSubgroup.toSubgroup'.map U.subtype
  have hsmall : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (W₀) π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk) (naturalRepresentation (Fin 6))
      (coverMap h e hz hk)
      (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (A.map π)).trans hsmall
  have hnA : A.map π ≠ ⊥ := by
    intro he
    exact hne (two_subgroup_le_core_of_le_extensionKernel h hz A
      (h.relative_radical.isPGroup.to_le hA)
      (CubicAction.projection_kernel h e hz hk ▸ (map_eq_bot_iff A).mp he))
  have hdim : Module.finrank (ZMod 2) W ≤ 2 := by
    exact Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallKernel.model_fixed_movement (coverAction h e hz hk) (moved_subgroup_cover_model h e hz hk) u
      (A.map π) (by simpa only [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] using ((map_mono hA).trans hR)) hnA hnat
  have hc : ⁅U ⊓ centralizer (A : Set M),Rg⁆ ≤ T := by
    apply commutator_le.mpr
    intro v hv r hr
    have hcu : ⁅v,r⁆ ∈ U := (commutator_le_left U Rg)
      (commutator_mem_commutator hv.1 hr)
    refine ⟨⟨⁅v,r⁆,hcu⟩,?_,rfl⟩
    change Additive.ofMul (⟨⁅v,r⁆,hcu⟩ : U) ∈ W
    rw [NormalElementaryQuotient.vector_commutator U π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) ⟨v,hv.1⟩ r]
    apply W.neg_mem_iff.mp
    rw [neg_sub]
    apply Submodule.subset_span
    refine ⟨π r,?_,Additive.ofMul ⟨v,hv.1⟩,?_,rfl⟩
    · simpa only [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq] using
        hR (mem_map_of_mem _ hr)
    · exact (NormalElementaryQuotient.mem_fixedSpace_image U π (CubicEven.projection_surjective h e hz hk)
        (CubicAction.moved_projection_kernel h e hz hk) A _).mpr hv.2
  apply (card_le_of_le hc).trans
  rw [card_map_of_injective U.subtype_injective]
  change Nat.card W ≤ 4
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact (Nat.pow_le_pow_right (by decide : 0<2) hdim)

include h e hz hk in
/-- The fixed part of the entire endpoint seed has at most four commutators
with its incident edge kernel. No equality with the critical moved line is used. -/
private theorem plane_small_edge_fixed_card_at (u : S)
    (hR : (Rg).map π ≤ D.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hcol : color Rg c = false)
    (hct : Adjacent Rg c t)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t)
    (hne : ¬ A ≤ Q Rg c)
    (hindex : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2) :
    Nat.card (⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),Q Rg t⁆ :
      Subgroup (FreeAmalgam Rg)) ≤ 4 := by
  obtain ⟨i,hi,_,hiR,hiQ,hiU⟩ := remaining_edge_coordinates h e hz hcol hct
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
  have hidx : (centralizer (A.comap i : Set M)).relIndex (W₀) ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hcard := plane_cover_small_fixed_edge_card h e hz hk u hR (A.comap i) hAr hAn hidx
  rw [←card_map_of_injective hi,map_commutator,
    ←map_inf_centralizer_of_injective i hi,hiU,hmA,hiR] at hcard
  let F := U Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hcol] at hh
    cases he : color Rg t <;> simp_all
  have hseed : Z Rg t ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedA := hseed.trans (centralizer_le hA)
  have hseedN : Z Rg t ≤ normalizer (U Rg c : Set (FreeAmalgam Rg)) :=
    ((adjacent_Z_le Rg hcol hct).trans (Z_le_stabilizer Rg c)).trans (U_normalized c)
  have heq : Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)) = F ⊔ Z Rg t := by
    rw [vertex_seed_eq_moving_sup_edge h e hz hcol hct,
      sup_comm (U Rg c),inf_centralizer_sup_of_centralizing _ _ _ hseedN hseedA]
    exact sup_comm _ _
  have hbound : ⁅F ⊔ Z Rg t,Q Rg t⁆ ≤ ⁅F,Q Rg t⁆ := by
    apply commutator_le.mpr
    intro x hx r hr
    have hn : Z Rg t ≤ normalizer (F : Set (FreeAmalgam Rg)) :=
      (le_inf hseedN (hseedA.trans (centralizer (A : Set (FreeAmalgam Rg))).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    have hp : x ∈ (F : Set (FreeAmalgam Rg)) * (Z Rg t : Set (FreeAmalgam Rg)) := by
      rw [←coe_mul_of_right_le_normalizer_left F (Z Rg t) hn]
      exact hx
    obtain ⟨w,hw,z,hz,rfl⟩ := hp
    have hzero : ⁅z,r⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hseed hz r hr).symm
    rw [commutatorElement_mul_left_eq_conj_mul,hzero,mul_one,mul_inv_cancel,one_mul]
    exact commutator_mem_commutator hw hr
  let := finite_Z Rg c
  have hFU : ⁅F,Q Rg t⁆ ≤ U Rg c :=
    (commutator_mono (show F ≤ U Rg c from inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((show Q Rg t ≤ stabilizer Rg c from
          fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (U_normalized c)))
  let : Finite (⁅F,Q Rg t⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion (hFU.trans (DistanceEight.U_le_Z Rg c))) (inclusion_injective _)
  rw [heq]
  exact (card_le_of_le hbound).trans hcard

include h e hz hk in
/-- The last edge bounds the entire reverse critical kernel's commutator
with the second predecessor core, for either full central cover. -/
theorem plane_small_critical_kernel_predecessor_card
    (hb : 2 < sourceDistance h)
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) ≤
      D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4) :
    Nat.card (⁅Z Rg a' ⊓ Q Rg a,
      Q Rg (p.walk.getVert (p.walk.length-2))⁆ : Subgroup (FreeAmalgam Rg)) ≤ 4 := by
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
  have hcard := plane_small_edge_fixed_card_at h e hz hk u hR p.end_color hat
    (Z Rg a) hZt p.critical.2 hindex
  rw [←hfixed] at hcard
  have hKt : Z Rg a' ⊓ Q Rg a ≤ Q Rg t := by
    apply inf_le_left.trans
    apply (Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color) ?_).trans
      (Q_le_adjacent_h Rg ht hat)
    rw [SimpleGraph.dist_self,(sourceGeometry h).distance_constant _ p.end_color]
    exact sourceDistance_pos h
  let := finite_stabilizer Rg t
  let : Finite (⁅Z Rg a' ⊓ Q Rg a,Q Rg t⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion ((Subgroup.commutator_le_sup _ _).trans
      ((sup_le hKt le_rfl).trans (fun _ hx => hx.1)))) (inclusion_injective _)
  exact (card_le_of_le (commutator_mono le_rfl hpred)).trans hcard

include h e hz hk in
private theorem plane_small_normal_core_fixed
    {c : Vertex Rg} (hcol : color Rg c = false)
    (N : Subgroup (FreeAmalgam Rg)) (hNQ : N ≤ Q Rg c)
    (hNn : stabilizer Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)))
    (hcard : Nat.card N ≤ 4)
    (hfix : N ≤ centralizer (Q Rg c : Set (FreeAmalgam Rg))) :
    N ≤ centralizer (Ltilde Rg c : Set (FreeAmalgam Rg)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg hcol
  let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM Rg)
  have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective Rg)
  have hact : act Rg g (alpha Rg) = c := by
    rw [hg]
    simp only [alpha,act_mVertex,one_mul]
  have hir : i.range = stabilizer Rg c := by
    rw [←hact,stabilizer_act]
    change ((MulAut.conj g⁻¹).toMonoidHom.comp (embedM Rg)).range = _
    rw [MonoidHom.range_comp]
    exact congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) (stabilizer_m_base Rg).symm
  have hiQ : (pCore 2 M).map i = Q Rg c := by
    rw [←hact,Q_act,Q_alpha Rg h.relative_radical.isPGroup
      h.relative_radical.twoCore_le,map_map]
  have hiL : (pResidual 2 M).map i = Ltilde Rg c := by
    rw [←hact,Ltilde_act,Ltilde_alpha,map_map]
  let N₀ := N.comap i
  have hNm : N₀.map i=N := map_comap_eq_self
    ((hNQ.trans (fun _ hx => hx.1)).trans_eq hir.symm)
  let : N₀.Normal := ⟨by
    intro z hz m
    change i (m*z*m⁻¹) ∈ N
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hNn (hir ▸ (show i m ∈ i.range from ⟨m,rfl⟩))) _).mp hz⟩
  have hc₀ : Nat.card N₀ ≤ 4 := by
    rw [←card_map_of_injective hi,hNm]
    exact hcard
  have hQfix : pCore 2 M ≤ centralizer (N₀ : Set M) := by
    intro m hm n hn
    apply hi
    simp only [map_mul]
    exact (hfix hn (i m) (hiQ ▸ mem_map_of_mem i hm)).symm
  have hfixed := small_normal_subgroup_fixed h e hz hk N₀ hc₀ hQfix
  rw [←h.relative_residual] at hfixed
  have hh := congrArg (Subgroup.map i) (commutator_eq_bot_iff_le_centralizer.mpr hfixed)
  rw [map_commutator,hNm,hiL,Subgroup.map_bot] at hh
  exact commutator_eq_bot_iff_le_centralizer.mp hh

include h e hz hk in
/-- A small predecessor slice makes the full reverse-kernel commutator
central in the predecessor stabilizer. Its order can be four; the cubic
normal-subgroup action argument supplies residual fixedness. -/
theorem plane_predecessor_slice_commutator_central
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hindex : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg a') ≤ 2) :
    let K := Z Rg a' ⊓ Q Rg a
    let N := ⁅K,Q Rg (p.walk.getVert (p.walk.length-2))⁆
    Nat.card N ≤ 4 ∧ N ≤ Z Rg (p.walk.getVert (p.walk.length-1)) ∧
      N ≤ centralizer (stabilizer Rg (p.walk.getVert (p.walk.length-2)) :
        Set (FreeAmalgam Rg)) := by
  have hb := distance_gt_two h e hz hk
  let c := p.walk.getVert (p.walk.length-2)
  let t := p.walk.getVert (p.walk.length-1)
  let K := Z Rg a' ⊓ Q Rg a
  let N := ⁅K,Q Rg c⁆
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c=false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hct : Adjacent Rg c t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have het : Adjacent Rg a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t=true := by
    have hh := adjacent_color_ne Rg hct
    rw [hcol] at hh
    cases he : color Rg t <;> simp_all
  have hslice := critical_predecessor_small_slice h e hz hk hb p hindex
  have hKB : K ≤ B Rg c ((sourceGeometry h).Z_normal _) :=
    hslice.1.ge.trans inf_le_right
  have hcard : Nat.card N ≤ 4 := plane_small_critical_kernel_predecessor_card h e hz hk hb u hR.le p
    (by rw [hslice.2.2]; decide)
  have hNedge : N ≤ Z Rg t :=
    (commutator_mono inf_le_left (Q_le_adjacent_h Rg ht hct)).trans
      (plane_edge_seed_commutator h e hz hk u hR p.end_color het)
  have hVG := ((sourceGeometry h).V_le_Q hb c hcol).trans
    (show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1)
  have hKQ : K ≤ Q Rg c := by
    intro z hz
    exact (sourceGeometry h).V_le_Q hb c hcol
      (((mem_B_iff Rg c _ hVG z).mp (hKB hz)).1)
  have hNQ : N ≤ Q Rg c := (Subgroup.commutator_le_sup _ _).trans (sup_le hKQ le_rfl)
  have hfix : ⁅Ltilde Rg c,K⁆ ≤ centralizer (Q Rg c : Set (FreeAmalgam Rg)) := by
    apply le_trans _ (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hcol))
    apply commutator_le.mpr
    intro l hl z hz
    exact ((mem_B_iff Rg c _ hVG z).mp (hKB hz)).2 l hl
  have hLn : Ltilde Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)) :=
    fixed_mod_seed_normalizes_commutator K (Q Rg c) (Ltilde Rg c)
      (hKQ.trans (Q Rg c).le_normalizer)
      ((Ltilde_le_stabilizer c).trans (Q_normalized Rg c)) hfix
  have hedgefix : N ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    intro z hz
    have hh := hNedge hz
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  have hgen : Ltilde Rg c ⊔ Q Rg t = stabilizer Rg c := by
    apply CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
    · rw [h.relative_residual]
      exact (codisjoint_subgroupOf_sup L R).eq_top
    · exact hcol
    · exact hct
  have hNn : stabilizer Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le hLn ((le_centralizer_iff.mp hedgefix).trans (Subgroup.centralizer_le_normalizer _))
  have hres := plane_small_normal_core_fixed h e hz hk hcol N hNQ hNn hcard
    (hedgefix.trans (centralizer_le (Q_le_adjacent_h Rg ht hct)))
  refine ⟨hcard,hNedge,?_⟩
  apply le_centralizer_iff.mp
  rw [←hgen]
  exact sup_le (le_centralizer_iff.mp hres) (le_centralizer_iff.mp hedgefix)
include h in
private theorem plane_slice_commutator_transport_of_fixed
    (hb : 2 < sourceDistance h) {c : Vertex Rg}
    (hcol : color Rg c = false)
    (A : Subgroup (FreeAmalgam Rg))
    (hAB : A ≤ B Rg c ((sourceGeometry h).Z_normal _))
    (hfixed : ⁅A,Q Rg c⁆ ≤ centralizer (Ltilde Rg c : Set (FreeAmalgam Rg)))
    (D : Subgroup (FreeAmalgam Rg)) (hD : D ≤ Q Rg c)
    (k : FreeAmalgam Rg) (hk : k ∈ Ltilde Rg c) :
    ⁅A,D.map (MulAut.conj k).toMonoidHom⁆ = ⁅A,D⁆ := by
  have hVQ := (sourceGeometry h).V_le_Q hb c hcol
  have hVG := hVQ.trans (show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1)
  have hAQ : A ≤ Q Rg c := by
    intro a ha
    exact hVQ (((mem_B_iff Rg c _ hVG a).mp (hAB ha)).1)
  have hZQ : Z Rg c ≤ centralizer (Q Rg c : Set (FreeAmalgam Rg)) :=
    commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hcol)
  have he (a : FreeAmalgam Rg) (ha : a ∈ A)
      (x : FreeAmalgam Rg) (hx : x ∈ Q Rg c) :
      ⁅a,k*x*k⁻¹⁆ = ⁅a,x⁆ := by
    have hx' : k*x*k⁻¹ ∈ Q Rg c :=
      (mem_normalizer_iff.mp ((Q_normalized Rg c) (Ltilde_le_stabilizer _ hk)) x).mp hx
    have hka : ⁅k,a⁆ ∈ Z Rg c :=
      ((mem_B_iff Rg c _ hVG a).mp (hAB ha)).2 k hk
    have hax' : ⁅a,k*x*k⁻¹⁆ ∈ Q Rg c :=
      (Subgroup.commutator_le_sup _ _).trans (sup_le hAQ le_rfl)
        (commutator_mem_commutator ha hx')
    have hzero : ⁅⁅k,a⁆,k*x*k⁻¹⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hZQ hka _ hx').symm
    have hfix : k*⁅a,x⁆*k⁻¹ = ⁅a,x⁆ := by
      have hh := hfixed (commutator_mem_commutator ha hx) k hk
      rw [hh,mul_inv_cancel_right]
    have hh := conjugate_commutatorElement a x k
    rw [show k*a*k⁻¹ = ⁅k,a⁆*a by simp [commutatorElement_def,mul_assoc],
      commutatorElement_mul_left_eq_conj_mul,hzero,mul_one,
      ←hZQ hka _ hax',mul_inv_cancel_right,hfix] at hh
    exact hh.symm
  apply le_antisymm
  · apply commutator_le.mpr
    intro a ha x hx
    obtain ⟨y,hy,rfl⟩ := hx
    change ⁅a,k*y*k⁻¹⁆ ∈ ⁅A,D⁆
    rw [he a ha y (hD hy)]
    exact commutator_mem_commutator ha hy
  · apply commutator_le.mpr
    intro a ha x hx
    rw [←he a ha x (hD hx)]
    exact commutator_mem_commutator ha (mem_map_of_mem (MulAut.conj k).toMonoidHom hx)
include h e hz hk in
/-- Each predecessor residual element preserves the full kernel commutator
while transporting its core actor. The conjugator acts on that actor alone;
the kernel is controlled by the literal predecessor Baumann slice. -/
theorem plane_predecessor_slice_residual_transport
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hindex : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg a') ≤ 2)
    (T : Subgroup (FreeAmalgam Rg))
    (hT : T ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (k : FreeAmalgam Rg)
    (hkm : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2))) :
    ⁅Z Rg a' ⊓ Q Rg a,T.map (MulAut.conj k).toMonoidHom⁆ =
      ⁅Z Rg a' ⊓ Q Rg a,T⁆ := by
  have hb := distance_gt_two h e hz hk
  have hc : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hl : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hs := critical_predecessor_small_slice h e hz hk hb p hindex
  have hn := plane_predecessor_slice_commutator_central h e hz hk u hR p hindex
  exact plane_slice_commutator_transport_of_fixed (h := h) hb hc _
    (hs.1.ge.trans inf_le_right)
    (hn.2.2.trans (centralizer_le (Ltilde_le_stabilizer _))) T hT k hkm

include h e hz hk in
private theorem plane_uniform_slices_predecessor_control
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hall : ∀ v c t : Vertex Rg, color Rg v = false → Adjacent Rg v t → Adjacent Rg c t →
      (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    Z Rg z ⊓ B Rg (p.walk.getVert (p.walk.length-2))
        ((sourceGeometry h).Z_normal _) = Z Rg z ⊓ Q Rg a ∧
      (Q Rg a).relIndex (Z Rg z) = 2 ∧
      (Q Rg z).relIndex (Z Rg a) = 2 ∧
      (let N := ⁅Z Rg z ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆
       Nat.card N ≤ 4 ∧ N ≤ Z Rg (p.walk.getVert (p.walk.length-1)) ∧
       N ≤ centralizer (stabilizer Rg (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam Rg))) ∧
      ∀ T : Subgroup (FreeAmalgam Rg), T ≤ Q Rg (p.walk.getVert (p.walk.length-2)) →
        ∀ k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)),
          ⁅Z Rg z ⊓ Q Rg a,T.map (MulAut.conj k).toMonoidHom⁆ = ⁅Z Rg z ⊓ Q Rg a,T⁆ := by
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hlast : Adjacent Rg z (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hpre : Adjacent Rg (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hs := hall _ _ _ hc hpre hlast
  have hi := critical_predecessor_small_slice h e hz hk hb p hs
  exact ⟨hi.1,hi.2.1,hi.2.2,
    plane_predecessor_slice_commutator_central h e hz hk u hR p hs,
    fun T hT k hkm => plane_predecessor_slice_residual_transport h e hz hk u hR p hs T hT k hkm⟩

include h e hz hk in
/-- One trapped plane radius supplies full predecessor control on every
critical path of the original graph: the exact kernel, both critical indices,
the order-four commutator bound, whole-stabilizer centrality, and the same
residual transport identity. No predecessor-slice premise remains. -/
theorem plane_radius_failure_predecessor_control
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a₀ z₀ : Vertex Rg} (p₀ : CriticalPath Rg (sourceGeometry h) a₀ z₀)
    (hbad : V Rg a₀ ≤ Q Rg (p₀.walk.getVert (p₀.walk.length-2)))
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    Z Rg z ⊓ B Rg (p.walk.getVert (p.walk.length-2))
        ((sourceGeometry h).Z_normal _) = Z Rg z ⊓ Q Rg a ∧
      (Q Rg a).relIndex (Z Rg z) = 2 ∧
      (Q Rg z).relIndex (Z Rg a) = 2 ∧
      (let N := ⁅Z Rg z ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆
       Nat.card N ≤ 4 ∧ N ≤ Z Rg (p.walk.getVert (p.walk.length-1)) ∧
       N ≤ centralizer (stabilizer Rg (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam Rg))) ∧
      ∀ T : Subgroup (FreeAmalgam Rg), T ≤ Q Rg (p.walk.getVert (p.walk.length-2)) →
        ∀ k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)),
          ⁅Z Rg z ⊓ Q Rg a,T.map (MulAut.conj k).toMonoidHom⁆ = ⁅Z Rg z ⊓ Q Rg a,T⁆ :=
  plane_uniform_slices_predecessor_control h e hz hk u hR
    (fun _ _ _ hv hvt hct => plane_radius_failure_uniform_slices h e hz hk u hR p₀ hbad hv hvt hct) p
include h e hz hk in
private theorem plane_paired_eligible_commutator_escape
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hel : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    ¬ ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg (alpha Rg) ∨
      ¬ ⁅Z Rg c,Z Rg z'⁆ ≤ Z Rg (alpha Rg) := by
  by_contra! hboth
  obtain ⟨hcomm,hcomm'⟩ := hboth
  have hb := distance_gt_two h e hz hk
  have hd : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    have hh := (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := alpha Rg)
    omega
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hd)
  let Y := Z Rg c ⊔ Z Rg (alpha Rg)
  have hmove {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hm : ⁅Z Rg c,Z Rg w⁆ ≤ Z Rg (alpha Rg)) :
      ⁅Y,Z Rg w⁆ ≤ Z Rg (alpha Rg) := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (Z Rg c) (Z Rg (alpha Rg)) (Z Rg w) (Z Rg (alpha Rg))
      (Z_normalized Rg _) (hZV.trans ((sourceGeometry h).V_local _ rfl hb))
      (Z_le_stabilizer Rg _) hm
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) r.critical).trans (Z_normalized Rg _))
  have hpY := hmove p hcomm
  have hqY := hmove q hcomm'
  have hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen,plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat]
    refine sup_le (sup_le ?_ (le_normalizer_iff_commutator_le_left.mpr
      (hpY.trans le_sup_right))) (le_normalizer_iff_commutator_le_left.mpr
        (hqY.trans le_sup_right))
    exact (le_inf ((show Q Rg t ≤ stabilizer Rg c from
      fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg c))
      ((show Q Rg t ≤ stabilizer Rg (alpha Rg) from
        fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hUB : U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    (DistanceEight.U_le_Z Rg c).trans (le_sup_left.trans
      (normalized_radius_le_slice_of_critical_commutator h e hz hb p Y
        (sup_le hZV (Z_le_VBall Rg _ 2)) hYN hpY))
  exact hel hUB

include h e hz hk in
private theorem plane_uniform_nonzero_residual_path
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hall : ∀ v c t : Vertex Rg, color Rg v = false → Adjacent Rg v t → Adjacent Rg c t →
      (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    {z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≠ ⊥)
    (k : FreeAmalgam Rg)
    (hkm : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)))
    (hkt : act Rg k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3)) :
    ∃ q : CriticalPath Rg (sourceGeometry h) c (act Rg k z),
      q.walk.getVert 1 = t ∧
      (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      Nat.card (⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ = ⁅U Rg z,Z Rg (act Rg k⁻¹ c)⁆ ∧
      ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
        centralizer (stabilizer Rg (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam Rg)) ∧
      ¬ ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤
        centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
  have hb := distance_gt_two h e hz hk
  have hcontrol := plane_uniform_slices_predecessor_control h e hz hk u hR hall p
  have htransport :
      ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg (act Rg k⁻¹ c)⁆ =
        ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ := by
    rw [Z_act,inv_inv]
    exact hcontrol.2.2.2.2 _ hbad k hkm
  have hescape : ¬ Z Rg c ≤ Q Rg (act Rg k z) := by
    intro hh
    have hm : Z Rg (act Rg k⁻¹ c) ≤ Q Rg z := by
      calc
        _ = (Z Rg c).map (MulAut.conj k).toMonoidHom := by rw [Z_act,inv_inv]
        _ ≤ (Q Rg (act Rg k z)).map (MulAut.conj k).toMonoidHom := map_mono hh
        _ = Q Rg (act Rg k⁻¹ (act Rg k z)) := by
          simpa only [inv_inv] using (Q_act Rg k⁻¹ (act Rg k z)).symm
        _ = Q Rg z := by rw [←act_mul,mul_inv_cancel,act_one]
    apply hne
    rw [←htransport]
    exact le_bot_iff.mp ((commutator_mono inf_le_left hm).trans_eq
      (Z_centralizes_Q Rg z p.end_color))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcfalse : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h1
    cases hc : color Rg c <;> cases ht : color Rg t <;> simp_all
  have hlast : Adjacent Rg (p.walk.getVert (p.walk.length-1)) z := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hend : (cosetGraph Rg).Adj (p.walk.getVert (p.walk.length-3)) (act Rg k z) := by
    rw [←hkt]
    exact (cosetGraph_adj Rg _ _).mpr
      ((adjacent_act_iff Rg k _ _).mpr hlast)
  let w₀ : (cosetGraph Rg).Walk c (alpha Rg) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hct)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  let w₁ := (p.walk.take (p.walk.length-3)).concat hend
  let w := w₀.append w₁
  have hw₀ : w₀.length = 2 := rfl
  have hw : w.length = p.walk.length := by
    simp only [w,w₁,SimpleGraph.Walk.length_append,hw₀,SimpleGraph.Walk.length_concat,
      SimpleGraph.Walk.take_length,inf_eq_left.mpr (Nat.sub_le _ _)]
    omega
  have hmin := criticalDistance_le Rg c ((sourceGeometry h).exists_critical c hcfalse) hescape
  rw [(sourceGeometry h).distance_constant c hcfalse] at hmin
  have hdist : (cosetGraph Rg).dist c (act Rg k z) = sourceDistance h := by
    have hh := SimpleGraph.dist_le w
    rw [hw,p.length_eq_b] at hh
    exact le_antisymm hh hmin
  let q : CriticalPath Rg (sourceGeometry h) c (act Rg k z) :=
    ⟨hcfalse,w,hw.trans (p.length_eq_b.trans hdist.symm),by
      refine ⟨?_,hescape⟩
      rw [(sourceGeometry h).distance_constant c hcfalse]
      exact hdist⟩
  have hback : act Rg k⁻¹ (act Rg k z) = z := by
    rw [←act_mul,mul_inv_cancel,act_one]
  let qr := CriticalPath.ofPair (geometry := sourceGeometry h) q.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      c q.start_color (by
        rw [(sourceGeometry h).distance_constant c q.start_color]
        exact sourceDistance_pos h) (act Rg k z) q.end_color q.critical)
  have hrex : Nonempty (CriticalPath Rg (sourceGeometry h) z (act Rg k⁻¹ c)) := by
    rw [←hback]
    exact ⟨qr.act k⁻¹⟩
  obtain ⟨r⟩ := hrex
  have hrs : (Q Rg (act Rg k⁻¹ c)).relIndex (Z Rg z) < 4 := by
    rw [(plane_uniform_slices_predecessor_control h e hz hk u hR hall r).2.2.1]
    decide
  let H := ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆
  let D₀ := ⁅U Rg z,Z Rg (act Rg k⁻¹ c)⁆
  have hDcard : Nat.card D₀ = 2 := by
    dsimp only [D₀]
    rw [small_critical_moving_commutator_eq h e hz hk r hrs]
    exact small_critical_commutator_card h e hz hk r hrs
  let : Finite D₀ := Nat.finite_of_card_ne_zero (by rw [hDcard]; decide)
  have hkQ : (Q Rg (p.walk.getVert (p.walk.length-2))).map
      (MulAut.conj k).toMonoidHom = Q Rg (p.walk.getVert (p.walk.length-2)) :=
    mem_normalizer_iff_map_conj_eq.mp ((Q_normalized Rg _)
      (Ltilde_le_stabilizer _ hkm))
  have hDk : Z Rg (act Rg k⁻¹ c) ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    rw [Z_act,inv_inv]
    exact (map_mono hbad).trans_eq hkQ
  have hle : H ≤ D₀ := by
    dsimp only [H,D₀]
    rw [←htransport,(critical_kernel_predecessor_moving h e hz hb p).2.2 _ hDk]
    exact commutator_mono inf_le_left le_rfl
  let : Finite H := Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hcard : Nat.card H = 2 := by
    have hlo := (one_lt_card_iff_ne_bot _).mpr hne
    have hhi := card_le_of_le hle
    rw [hDcard] at hhi
    change 1 < Nat.card H at hlo
    omega
  have heq : H = D₀ := eq_of_le_of_card_ge hle (by rw [hcard,hDcard])
  have hcentral : H ≤ centralizer (stabilizer Rg (p.walk.getVert (p.walk.length-2)) :
      Set (FreeAmalgam Rg)) :=
    (commutator_mono le_rfl hbad).trans hcontrol.2.2.2.1.2.2
  have hnon : ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
    rw [heq]
    exact critical_moving_commutator_not_central h e hz hk r
  refine ⟨q,?_,?_,hcard,heq,hcentral,hnon⟩
  · change (w₀.append w₁).getVert 1 = t
    simp only [SimpleGraph.Walk.getVert_append,hw₀,show 1<2 from by decide,ite_true,
      w₀,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero]
  · intro i hi
    change (w₀.append w₁).getVert (i+2) = p.walk.getVert i
    rw [SimpleGraph.Walk.getVert_append,hw₀,if_neg (by omega),Nat.add_sub_cancel]
    change ((p.walk.take (p.walk.length-3)).concat hend).getVert i = p.walk.getVert i
    rw [SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.getVert_append']
    rw [if_pos (by simpa only [SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (Nat.sub_le _ _)] using hi),SimpleGraph.Walk.take_getVert,inf_eq_right.mpr hi]

include h e hz hk in
/-- In the uniform-small case, the original paired selector constructs a
residual-shifted critical path. Every overlap and both generation identities
are retained. Its nonzero full reverse-kernel line is central at the original
second predecessor, but noncentral at the selected endpoint. -/
theorem plane_radius_failure_selected_residual_path
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
  · exact ⟨z,p,Or.inl (fun _ => rfl),finish p (hZV.trans hbad) hn⟩
  · exact ⟨act Rg x z,q,Or.inr (fun _ => rfl),finish q (hZV.trans hqbad) hn⟩
omit hk in
include h e hz in
/-- Whole-core assembly separates the plane branch into actual backward and
forward critical paths, or uniformly small slices with exact full kernels,
central predecessor commutators and their actual residual transports.
The original Borel branch, cubic kernel and both full covers are retained. -/
theorem coreExhaustion_or_cubic_plane_predecessor_reduction :
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
        ((∀ v c t : Vertex Rg, color Rg v = false → Adjacent Rg v t → Adjacent Rg c t →
          (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2) ∧
          ∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
            Z Rg z ⊓ B Rg (p.walk.getVert (p.walk.length-2))
                ((sourceGeometry h).Z_normal _) = Z Rg z ⊓ Q Rg a ∧
              (Q Rg a).relIndex (Z Rg z) = 2 ∧
              (Q Rg z).relIndex (Z Rg a) = 2 ∧
              (let N := ⁅Z Rg z ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆
               Nat.card N ≤ 4 ∧ N ≤ Z Rg (p.walk.getVert (p.walk.length-1)) ∧
               N ≤ centralizer (stabilizer Rg (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam Rg))) ∧
              ∀ T : Subgroup (FreeAmalgam Rg), T ≤ Q Rg (p.walk.getVert (p.walk.length-2)) →
                ∀ k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)),
                  ⁅Z Rg z ⊓ Q Rg a,T.map (MulAut.conj k).toMonoidHom⁆ =
                    ⁅Z Rg z ⊓ Q Rg a,T⁆))) := by
  classical
  rcases coreExhaustion_or_cubic_plane_or_borel h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hplane | hborel⟩
  · exact Or.inl hex
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    by_cases hw : (∃ a z, ∃ _p : CriticalPath Rg (sourceGeometry h) a z,
        4 ≤ (Q Rg z).relIndex (Z Rg a)) ∨
      (∃ v c t : Vertex Rg, color Rg v = false ∧ Adjacent Rg v t ∧ Adjacent Rg c t ∧
        2 < (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c))
    · exact Or.inl (fun a z p => plane_paths_of_large_pair_or_strict_slice h e hz hk u hplane hw p)
    · have hall : ∀ v c t : Vertex Rg, color Rg v = false → Adjacent Rg v t → Adjacent Rg c t →
          (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2 := by
        intro v c t hv hvt hct
        by_contra! hh
        exact hw (Or.inr ⟨v,c,t,hv,hvt,hct,hh⟩)
      exact Or.inr ⟨hall,fun a z p => plane_uniform_slices_predecessor_control h e hz hk u hplane hall p⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩

omit hk in
include h e hz in
/-- The literal C.1.32 consumer retains the original cubic radius alternatives,
with full predecessor centrality and residual transport in the uniform case. -/
theorem rankTwo_or_cubic_plane_predecessor_reduction :
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
        ((∀ v c t : Vertex Rg, color Rg v = false → Adjacent Rg v t → Adjacent Rg c t →
          (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2) ∧
          ∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
            Z Rg z ⊓ B Rg (p.walk.getVert (p.walk.length-2))
                ((sourceGeometry h).Z_normal _) = Z Rg z ⊓ Q Rg a ∧
              (Q Rg a).relIndex (Z Rg z) = 2 ∧
              (Q Rg z).relIndex (Z Rg a) = 2 ∧
              (let N := ⁅Z Rg z ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆
               Nat.card N ≤ 4 ∧ N ≤ Z Rg (p.walk.getVert (p.walk.length-1)) ∧
               N ≤ centralizer (stabilizer Rg (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam Rg))) ∧
              ∀ T : Subgroup (FreeAmalgam Rg), T ≤ Q Rg (p.walk.getVert (p.walk.length-2)) →
                ∀ k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2)),
                  ⁅Z Rg z ⊓ Q Rg a,T.map (MulAut.conj k).toMonoidHom⁆ =
                    ⁅Z Rg z ⊓ Q Rg a,T⁆))) :=
  (coreExhaustion_or_cubic_plane_predecessor_reduction h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
