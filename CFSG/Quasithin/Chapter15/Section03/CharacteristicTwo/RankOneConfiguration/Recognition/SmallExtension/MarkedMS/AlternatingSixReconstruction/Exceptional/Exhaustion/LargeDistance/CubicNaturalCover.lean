module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardRigidity
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicMidpointSlices

/-!
# Excluding the natural moving cover in the cubic point branch

The point-core action on the fixed hyperplane of a transposition has
displacement in that transposition's natural line. When the entire moving
cover has order sixteen, its literal natural quotient is injective, so this
bound holds in the cover itself. Edge embeddings transfer it to the full
reverse seed kernel and its predecessor-core commutator.

On the original generating consecutive critical paths, the shifted
full-omega kernel commutator is central at the starting vertex. If nontrivial,
the bound identifies it with the starting critical line, contradicting that
line's noncentrality. Its vanishing gives full-omega control and normalization
of the backward moving kernel joined to the starting seed. The generating
edge then forces a midpoint slice of index at most two. This contradicts
the proved strict reciprocal slice on the same selected nonabelian span,
after the original graph conjugation when necessary.

Thus the point branch has the augmentation cover of order thirty-two, with
its original action marking and its central attachment of order two. The
whole-core and literal C.1.32 applications retain the selected paths, central
derived line, original projection with kernel E and odd E/Q, and the
plane/Sylow alternatives. This eliminates only the order-sixteen point branch;
the augmentation commutator contradiction and the other reconstruction
obligations still remain.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), pp.866--867, and (5.12)(1), pp.924--925;
Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local notation "Rg" => edge L R
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
private abbrev naturalCoverAction : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive W) := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation W π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)
private def naturalCoverMap : Additive W →ₗ[ZMod 2] natural (Fin 6) :=
  Classical.choose (CubicAction.moved_natural_projection h e hz hk)
private theorem naturalCoverMap_surjective : Function.Surjective (naturalCoverMap h e hz hk) :=
  (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).1
private theorem naturalCoverMap_equivariant (g : Equiv.Perm (Fin 6)) (v : Additive W) :
    naturalCoverMap h e hz hk (naturalCoverAction h e hz hk g v) =
      naturalRepresentation (Fin 6) g (naturalCoverMap h e hz hk v) := by
  let := h.relative_normal
  obtain ⟨a,rfl⟩ := CubicEven.projection_surjective h e hz hk g
  have he : naturalCoverAction h e hz hk (π a) v = Additive.ofMul (MulAut.conjNormal a v.toMul) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply W π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) a v
  rw [he]
  exact (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).2.2 a v

include h e hz hk in
/-- The natural quotient is injective for the order-sixteen cover, so the
point-core fixed-hyperplane displacement bound holds in the whole cover. -/
theorem cover_fixed_edge_le_line_of_sixteen
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hcard : Nat.card W = 16)
    (A : Subgroup M) (hA : A ≤ Rg)
    (hne : ¬ A ≤ pCore 2 M)
    (hindex : (centralizer (A : Set M)).relIndex W ≤ 2) :
    ⁅W ⊓ centralizer (A : Set M),Rg⁆ ≤ ⁅W,A⁆ := by
  let := h.relative_normal
  let U := W
  let f := naturalCoverMap h e hz hk
  let Dnat := subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map π)
  let T := (Dnat.comap f).toAddSubgroup.toSubgroup'.map U.subtype
  have hnA : A.map π ≠ ⊥ := by
    intro he
    apply hne
    exact two_subgroup_le_core_of_le_extensionKernel h hz A
      (h.relative_radical.isPGroup.to_le hA)
      ((CubicAction.projection_kernel h e hz hk) ▸ (map_eq_bot_iff A).mp he)
  have hsmall : fixedCodim (naturalCoverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      W π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (naturalCoverAction h e hz hk)
      (naturalRepresentation (Fin 6)) f (naturalCoverMap_surjective h e hz hk)
      (naturalCoverMap_equivariant h e hz hk) (A.map π)).trans hsmall
  have hdisp := PointCoreTranspositionFixed.small_image_fixed_displacement_le u
    (A.map π) ((map_mono hA).trans hR) hnA hnat
  have hT : ⁅U ⊓ centralizer (A : Set M),Rg⁆ ≤ T := by
    apply commutator_le.mpr
    intro v hv r hr
    have hcu : ⁅v,r⁆ ∈ U := (commutator_le_left U Rg)
      (commutator_mem_commutator hv.1 hr)
    refine ⟨⟨⁅v,r⁆,hcu⟩,?_,rfl⟩
    change f (Additive.ofMul (⟨⁅v,r⁆,hcu⟩ : U)) ∈ Dnat
    rw [NormalElementaryQuotient.vector_commutator U π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) ⟨v,hv.1⟩ r,map_sub]
    change f (Additive.ofMul ⟨v,hv.1⟩) -
      f (naturalCoverAction h e hz hk (π r) (Additive.ofMul ⟨v,hv.1⟩)) ∈ Dnat
    rw [show f (naturalCoverAction h e hz hk (π r) (Additive.ofMul ⟨v,hv.1⟩)) =
      naturalRepresentation (Fin 6) (π r) (f (Additive.ofMul ⟨v,hv.1⟩)) from
        naturalCoverMap_equivariant h e hz hk _ _]
    apply Dnat.neg_mem_iff.mp
    rw [neg_sub]
    apply hdisp
    apply Submodule.subset_span
    refine ⟨π r,hR (mem_map_of_mem _ hr),f (Additive.ofMul ⟨v,hv.1⟩),?_,rfl⟩
    have hfixed := (NormalElementaryQuotient.mem_fixedSpace_image U π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) A
      (Additive.ofMul ⟨v,hv.1⟩)).mpr hv.2
    intro a
    change naturalRepresentation (Fin 6) a (f (Additive.ofMul ⟨v,hv.1⟩)) =
      f (Additive.ofMul ⟨v,hv.1⟩)
    exact (naturalCoverMap_equivariant h e hz hk a _).symm.trans (congrArg f (hfixed a))
  have hfcard : Nat.card (natural (Fin 6)) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      finrank_natural_even (Fin 6) (by decide)]
    rfl
  have hfi : Function.Injective f :=
    (naturalCoverMap_surjective h e hz hk).bijective_of_nat_card_le
      (by change Nat.card W ≤ Nat.card (natural (Fin 6)); omega) |>.1
  have hmap : (NormalElementaryQuotient.commutatorSpace U A).map f = Dnat := by
    rw [NormalElementaryQuotient.commutatorSpace_eq U π
      (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)]
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (naturalCoverAction h e hz hk) (MonoidHom.id _) f
      (fun g v => (naturalCoverMap_equivariant h e hz hk g v).symm) (A.map π) ⊤
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr (naturalCoverMap_surjective h e hz hk),
      Subgroup.map_id] at hh
    exact hh.symm
  have hpre : Dnat.comap f = NormalElementaryQuotient.commutatorSpace U A := by
    rw [←hmap,Submodule.comap_map_eq_of_injective hfi]
  apply hT.trans
  rintro x ⟨v,hv,rfl⟩
  change Additive.ofMul v ∈ Dnat.comap f at hv
  rw [hpre] at hv
  exact hv

include h e hz hk in
/-- The same bound for the full seed at the actual oriented edge. The edge
seed contributes no displacement, and the cubic projection kernel is retained. -/
theorem small_edge_fixed_le_line_of_sixteen
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hcard : Nat.card W = 16)
    {c t : Vertex Rg} (hcol : color Rg c = false) (hct : Adjacent Rg c t)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t)
    (hne : ¬ A ≤ Q Rg c)
    (hindex : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2) :
    ⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),Q Rg t⁆ ≤ ⁅Z Rg c,A⁆ := by
  have hcoords : ∃ i : M →* FreeAmalgam Rg, Function.Injective i ∧
      (Rg).map i = Q Rg t ∧ (pCore 2 M).map i = Q Rg c ∧
      (W).map i = U Rg c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common Rg c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM Rg)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective Rg),?_,?_,?_⟩
      · have he := Q_act Rg g (beta Rg)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
      · have he := Q_act Rg g (alpha Rg)
        rw [Q_alpha Rg (h.relative_radical.isPGroup) (h.relative_radical.twoCore_le)] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := U_act Rg g (alpha Rg)
        rw [←graph_U_map h e hz] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · rw [hg.1] at hcol
      cases hcol
  obtain ⟨i,hi,hiR,hiQ,hiU⟩ := hcoords
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
  have hidx : (centralizer (A.comap i : Set M)).relIndex (W) ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hbnd := cover_fixed_edge_le_line_of_sixteen h e hz hk u hR hcard
    (A.comap i) hAr hAn hidx
  have hm := map_mono (f := i) hbnd
  rw [map_commutator,←map_inf_centralizer_of_injective i hi,hiU,hmA,hiR,
    map_commutator,hiU,hmA] at hm
  rw [full_fixed_seed_edge_commutator h e hz hcol hct A hA (Q Rg t) le_rfl]
  exact hm.trans (commutator_mono (DistanceEight.U_le_Z Rg c) le_rfl)


include h e hz hk in
/-- At a small critical pair, the reverse full-seed kernel has predecessor
commutator contained in the original critical line for the order-sixteen cover. -/
theorem critical_kernel_predecessor_le_line_of_sixteen
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hcard : Nat.card W = 16)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4) :
    ⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
      ⁅Z Rg a,Z Rg a'⁆ := by
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
  have hbnd := small_edge_fixed_le_line_of_sixteen h e hz hk u hR hcard p.end_color hat
    (Z Rg a) hZt p.critical.2 hindex
  rw [←hfixed,commutator_comm (Z Rg a')] at hbnd
  exact (commutator_mono le_rfl hpred).trans hbnd

include h e hz hk in
/-- The generating backward edge forces the shifted full-omega kernel
commutator to vanish in the order-sixteen branch. -/
theorem point_generating_shifted_kernel_eq_bot_of_sixteen
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hcard : Nat.card W = 16)
    {a z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = a)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg a) :
    ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆ = ⊥ := by
  let R₁ := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆
  have hdata := point_shifted_omega_kernel_line h e hz hk u hR p q hpc hqa
  have hcentral := (point_generating_shifted_kernel_central h e hz hk u hR p q hpc hqa hgen).2.1
  have hl : p.walk.length = 4 := p.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
  have hs : (Q Rg z).relIndex (Z Rg a) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR p).1]
    decide
  have hbound := critical_kernel_predecessor_le_line_of_sixteen h e hz hk u hR hcard p hs
  rw [hl,show 4-2=2 from rfl,hpc] at hbound
  by_contra hne
  have hRline : R₁ = ⁅Z Rg a,Z Rg z⁆ := by
    have hRH : R₁ = ⁅Z Rg z ⊓ Q Rg a,Q Rg c⁆ :=
      (hdata.2.2.1.resolve_left hne).trans (hdata.2.2.2.2.2.2.2.2 hne)
    have hcardline := (point_image_critical_indices_two h e hz hk u hR p).2.2
    let : Finite (⁅Z Rg a,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) :=
      Nat.finite_of_card_ne_zero (by rw [hcardline]; decide)
    have hRcard : Nat.card R₁ = 2 := by
      change Nat.card (⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆ : Subgroup (FreeAmalgam Rg)) = 2
      rw [hdata.2.2.1.resolve_left hne]
      exact hdata.1
    exact eq_of_le_of_card_ge (hRH ▸ hbound) (by rw [hRcard,hcardline])
  exact critical_commutator_not_central h e hz hk p (hRline ▸ hcentral)

include h e hz hk in
/-- Vanishing of the shifted kernel supplies the full-X commutator bound
and normalization on these same consecutive critical paths. -/
theorem point_generating_shifted_control_of_sixteen
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hcard : Nat.card W = 16)
    {a z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = a)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg a) :
    let Y := U Rg d ⊓ Q Rg c
    ⁅Y,X Rg z⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ∧
      X Rg z ≤ normalizer ((Y ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  let Y := U Rg d ⊓ Q Rg c
  have hzero := point_generating_shifted_kernel_eq_bot_of_sixteen h e hz hk u hR hcard p q hpc hqa hgen
  have hs : (Q Rg z).relIndex (Z Rg a) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR p).1]
    decide
  have hl : p.walk.length = 4 := p.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
  have hYG : Y ≤ stabilizer Rg z :=
    inf_le_right.trans (Q_le_stabilizer_of_dist_le_two c z q.end_color p.end_color (by
      rw [←hpc,p.dist_end,hl]))
  have hbound := small_critical_omega_kernel_control h e hz hk p hs Y hYG
    (commutator_eq_bot_iff_le_centralizer.mp hzero)
  have hreverse := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
    a p.start_color (by
      rw [(sourceGeometry h).distance_constant _ p.start_color]
      exact sourceDistance_pos h) z p.end_color p.critical
  have hXN : X Rg z ≤ normalizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (critical_X_le_vertex h e z p.end_color a hreverse).trans (Z_normalized Rg a)
  refine ⟨hbound,?_⟩
  rw [sup_comm Y]
  apply normalizes_join_of_displacement _ _ _ hXN
  rw [commutator_comm]
  exact hbound.trans (critical_seed_commutator_le h p)

include h e hz hk in
/-- For an order-sixteen moving cover, a generating backward shift rules
out a strict forward midpoint slice. -/
theorem point_forward_slice_le_two_of_sixteen
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hcard : Nat.card W = 16)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2 := by
  by_contra hnot
  have hindex : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) := by omega
  have hb := distance_gt_two h e hz hk
  have hb4 := point_image_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  obtain ⟨d,t,x,hx,hxd,hat,hdt,hgen,q,hq1,hover⟩ :=
    full_point_backward_step_of_strict_forward h e hz hk u
      (full_point_image_of_contained h e hz hk u hR) p hindex
  have hpc : p.walk.getVert 2 = p.walk.getVert (p.walk.length-2) := by rw [hl]
  have hqa : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hgen' : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) := by
    rwa [hq1]
  have hcontrol := point_generating_shifted_control_of_sixteen h e hz hk u hR hcard p q hpc hqa hgen'
  have hsmall := (point_generating_shifted_slice_of_control h e hz hk u hR p q hpc hqa hgen'
    ⟨hcontrol.1.trans le_sup_left,hcontrol.2⟩).2
  have hBmap : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      (geometry := sourceGeometry h) hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hx))
  rw [←hxd,U_act,←hBmap,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective] at hsmall
  omega

include h e hz hk in
/-- The strict reciprocal slice on the selected nonabelian span excludes
the entire order-sixteen moving-cover case in the cubic point branch. -/
theorem point_moved_card_eq_thirtytwo
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    Nat.card W = 32 := by
  rcases moved_card h e hz hk with hcard | hcard
  · exfalso
    obtain ⟨z,p,hderived,hcentral,hradius⟩ := point_image_selected_span_radius_line h e hz hk u hR
    have hnon : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
        localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ := by
      intro he
      rw [he,card_bot] at hderived
      omega
    rcases point_selected_reciprocal_slice_alternative h e hz hk u hR p hnon with hforward | hreverse
    · exact (Nat.not_lt_of_ge (point_forward_slice_le_two_of_sixteen h e hz hk u hR hcard p)) hforward
    obtain ⟨_,x,hx,q,_,hqa,_⟩ :=
      selected_span_conjugate_critical_path h (distance_gt_two h e hz hk) p hnon
    have hqindex : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (q.walk.getVert 2)) := by rwa [hqa]
    obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg q.start_color
    have hbase : act Rg g⁻¹ (p.walk.getVert 2) = alpha Rg := by
      rw [hg,act_mVertex,mul_inv_cancel]
      rfl
    have hs : 2 < (B Rg (act Rg g⁻¹ (p.walk.getVert 2))
        ((sourceGeometry h).Z_normal _)).relIndex (U Rg ((q.act g⁻¹).walk.getVert 2)) := by
      simp only [CriticalPath.act,actWalk_getVert]
      rw [Escape.PairingControl.FirstPairing.B_act (distance_gt_two h e hz hk) g⁻¹ _ q.start_color,
        U_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
      exact hqindex
    have hq0 : ∃ q0 : CriticalPath Rg (sourceGeometry h)
        (act Rg g⁻¹ (p.walk.getVert 2)) (act Rg g⁻¹ (act Rg x (p.walk.getVert 2))),
        2 < (B Rg (act Rg g⁻¹ (p.walk.getVert 2)) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (q0.walk.getVert 2)) := ⟨q.act g⁻¹,hs⟩
    rw [hbase] at hq0
    obtain ⟨q0,hq0⟩ := hq0
    exact (Nat.not_lt_of_ge (point_forward_slice_le_two_of_sixteen h e hz hk u hR hcard q0)) hq0
  · exact hcard

include h e hz hk in
/-- Transport of the forced cover order through the original graph action. -/
theorem point_graph_moved_card_eq_thirtytwo
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (a : Vertex Rg) (ha : color Rg a = false) : Nat.card (U Rg a) = 32 := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color Rg ha
  have hu := U_act Rg g (alpha Rg)
  simp only [alpha,act_mVertex,one_mul] at hu
  rw [hu,card_map_of_injective (MulAut.conj g⁻¹).injective]
  change Nat.card (U Rg (alpha Rg)) = 32
  rw [←graph_U_map h e hz,card_map_of_injective (embedM_injective Rg)]
  exact point_moved_card_eq_thirtytwo h e hz hk u hR

include h e hz hk in
/-- The actual fixed attachment of the moving cover has order two at
every component vertex; it is not discarded when passing to the natural quotient. -/
theorem point_graph_central_attachment_card_two
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (a : Vertex Rg) (ha : color Rg a = false) :
    Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
      Subgroup (FreeAmalgam Rg)) = 2 := by
  obtain ⟨_,_,_,_,_,_,f,hf,hker,_⟩ := graph_cover h e hz hk a ha
  have hr : Nat.card f.range = 16 := by
    rw [MonoidHom.range_eq_top.mpr hf,Nat.card_congr topEquiv.toEquiv]
    change Nat.card (natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      finrank_natural_even (Fin 6) (by decide)]
    rfl
  have hc := f.ker.card_mul_index
  rw [index_ker,hr,point_graph_moved_card_eq_thirtytwo h e hz hk u hR a ha] at hc
  have hkc : Nat.card f.ker = 2 := by omega
  have he : f.ker.map (U Rg a).subtype =
      U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    rw [hker]
    change ((centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))).comap
      (U Rg a).subtype).map (U Rg a).subtype = _
    rw [map_comap_eq,range_subtype,inf_comm]
  rw [←he,card_map_of_injective (U Rg a).subtype_injective]
  exact hkc

include h e hz hk in
/-- The remaining whole moved cover is the actual binary augmentation
module, with the original cubic projection and conjugation action. -/
theorem point_moved_core_model
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    let := h.relative_normal
    ∃ E : Additive W ≃ₗ[ZMod 2] core (Fin 6),
      ∀ (g : M) (v : Additive W),
        E (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
          coreRepresentation (Fin 6) (π g) (E v) := by
  let := h.relative_normal
  rcases moved_subgroup_cover_model h e hz hk with ⟨E,_⟩ | ⟨E,hE⟩
  · have hc := point_moved_card_eq_thirtytwo h e hz hk u hR
    change Nat.card (Additive W) = 32 at hc
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod,finrank_natural_even (Fin 6) (by decide)] at hc
    norm_num at hc
  · refine ⟨E,?_⟩
    intro g v
    have he : naturalCoverAction h e hz hk (π g) v =
        Additive.ofMul (MulAut.conjNormal g v.toMul) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact NormalElementaryQuotient.representation_apply W π
        (CubicEven.projection_surjective h e hz hk)
        (CubicAction.moved_projection_kernel h e hz hk) g v
    exact (congrArg E he).symm.trans (hE (π g) v)

omit hk in
include h e hz in
/-- Whole-core application: the point branch has the actual augmentation cover,
with order 32 and a central attachment of order two at every component vertex. -/
theorem coreExhaustion_or_cubic_point_augmentation :
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
            ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
              (p.walk.getVert (p.walk.length-2)),
            q.walk.getVert 2 = alpha Rg ∧
            let c := p.walk.getVert (p.walk.length-2)
            let P := localZSpan Rg c (alpha Rg)
            let H := ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆
            let R₁ := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
            Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
            Nat.card H = 2 ∧ (R₁ = ⊥ ∨ R₁ = H) ∧
            R₁ ≤ Z Rg (alpha Rg) ⊓ Z Rg c ∧
            R₁ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            R₁ = ⁅U Rg d ⊓ Q Rg c,Z Rg z ⊓ Q Rg (alpha Rg)⁆ ∧
            (R₁ ≠ ⊥ → H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_radical_cases h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint.2,hpoint.1,
      point_moved_core_model h e hz hk u hpoint.2.le,
      fun a ha => ⟨point_graph_moved_card_eq_thirtytwo h e hz hk u hpoint.2.le a ha,
        point_graph_central_attachment_card_two h e hz hk u hpoint.2.le a ha⟩,
      fun a ha => ⟨point_omega_central_generation h e hz hk u hpoint.2.le a ha,
        point_omega_eq_seed h e hz hk u hpoint.2.le a ha⟩,
      point_image_selected_central_omega h e hz hk u hpoint.2.le⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application: the order-16 point branch is eliminated while
the central attachment, original projection and plane/Sylow alternatives remain. -/
theorem rankTwo_or_cubic_point_augmentation :
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
            ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d
              (p.walk.getVert (p.walk.length-2)),
            q.walk.getVert 2 = alpha Rg ∧
            let c := p.walk.getVert (p.walk.length-2)
            let P := localZSpan Rg c (alpha Rg)
            let H := ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆
            let R₁ := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
            Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅P,P⁆ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            ⁅P,V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
            Nat.card H = 2 ∧ (R₁ = ⊥ ∨ R₁ = H) ∧
            R₁ ≤ Z Rg (alpha Rg) ⊓ Z Rg c ∧
            R₁ ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
            R₁ = ⁅U Rg d ⊓ Q Rg c,Z Rg z ⊓ Q Rg (alpha Rg)⁆ ∧
            (R₁ ≠ ⊥ → H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_point_augmentation h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
