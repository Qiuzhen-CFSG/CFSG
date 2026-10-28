module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicNaturalCover
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardRigidity
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicMidpointSlices

/-!
# Moving central attachments on strict cubic critical paths

The fixed-hyperplane displacement bound lifts through the actual natural
quotient to the critical line joined with the endpoint's central attachment.
The original edge embeddings transfer this bound to the full reverse seed
kernel and the whole predecessor core. A central commutator on this kernel
must vanish: its natural quotient has a hyperplane fixed pointwise, forcing
the actor image back into the critical transposition. The cubic kernel E
is retained throughout, and only two-subgroups descend from E to Q.

On generating consecutive critical paths a--z and d--c, with midpoints c
and a, a strict moving slice forces [U_d intersect Q_c,X_z intersect Q_a]
to be nonzero. It equals both full-core commutator lines, is central in
G_a and noncentral in G_z. Exchanging lines in the plane above the natural
critical line puts C = C_{U_z}(G_z) inside Z_a; C is noncentral in G_a and
is moved by the actual generating edge. The strict reciprocal slice of the
selected nonabelian span constructs such paths on the original cubic graph.

The whole-core and literal C.1.32 applications preserve the augmentation
action, central attachment, original projection and plane/Sylow alternatives.
These results do not give centrality in G_c or the full-X commutator bound
of (5.12)(1). The terminal contradiction and both reconstruction outcomes
remain obligations of the source assembly.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.7) and (5.12)(1), pp.866--867,919,924--925;
Aschbacher--Smith C.1.31--32, pp.135--136. The representation and line-exchange
arguments adapt Natural.Exhaustion.LargeDistance.SectionFive's
EndpointAttachment, MidpointCoreLine and AttachmentMovement to the literal
cubic quotient and graph; no natural replacement graph is identified with it.
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
include h e hz hk in
/-- The fixed-edge displacement in the whole cover retains its central attachment. -/
theorem cover_fixed_edge_le_line_sup_attachment
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (hA : A ≤ Rg)
    (hne : ¬ A ≤ pCore 2 M)
    (hindex : (centralizer (A : Set M)).relIndex W ≤ 2) :
    ⁅W ⊓ centralizer (A : Set M),Rg⁆ ≤ ⁅W,A⁆ ⊔ (W ⊓ center M) := by
  let := h.relative_normal
  let U := W
  let f := coverMap h e hz hk
  let Dnat := subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map π)
  let T := (Dnat.comap f).toAddSubgroup.toSubgroup'.map U.subtype
  have hnA : A.map π ≠ ⊥ := by
    intro he
    apply hne
    exact two_subgroup_le_core_of_le_extensionKernel h hz A
      (h.relative_radical.isPGroup.to_le hA)
      ((CubicAction.projection_kernel h e hz hk) ▸ (map_eq_bot_iff A).mp he)
  have hsmall : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      W π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk)
      (naturalRepresentation (Fin 6)) f (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (A.map π)).trans hsmall
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
      f (coverAction h e hz hk (π r) (Additive.ofMul ⟨v,hv.1⟩)) ∈ Dnat
    rw [show f (coverAction h e hz hk (π r) (Additive.ofMul ⟨v,hv.1⟩)) =
      naturalRepresentation (Fin 6) (π r) (f (Additive.ofMul ⟨v,hv.1⟩)) from
        coverMap_equivariant h e hz hk _ _]
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
    exact (coverMap_equivariant h e hz hk a _).symm.trans (congrArg f (hfixed a))
  have hmap : (NormalElementaryQuotient.commutatorSpace U A).map f = Dnat := by
    rw [NormalElementaryQuotient.commutatorSpace_eq U π
      (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)]
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction h e hz hk) (MonoidHom.id _) f
      (fun g v => (coverMap_equivariant h e hz hk g v).symm) (A.map π) ⊤
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr (coverMap_surjective h e hz hk),
      Subgroup.map_id] at hh
    exact hh.symm
  apply hT.trans
  rintro x ⟨v,hv,rfl⟩
  change f (Additive.ofMul v) ∈ Dnat at hv
  rw [←hmap] at hv
  obtain ⟨w,hw,he⟩ := hv
  have hkf : f (Additive.ofMul v-w) = 0 := by rw [map_sub,he,sub_self]
  have hkc : ((Additive.ofMul v-w).toMul : M) ∈ center M :=
    moved_fixed_le_center h e hz hk ⟨(Additive.ofMul v-w).toMul.property,
      (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).2.1 _ |>.mp hkf⟩
  have hwc : (w.toMul : M) ∈ ⁅U,A⁆ := hw
  have hh := (⁅U,A⁆ ⊔ (U ⊓ center M)).mul_mem
    (mem_sup_right ⟨(Additive.ofMul v-w).toMul.property,hkc⟩) (mem_sup_left hwc)
  simpa only [toMul_sub,Subgroup.coe_mul,Subgroup.coe_inv,div_eq_mul_inv,
    inv_mul_cancel_right,toMul_ofMul,Subgroup.subtype_apply,U] using hh

include h e hz hk in
/-- The same bound for the full seed through the original oriented edge embedding. -/
theorem small_edge_fixed_le_line_sup_attachment (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hcol : color Rg c = false)
    (hct : Adjacent Rg c t)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t)
    (hne : ¬ A ≤ Q Rg c)
    (hindex : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2) :
    ⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),Q Rg t⁆ ≤
      ⁅U Rg c,A⁆ ⊔ (U Rg c ⊓
        centralizer (stabilizer Rg c : Set (FreeAmalgam Rg))) := by
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
  have hbound_quotient := map_mono (f := i)
    (cover_fixed_edge_le_line_sup_attachment h e hz hk u hR (A.comap i) hAr hAn hidx)
  rw [map_commutator,←map_inf_centralizer_of_injective i hi,hiU,hmA,hiR,
    Subgroup.map_sup,map_commutator,hiU,hmA] at hbound_quotient
  have hatt : (W ⊓ center M).map i ≤
      U Rg c ⊓ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨hiU ▸ mem_map_of_mem i hx.1,?_⟩
    intro y hy
    obtain ⟨m,rfl⟩ := hir ▸ hy
    simpa only [←map_mul] using congrArg i ((mem_center_iff.mp hx.2) m)
  rw [full_fixed_seed_edge_commutator h e hz hcol hct A hA (Q Rg t) le_rfl]
  exact hbound_quotient.trans (sup_le_sup_left hatt _)

include h e hz hk in
/-- The full reverse critical kernel is moved into the critical line and
the endpoint attachment by its whole predecessor core. -/
theorem critical_kernel_predecessor_le_line_sup_attachment
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4) :
    ⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
      ⁅Z Rg a,Z Rg a'⁆ ⊔ (U Rg a' ⊓
        centralizer (stabilizer Rg a' : Set (FreeAmalgam Rg))) := by
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
  have hbnd := small_edge_fixed_le_line_sup_attachment h e hz hk u hR p.end_color hat
    (Z Rg a) hZt p.critical.2 hindex
  rw [←hfixed] at hbnd
  apply ((commutator_mono le_rfl hpred).trans hbnd).trans
  apply sup_le_sup_right
  rw [commutator_comm]
  exact commutator_mono le_rfl (DistanceEight.U_le_Z Rg a')

include h e hz hk in
/-- Central movement of the small actor's fixed hyperplane vanishes,
with the original cubic projection kernel retained. -/
theorem cover_fixed_central_commutator_eq_bot
    (A B : Subgroup M) (hAB : A ≤ B)
    (hAtwo : IsPGroup 2 A)
    (hne : ¬ A ≤ pCore 2 M)
    (hindex : (centralizer (A : Set M)).relIndex W ≤ 2)
    (hcomm : ⁅W ⊓ centralizer (A : Set M),B⁆ ≤
      center M) :
    ⁅W ⊓ centralizer (A : Set M),B⁆ = ⊥ := by
  let := h.relative_normal
  let f := coverMap h e hz hk
  let F := fixedSpace (coverAction h e hz hk) (A.map π)
  let T := fixedSpace (naturalRepresentation (Fin 6)) (B.map π)
  have hfix : F ≤ T.comap f := by
    intro v hv b
    obtain ⟨x,hx,hxb⟩ := b.property
    have hva : (v.toMul : M) ∈ centralizer (A : Set M) :=
      (NormalElementaryQuotient.mem_fixedSpace_image W
        π (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) A v).mp hv
    let z : W := MulAut.conjNormal x v.toMul * v.toMul⁻¹
    have hzC : (z : M) ∈ center M := by
      apply hcomm
      rw [commutator_comm]
      exact commutator_mem_commutator hx ⟨v.toMul.property,hva⟩
    have hz0 : f (Additive.ofMul z) = 0 :=
      ((Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).2.1 _).mpr
        (center_le_centralizer (L.subgroupOf M : Set M) hzC)
    have hzEq : f (Additive.ofMul z) =
        naturalRepresentation (Fin 6) (π x) (f v) - f v := by
      change f (Additive.ofMul (MulAut.conjNormal x v.toMul * v.toMul⁻¹)) = _
      rw [ofMul_mul,ofMul_inv,ofMul_toMul,←sub_eq_add_neg,map_sub]
      exact congrArg (fun w => w - f v)
        ((Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).2.2 x v)
    change naturalRepresentation (Fin 6) b (f v) = f v
    rw [hz0] at hzEq
    rw [←hxb]
    exact sub_eq_zero.mp hzEq.symm
  let q := F.mapQ T f hfix
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨w,rfl⟩ := T.mkQ_surjective v
    obtain ⟨v,rfl⟩ := coverMap_surjective h e hz hk w
    exact ⟨F.mkQ v,rfl⟩
  have hsmall : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      W π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (B.map π) ≤ 1 :=
    (LinearMap.finrank_le_finrank_of_surjective hq).trans hsmall
  have hnA : A.map π ≠ ⊥ := by
    intro he
    exact hne (two_subgroup_le_core_of_le_extensionKernel h hz A hAtwo
      ((CubicAction.projection_kernel h e hz hk) ▸ (map_eq_bot_iff A).mp he))
  have hnB : B.map π ≠ ⊥ := by
    intro he
    exact hnA (le_bot_iff.mp ((map_mono hAB).trans_eq he))
  obtain ⟨t,_,ht,hBt⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers
    (B.map π) hnB hnat
  have hcard : Nat.card (B.map π) = 2 := by
    rw [hBt,Nat.card_zpowers,ht.orderOf]
  have hlo := (one_lt_card_iff_ne_bot (A.map π)).mpr hnA
  have heq : A.map π = B.map π :=
    eq_of_le_of_card_ge (map_mono hAB) (by omega)
  have hB : B ≤ (π).ker ⊔ A := by
    have hh := le_comap_map π B
    rw [←heq,Subgroup.comap_map_eq] at hh
    exact hh.trans_eq (sup_comm _ _)
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  exact hB.trans (sup_le
    ((CubicAction.moved_projection_kernel h e hz hk).le.trans (centralizer_le inf_le_left))
    (le_centralizer_iff.mpr inf_le_right))

include h e hz hk in
/-- A nonzero reverse-kernel commutator with the midpoint core is
noncentral at the endpoint, including on the augmentation cover. -/
theorem four_kernel_core_noncentral
    (hb : sourceDistance h = 4)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4)
    (hne : ⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert 2)⁆ ≠ ⊥) :
    ¬ ⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert 2)⁆ ≤
      centralizer (stabilizer Rg a' : Set (FreeAmalgam Rg)) := by
  intro hcentral
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let c := p.walk.getVert 2
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hdist : (cosetGraph Rg).dist c a' = 2 := by rw [p.dist_end,hl]
  have hQG : Q Rg c ≤ stabilizer Rg a' :=
    Q_le_stabilizer_of_dist_two Rg c a' hcol hdist
  have hZaQ : Z Rg a ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg a ((sourceGeometry h).exists_critical a p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact hb2
  obtain ⟨i,hi,hir,hiQ,_,hiU,_⟩ := graph_cover h e hz hk a' p.end_color
  let A := (Z Rg a).comap i
  let B := (Q Rg c).comap i
  have hmA : A.map i = Z Rg a :=
    map_comap_eq_self ((hZaQ.trans hQG).trans_eq hir.symm)
  have hmB : B.map i = Q Rg c := map_comap_eq_self (hQG.trans_eq hir.symm)
  have hAB : A ≤ B := comap_mono hZaQ
  have hnA : ¬ A ≤ pCore 2 M := by
    intro hh
    have he := map_mono (f := i) hh
    rw [hmA,hiQ] at he
    exact p.critical.2 he
  have hfix : U Rg a' ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) =
      U Rg a' ⊓ Q Rg a := by
    let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
      (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
        a' p.end_color p.critical)
    have hfull := critical_seed_centralizer_intersection h e pr
    have he := congrArg (fun D : Subgroup (FreeAmalgam Rg) => U Rg a' ⊓ D) hfull
    simpa only [←inf_assoc,inf_eq_left.mpr (DistanceEight.U_le_Z Rg a')] using he
  have hmF : (W ⊓ centralizer (A : Set M)).map i =
      U Rg a' ⊓ Q Rg a := by
    rw [←map_inf_centralizer_of_injective i hi,hiU,hmA,hfix]
  have hcF : ⁅W ⊓ centralizer (A : Set M),B⁆ ≤ center M := by
    intro x hx
    apply mem_center_iff.mpr
    intro m
    apply hi
    simp only [map_mul]
    apply hcentral
    · have hh := mem_map_of_mem i hx
      rw [map_commutator,hmF,hmB] at hh
      exact commutator_mono (inf_le_inf_right _ (DistanceEight.U_le_Z Rg a')) le_rfl hh
    · rw [←hir]
      exact ⟨m,rfl⟩
  let := finite_Z Rg a'
  let : Finite (U Rg a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg a')) (inclusion_injective _)
  have hidx : (centralizer (A : Set M)).relIndex W ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,hmF,hiU,
      inf_relIndex_left]
    exact (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg a')
      index_ne_zero_of_finite).trans_eq (small_critical_indices h e hz hk p hsmall).2
  have hzero := congrArg (Subgroup.map i) (cover_fixed_central_commutator_eq_bot h e hz hk A B hAB
    (((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le c hcol).to_le hZaQ).comap_of_injective i hi)
    hnA hidx hcF)
  rw [map_commutator,hmF,hmB,Subgroup.map_bot] at hzero
  have hm := (critical_kernel_predecessor_moving h e hz hb2 p).2.2 (Q Rg c)
    (by simp only [hl,Nat.reduceSub]; exact le_rfl)
  exact hne (hm.trans hzero)


private theorem two_line_exchange {F : Type*} [Group F]
    (H D C : Subgroup F) [Finite D] (hd : Nat.card D = 2)
    (hHD : H ≤ D ⊔ C) (hCN : C ≤ normalizer (D : Set F))
    (hne : ¬ H ≤ C) : D ≤ H ⊔ C := by
  obtain ⟨x,hx,hxC⟩ : ∃ x, x ∈ H ∧ x ∉ C := by
    by_contra hno
    apply hne
    intro x hx
    by_contra hxC
    exact hno ⟨x,hx,hxC⟩
  have hp : x ∈ (D : Set F) * (C : Set F) := by
    rw [←coe_mul_of_right_le_normalizer_left D C hCN]
    exact hHD hx
  obtain ⟨z,hz,c,hc,hzc⟩ := hp
  change z*c=x at hzc
  have hzJ : z ∈ H ⊔ C := by
    have hh := (H ⊔ C).mul_mem (mem_sup_left hx) ((H ⊔ C).inv_mem (mem_sup_right hc))
    rwa [←hzc,mul_inv_cancel_right] at hh
  have hzne : z ≠ 1 := by
    intro he
    rw [he,one_mul] at hzc
    exact hxC (hzc ▸ hc)
  let J := D ⊓ (H ⊔ C)
  let : Finite J := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hJne : J ≠ ⊥ := by
    intro he
    exact hzne (mem_bot.mp (he ▸ (show z ∈ J from ⟨hz,hzJ⟩)))
  have hJcard := (one_lt_card_iff_ne_bot J).mpr hJne
  have heq : J = D := eq_of_le_of_card_ge inf_le_left (by omega)
  exact heq ▸ (inf_le_right : J ≤ H ⊔ C)

include h e hz hk in
private theorem point_shifted_control_of_kernel_zero
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (_hqa : q.walk.getVert 2 = a)
    (hzero : ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg a⁆ = ⊥) :
    let Y := U Rg d ⊓ Q Rg c
    ⁅Y,X Rg z⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ∧
      X Rg z ≤ normalizer ((Y ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  let Y := U Rg d ⊓ Q Rg c
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
/-- A strict backward slice forces the shifted full-omega commutator to be
nonzero, identifies it with both full-core lines, and exposes the endpoint
attachment inside the starting seed but outside its stabilizer center. -/
theorem point_strict_shifted_attachment
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z c d : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hpc : p.walk.getVert 2 = c) (hqa : q.walk.getVert 2 = alpha Rg)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg))
    (hlarge : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) :
    let H := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
    let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
    H = ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆ ∧
      H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆ ∧
      Nat.card H = 2 ∧
      H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) ∧
      C ≤ Z Rg (alpha Rg) ∧
      ¬ C ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      ⁅C,Q Rg (q.walk.getVert 1)⁆ ≠ ⊥ := by
  let H := ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆
  let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  let D := ⁅Z Rg (alpha Rg),Z Rg z⁆
  have hne : H ≠ ⊥ := by
    intro hzH
    have hc := point_shifted_control_of_kernel_zero h e hz hk u hR p q hpc hqa hzH
    have hh := (point_generating_shifted_slice_of_control h e hz hk u hR p q hpc hqa hgen
      ⟨hc.1.trans le_sup_left,hc.2⟩).2
    omega
  have hd := point_shifted_omega_kernel_line h e hz hk u hR p q hpc hqa
  have hback : H = ⁅Z Rg d ⊓ Q Rg c,Q Rg (alpha Rg)⁆ := hd.2.2.1.resolve_left hne
  have hfull : H = ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆ :=
    hback.trans (hd.2.2.2.2.2.2.2.2 hne)
  have hcard : Nat.card H = 2 := hback ▸ hd.1
  have hcentral := (point_generating_shifted_kernel_central h e hz hk u hR p q hpc hqa hgen).2.1
  have hHZ := (point_generating_shifted_kernel_central h e hz hk u hR p q hpc hqa hgen).2.2
  have hb := point_image_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hs : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR p).1]
    decide
  have hnon : ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
    rw [hfull,←hpc]
    exact four_kernel_core_noncentral h e hz hk hb p hs (by rwa [hpc,←hfull])
  have hHD : H ≤ D ⊔ C := by
    have hh := critical_kernel_predecessor_le_line_sup_attachment h e hz hk u hR p hs
    simpa only [hl,Nat.reduceSub,hpc,←hfull] using hh
  have hDZ : D ≤ Z Rg (alpha Rg) := critical_seed_commutator_le h p
  have hDZ' : D ≤ Z Rg z := by
    change ⁅Z Rg (alpha Rg),Z Rg z⁆ ≤ Z Rg z
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) z p.end_color (by
        rw [(sourceGeometry h).distance_constant _ p.end_color]
        exact sourceDistance_pos h)
        (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
          _ p.start_color (by
            rw [(sourceGeometry h).distance_constant _ p.start_color]
            exact sourceDistance_pos h) _ p.end_color p.critical)).trans (Z_normalized Rg z))
  have hCN : C ≤ normalizer (D : Set (FreeAmalgam Rg)) :=
    ((inf_le_right : C ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))).trans
      (centralizer_le (hDZ'.trans (Z_le_stabilizer Rg z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hDN : D ≤ normalizer (C : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp ((inf_le_right : C ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))).trans
      (centralizer_le (hDZ'.trans (Z_le_stabilizer Rg z))))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hDc : Nat.card D = 2 := (point_image_critical_indices_two h e hz hk u hR p).2.2
  have hCc : Nat.card C = 2 := point_graph_central_attachment_card_two h e hz hk u hR z p.end_color
  let : Finite D := Nat.finite_of_card_ne_zero (by rw [hDc]; decide)
  let : Finite C := Nat.finite_of_card_ne_zero (by rw [hCc]; decide)
  have hnotD : ¬ H ≤ D := by
    intro hh
    have he : H = D := eq_of_le_of_card_ge hh (by rw [hcard,hDc])
    exact critical_commutator_not_central h e hz hk p
      (he.ge.trans hcentral)
  have hC : C ≤ H ⊔ D := two_line_exchange H C D hCc (hHD.trans_eq (sup_comm D C)) hDN hnotD
  have hD : D ≤ H ⊔ C := two_line_exchange H D C hDc hHD hCN (fun hh => hnon (hh.trans inf_le_right))
  have hCn : ¬ C ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    intro hc
    exact critical_commutator_not_central h e hz hk p (hD.trans (sup_le hcentral hc))
  refine ⟨hback,hfull,hcard,hcentral,hnon,hC.trans (sup_le hHZ hDZ),hCn,?_⟩
  intro hzC
  apply hCn
  apply le_centralizer_iff.mp
  rw [←hgen]
  exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzC))
    (le_centralizer_iff.mp ((inf_le_right : C ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))).trans
      (centralizer_le (Z_le_stabilizer Rg z))))
include h e hz hk in
/-- A strict forward slice constructs the generating backward path, and
identifies its shifted kernel with the full opposite-core line. -/
theorem point_strict_forward_attachment
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hindex : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
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
      ⁅C,Q Rg (q.walk.getVert 1)⁆ ≠ ⊥ := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
  obtain ⟨d,t,x,hx,hxd,hat,hdt,hgen,q,hq1,hover⟩ :=
    full_point_backward_step_of_strict_forward h e hz hk u
      (full_point_image_of_contained h e hz hk u hR) p hindex
  have hpc : p.walk.getVert 2 = p.walk.getVert (p.walk.length-2) := by rw [hl]
  have hqa : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hgen' : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg (alpha Rg) := by rwa [hq1]
  have hlarge : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) := by
    have hBmap : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
        (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        (geometry := sourceGeometry h) hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hx))
    rw [←hxd,U_act,←hBmap,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hindex
  exact ⟨d,q,hqa,hgen',point_strict_shifted_attachment h e hz hk u hR p q hpc hqa hgen' hlarge⟩

include h e hz hk in
/-- The strict reciprocal slice on the actual selected span supplies a
critical path on the original graph with a moving endpoint attachment.
The reciprocal orientation is transported by the literal graph action. -/
theorem point_exists_strict_attachment
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    ∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
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
        ⁅C,Q Rg (q.walk.getVert 1)⁆ ≠ ⊥ := by
  have hstrict : ∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
      2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2)) := by
    obtain ⟨z,p,hcard,hcentral,hradius⟩ := point_image_selected_span_radius_line h e hz hk u hR
    have hnon : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
        localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ := by
      intro he
      rw [he,card_bot] at hcard
      omega
    rcases point_selected_reciprocal_slice_alternative h e hz hk u hR p hnon with hforward | hreverse
    · exact ⟨z,p,hforward⟩
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
    exact ⟨_,q0,hq0⟩
  obtain ⟨z,p,hindex⟩ := hstrict
  exact ⟨z,p,hindex,point_strict_forward_attachment h e hz hk u hR p hindex⟩

omit hk in
include h e hz in
/-- Whole-core application of the forced moving attachment on the original cubic graph. -/
theorem coreExhaustion_or_cubic_attachment_movement :
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
              ⁅C,Q Rg (q.walk.getVert 1)⁆ ≠ ⊥)) ∨
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
      point_exists_strict_attachment h e hz hk u hpoint.2.le⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application with the nonzero shifted line and the
attachment moved by its actual generating edge. -/
theorem rankTwo_or_cubic_attachment_movement :
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
              ⁅C,Q Rg (q.walk.getVert 1)⁆ ≠ ⊥)) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_attachment_movement h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
