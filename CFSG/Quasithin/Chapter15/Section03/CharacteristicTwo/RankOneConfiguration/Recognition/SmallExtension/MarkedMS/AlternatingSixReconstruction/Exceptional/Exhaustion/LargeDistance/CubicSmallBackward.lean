module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicForwardKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SmallBackward

/-!
# Small-image backward shifts with the cubic kernel retained

The fixed subgroup of a nontrivial transposition on either entire moving
cover has at most one dimension of displacement under a conjugate point
core. We apply the representation theorem from SmallBackward to the
original cubic-cover action. Its augmentation displacement line is not
identified with the critical moved line: the central vector remains.
Transport through the literal endpoint and edge embeddings gives an
order-two commutator bound on the full fixed seed. Conversely, a commutator
of order at most two has fixed index at most two on the entire cover.

The full initial kernel E centralizes the endpoint seed. Its exact
small-critical-kernel centralizer therefore bounds the predecessor
commutator by the original critical line, without replacing E by Q.
An escaping two-subgroup detects the component on every normal section;
this puts the normalized fixed-seed product in the starting Baumann slice.
The small displacement bound contradicts a prescribed slice index greater
than two, giving the backward critical noncontainment.

In the full point-core branch, an even conjugate constructs a generating
edge in the symmetric quotient. Perfectness removes the possible supplement
to E/Q and lifts generation to the original stabilizer. One conjugator
transports the prescribed slice and first edge, with every overlap vertex
of the resulting critical walk identified. The whole-core and literal
C.1.32 applications retain both cover orders and the actual quotient map.
Point-core containment is assumed only where used; full point-core equality
is required for the constructed generating edge and is not inferred from
containment. No initial-natural or center-free input is used.

This supplies the small-image backward step under these literal source
choices, not the full selected-path theorem (5.11). The other radical-image
choices, strict slice selection, R4/R6 exclusions, distance-four exclusion
and final reconstruction remain with qt-e-ms-small-a6-reconstruction.
Independent natural exhaustion remains with
qt-e-ms-small-a6-exhaustion-large-distance.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), pp.866--867;
the fixed-seed argument in (5.7), p.919, used in (5.11), pp.923--924.
Adapts Natural.Exhaustion.LargeDistance.SectionFive.SmallBackward,
SmallKernel and ForwardClosure, retaining the cubic covering kernel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
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
private abbrev coverAction : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive W) := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation W π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)
private def coverMap : Additive W →ₗ[ZMod 2] natural (Fin 6) :=
  Classical.choose (CubicAction.moved_natural_projection h e hz hk)
private theorem coverMap_surjective : Function.Surjective (coverMap h e hz hk) :=
  (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).1
private theorem coverMap_equivariant (g : Equiv.Perm (Fin 6)) (v : Additive W) :
    coverMap h e hz hk (coverAction h e hz hk g v) =
      naturalRepresentation (Fin 6) g (coverMap h e hz hk v) := by
  let := h.relative_normal
  obtain ⟨a,rfl⟩ := CubicEven.projection_surjective h e hz hk g
  have he : coverAction h e hz hk (π a) v = Additive.ofMul (MulAut.conjNormal a v.toMul) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply W π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) a v
  rw [he]
  exact (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).2.2 a v


omit hk in
include h e hz in
private theorem vertex_seed_eq_moving_sup_edge {c b : Vertex Rg}
    (hc : color Rg c = false) (hcb : Adjacent Rg c b) :
    Z Rg c = U Rg c ⊔ Z Rg b := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common Rg c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    have hb := CubicAction.graph_Z_eq_moved_sup_edge h e hz (base_adjacent Rg)
    rw [graph_U_map h e hz] at hb
    have he := congrArg (fun A : Subgroup (FreeAmalgam Rg) =>
      A.map (MulAut.conj g⁻¹).toMonoidHom) hb
    rw [Subgroup.map_sup,←Z_act,←U_act,←Z_act] at he
    simpa [alpha,beta] using he
  · rw [hg.1] at hc
    cases hc

include h e hz hk in
/-- The full cover's fixed hyperplane has at most two commutators with a
point-core radical, retaining the possible central line. -/
theorem cover_small_fixed_edge_card (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (hA : A ≤ Rg)
    (hne : ¬ A ≤ pCore 2 M)
    (hindex : (centralizer (A : Set M)).relIndex (W) ≤ 2) :
    Nat.card (⁅W ⊓ centralizer (A : Set M),Rg⁆ :
      Subgroup M) ≤ 2 := by
  let := h.relative_normal
  let U := W
  let D := subspaceCommutator (coverAction h e hz hk) (fixedSpace (coverAction h e hz hk) (A.map π))
    (pointCore.map (MulAut.conj u).toMonoidHom)
  let T := D.toAddSubgroup.toSubgroup'.map U.subtype
  have hsmall : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (W) π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk) (naturalRepresentation (Fin 6))
      (coverMap h e hz hk)
      (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (A.map π)).trans hsmall
  have hnA : A.map π ≠ ⊥ := by
    intro he
    apply hne
    exact two_subgroup_le_core_of_le_extensionKernel h hz A
      (h.relative_radical.isPGroup.to_le hA)
      (CubicAction.projection_kernel h e hz hk ▸ (map_eq_bot_iff A).mp he)
  have hdim : Module.finrank (ZMod 2) D ≤ 1 :=
    AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SmallBackward.model_small_fixed_movement (coverAction h e hz hk) (moved_subgroup_cover_model h e hz hk) u
      (A.map π) ((map_mono hA).trans hR) hnA hnat
  have hc : ⁅U ⊓ centralizer (A : Set M),Rg⁆ ≤ T := by
    apply commutator_le.mpr
    intro v hv r hr
    have hcu : ⁅v,r⁆ ∈ U := (commutator_le_left U Rg)
      (commutator_mem_commutator hv.1 hr)
    refine ⟨⟨⁅v,r⁆,hcu⟩,?_,rfl⟩
    change Additive.ofMul (⟨⁅v,r⁆,hcu⟩ : U) ∈ D
    rw [NormalElementaryQuotient.vector_commutator U π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) ⟨v,hv.1⟩ r]
    apply D.neg_mem_iff.mp
    rw [neg_sub]
    apply Submodule.subset_span
    refine ⟨π r,hR (mem_map_of_mem _ hr),Additive.ofMul ⟨v,hv.1⟩,?_,rfl⟩
    exact (NormalElementaryQuotient.mem_fixedSpace_image U π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) A _).mpr hv.2
  apply (card_le_of_le hc).trans
  rw [card_map_of_injective U.subtype_injective]
  change Nat.card D ≤ 2
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact (Nat.pow_le_pow_right (by decide : 0<2) hdim)

include h e hz hk in
/-- A commutator of order at most two has fixed index at most two on the
whole marked cover. The cyclic image is deduced through the natural quotient. -/
theorem cover_small_commutator_fixed_index (A : Subgroup M)
    (hcard : Nat.card (⁅W,A⁆ : Subgroup M) ≤ 2) :
    (centralizer (A : Set M)).relIndex (W) ≤ 2 := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 (⁅W,A⁆ : Subgroup M) :=
    IsElementaryAbelian.of_le (commutator_le_left (W) A)
  let f := coverMap h e hz hk
  let D := subspaceCommutator (coverAction h e hz hk) ⊤ (A.map π)
  have hDcard : Nat.card D ≤ 2 := by
    have he := Nat.card_congr (NormalElementaryQuotient.movedEquiv
      (W) π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) A).toEquiv
    change Nat.card (⁅W,A⁆ : Subgroup M) = Nat.card D at he
    rwa [←he]
  have hDdim : Module.finrank (ZMod 2) D ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hDcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hDcard
  have hm : D.map f = subspaceCommutator (naturalRepresentation (Fin 6)) ⊤
      (A.map π) := by
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction h e hz hk) (MonoidHom.id (Equiv.Perm (Fin 6))) f
      (fun g v => (coverMap_equivariant h e hz hk g v).symm) (A.map π) ⊤
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr (coverMap_surjective h e hz hk),Subgroup.map_id] at hh
    exact hh.symm
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 := by
    rw [←NaturalPairing.moved_finrank_eq_fixedCodim,←hm]
    exact (Submodule.finrank_map_le f D).trans hDdim
  have hsmall : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    by_cases he : A.map π = ⊥
    · rw [he,(fixedCodim_eq_zero_iff (coverAction h e hz hk) ⊥).mpr (fixedSpace_bot (coverAction h e hz hk))]
      omega
    · obtain ⟨t,_,_,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers
        (A.map π) he hnat
      change Module.finrank (ZMod 2) (subspaceCommutator (coverAction h e hz hk) ⊤
        (A.map π)) ≤ 1 at hDdim
      rw [he,Representation.CyclicFixedRank.commutator_eq_range,
        ←fixedCodim_zpowers_eq_displacement_rank] at hDdim
      rwa [he]
  rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
    (W) π (CubicEven.projection_surjective h e hz hk)
    (CubicAction.moved_projection_kernel h e hz hk)]
  exact Nat.pow_le_pow_right (by decide : 0<2) hsmall

include h e hz hk in
/-- The same inverse movement bound on the actual full cover at any vertex. -/
theorem moving_small_commutator_fixed_index {c : Vertex Rg} (hcol : color Rg c = false)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ stabilizer Rg c)
    (hcard : Nat.card (⁅U Rg c,A⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2) :
    (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2 := by
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,hiC⟩ := graph_cover h e hz hk c hcol
  have hmA : (A.comap i).map i = A := map_comap_eq_self (hA.trans_eq hir.symm)
  have hh : Nat.card (⁅W,A.comap i⁆ : Subgroup M) ≤ 2 := by
    rw [←card_map_of_injective hi,map_commutator,hiU,hmA]
    exact hcard
  have hf := cover_small_commutator_fixed_index h e hz hk (A.comap i) hh
  rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
    map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
    inf_relIndex_left]
  exact hf

include h e hz hk in
/-- The fixed part of the entire endpoint seed has at most two commutators
with its incident edge kernel. No equality with the critical moved line is used. -/
theorem small_edge_fixed_card_at (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hcol : color Rg c = false)
    (hct : Adjacent Rg c t)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t)
    (hne : ¬ A ≤ Q Rg c)
    (hindex : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2) :
    Nat.card (⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),Q Rg t⁆ :
      Subgroup (FreeAmalgam Rg)) ≤ 2 := by
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
  have hcard := cover_small_fixed_edge_card h e hz hk u hR (A.comap i) hAr hAn hidx
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

include h e in
private theorem reverse_pair {a c : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a c) :
    CriticalPair Rg c a ((sourceGeometry h).exists_critical c p.end_color) :=
  critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
    a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
    c p.end_color p.critical

include h e hz hk in
/-- Every subgroup of the opposite stabilizer fixing the literal critical
kernel has its entire endpoint commutator in the same critical line. -/
theorem small_critical_kernel_commutator {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg))
    (hY : Y ≤ stabilizer Rg a')
    (hfix : Y ≤ centralizer (Z Rg a' ⊓ Q Rg a : Set (FreeAmalgam Rg))) :
    ⁅Y,Z Rg a'⁆ ≤ ⁅Z Rg a,Z Rg a'⁆ := by
  let q : CriticalPath Rg (sourceGeometry h) a' a :=
    CriticalPath.ofPair p.end_color (reverse_pair h e p)
  have hs : (Q Rg a).relIndex (Z Rg a') < 4 := by
    rw [(small_critical_indices h e hz hk p hsmall).2]
    decide
  have hjoin := (le_inf hY hfix).trans (small_critical_kernel_centralizer h e hz hk q hs)
  have hZa : Z Rg a ≤ stabilizer Rg a' :=
    Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hQ : (stabilizer Rg a' ⊓ centralizer (X Rg a' : Set (FreeAmalgam Rg))) ≤
      centralizer (Z Rg a' : Set (FreeAmalgam Rg)) :=
    inf_le_right.trans (centralizer_le ((sourceGeometry h).omega_bound a' p.end_color (by
      rw [(sourceGeometry h).distance_constant a' p.end_color]
      exact sourceDistance_pos h)))
  have he := commutator_eq_of_centralizing_sup
    (show (stabilizer Rg a' ⊓ centralizer (X Rg a' : Set (FreeAmalgam Rg))) ⊔ Z Rg a = (stabilizer Rg a' ⊓ centralizer (X Rg a' : Set (FreeAmalgam Rg))) ⊔ Z Rg a from rfl)
    hQ (hZa.trans (Z_normalized Rg a'))
  rw [commutator_comm Y,commutator_comm (Z Rg a)]
  exact (commutator_mono le_rfl hjoin).trans_eq he.symm

include h in
private theorem critical_seed_commutator_le {a c : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a c) : ⁅Z Rg a,Z Rg c⁆ ≤ Z Rg a := by
  apply le_normalizer_iff_commutator_le_left.mp
  exact (critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
    (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
    p.critical).trans (Z_normalized Rg a)

include h e hz hk in
/-- Fixing the opposite critical kernel is enough for the source predecessor
commutator bound, independently of the radical image and cover order. -/
theorem small_critical_predecessor_commutator (hb : 2 < sourceDistance h) {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg))
    (hY : Y ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hfix : Y ≤ centralizer (Z Rg a' ⊓ Q Rg a : Set (FreeAmalgam Rg))) :
    ⁅Y,Z Rg a'⁆ ≤ Z Rg a := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let t := p.walk.getVert (p.walk.length-1)
  have hat : Adjacent Rg a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1 = p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hct : Adjacent Rg (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1 = p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hYt := hY.trans (Q_le_adjacent_h Rg ht hct)
  have hYe : Y ≤ stabilizer Rg a' := fun y hy =>
    (hYt hy).2 _ (adjacent_symm Rg hat)
  exact (small_critical_kernel_commutator h e hz hk p hsmall Y hYe hfix).trans
    (critical_seed_commutator_le h p)

omit hk in
include h e hz in
/-- A normal radius subgroup fixed modulo the seed by a critical actor
is contained in the actual Baumann slice. -/
theorem normalized_radius_le_slice_of_critical_commutator
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (D : Subgroup (FreeAmalgam Rg)) (hDV : D ≤ V Rg (alpha Rg))
    (hDN : stabilizer Rg (alpha Rg) ≤ normalizer (D : Set (FreeAmalgam Rg)))
    (hcomm : ⁅D,Z Rg a'⁆ ≤ Z Rg (alpha Rg)) :
    D ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  let D₀ := D.comap (embedM Rg)
  let Z₀ := (Z Rg (alpha Rg)).comap (embedM Rg)
  let A₀ := (Z Rg a').comap (embedM Rg)
  have hDG : D ≤ (embedM Rg).range :=
    (hDV.trans ((sourceGeometry h).V_local (alpha Rg) rfl hb)).trans_eq (stabilizer_m_base Rg)
  have hDm : D₀.map (embedM Rg) = D := map_comap_eq_self hDG
  have hZm : Z₀.map (embedM Rg) = Z Rg (alpha Rg) :=
    map_comap_eq_self ((Z_le_stabilizer Rg (alpha Rg)).trans_eq (stabilizer_m_base Rg))
  have hAm : A₀.map (embedM Rg) = Z Rg a' := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  have hg (m : M) : embedM Rg m ∈ stabilizer Rg (alpha Rg) := by
    change embedM Rg m ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : D₀.Normal := ⟨by
    intro z hd m
    change embedM Rg (m*z*m⁻¹) ∈ D
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hDN (hg m)) (embedM Rg z)).mp hd⟩
  let : Z₀.Normal := ⟨by
    intro z hd m
    change embedM Rg (m*z*m⁻¹) ∈ Z Rg (alpha Rg)
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp ((Z_normalized Rg _) (hg m)) (embedM Rg z)).mp hd⟩
  have hcomm₀ : ⁅D₀,A₀⁆ ≤ Z₀ := by
    apply (map_le_map_iff_of_injective (embedM_injective Rg)).mp
    rwa [map_commutator,hDm,hAm,hZm]
  have hne : ¬ A₀ ≤ pCore 2 M := by
    intro he
    have hh := map_mono (f := embedM Rg) he
    rw [hAm,←Q_alpha Rg (h.relative_radical.isPGroup) (h.relative_radical.twoCore_le)] at hh
    exact (reverse_pair h e p).2 hh
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color
  have hAtwo : IsPGroup 2 A₀ :=
    (IsElementaryAbelian.isPGroup 2 (Z Rg a')).comap_of_injective _ (embedM_injective Rg)
  have hDL := CubicAction.normal_commutator_le_of_escaping_two h e hz D₀ Z₀ A₀ hAtwo hne hcomm₀
  have hm := map_mono (f := embedM Rg) hDL
  rw [map_commutator,hDm,hZm,show (L.subgroupOf (L ⊔ R)).map (embedM Rg) = Ltilde Rg (alpha Rg) by
    rw [Ltilde_alpha,h.relative_residual]] at hm
  intro z hd
  apply (mem_B_iff Rg (alpha Rg) _ ((sourceGeometry h).V_local (alpha Rg) rfl hb) z).mpr
  refine ⟨hDV hd,?_⟩
  intro l hl
  rw [commutator_comm] at hm
  exact hm (commutator_mem_commutator hl hd)

private theorem abelian_action_preserves_fixed {H : Type*} [Group H]
    (P V A : Subgroup H) (hPV : P ≤ normalizer (V : Set H)) (hA : A ≤ P)
    (hcom : ⁅P,P⁆ ≤ centralizer (V : Set H)) :
    P ≤ normalizer ((V ⊓ centralizer (A : Set H) : Subgroup H) : Set H) := by
  let f : P →* MulAut V := V.normalizerMonoidHom.comp (inclusion hPV)
  have hf (p q : P) : Commute (f p) (f q) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    ext v
    change ⁅(p:H),(q:H)⁆*(v:H)*⁅(p:H),(q:H)⁆⁻¹ = (v:H)
    rw [←hcom (commutator_mem_commutator p.property q.property) v v.property,mul_inv_cancel_right]
  apply le_normalizer_iff.mpr
  intro g hg v hv
  have hgv : g*v*g⁻¹ ∈ V := (mem_normalizer_iff.mp (hPV hg) v).mp hv.1
  refine ⟨hgv,?_⟩
  intro a ha
  have hvfix : f ⟨a,hA ha⟩ ⟨v,hv.1⟩ = (⟨v,hv.1⟩:V) := by
    apply Subtype.ext
    change a*v*a⁻¹ = v
    rw [hv.2 a ha,mul_inv_cancel_right]
  have hh := DFunLike.congr_fun (hf ⟨a,hA ha⟩ ⟨g,hg⟩).eq (⟨v,hv.1⟩:V)
  change f ⟨a,hA ha⟩ (f ⟨g,hg⟩ ⟨v,hv.1⟩) = f ⟨g,hg⟩ (f ⟨a,hA ha⟩ ⟨v,hv.1⟩) at hh
  rw [hvfix] at hh
  have he : a*(g*v*g⁻¹)*a⁻¹ = g*v*g⁻¹ := congrArg Subtype.val hh
  exact mul_inv_eq_iff_eq_mul.mp he

include h e hz hk in
private theorem edge_preserves_seed_fixer (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hcol : color Rg c = false)
    (hct : Adjacent Rg c t)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t) :
    Q Rg t ≤ normalizer ((Z Rg c ⊓ centralizer
      (A : Set (FreeAmalgam Rg)) : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  let := pointCore_elementary
  let : IsElementaryAbelian 2 (pointCore.map (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
  let helem : IsElementaryAbelian 2 ((Rg).map π) := IsElementaryAbelian.of_le hR
  have hcore : ⁅Rg,Rg⁆ ≤ pCore 2 M := by
    apply two_subgroup_le_core_of_le_extensionKernel h hz ⁅Rg,Rg⁆
      (h.relative_radical.isPGroup.to_le ((Subgroup.commutator_le_sup Rg Rg).trans (sup_idem Rg).le))
    rw [←CubicAction.projection_kernel h e hz hk,←Subgroup.map_eq_bot_iff,map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr helem.toIsMulCommutative)
  have hbase : ⁅Q Rg (beta Rg),Q Rg (beta Rg)⁆ ≤ Q Rg (alpha Rg) := by
    rw [Q_beta,Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le,←map_commutator]
    exact map_mono hcore
  have hderived : ⁅Q Rg t,Q Rg t⁆ ≤ Q Rg c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common Rg c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hbase
      rw [map_commutator,←Q_act,←Q_act] at hh
      simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using hh
    · rw [hg.1] at hcol
      cases hcol
  have htG : Q Rg t ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  exact abelian_action_preserves_fixed _ _ A (htG.trans (Z_normalized Rg c)) hA
    (hderived.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg c hcol))))

include h e hz hk in
/-- In the small-original-image branch, a generating edge transports a
slice of index greater than two to a backward critical noncontainment.
The displacement line may differ from the original critical line. -/
theorem small_image_backward_not_le (hb : 2 < sourceDistance h) (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg))
    (hindex : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg c)) :
    ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  let K := Z Rg a' ⊓ Q Rg (alpha Rg)
  let F := Z Rg c ⊓ centralizer (K : Set (FreeAmalgam Rg))
  let Y := F ⊔ Z Rg (alpha Rg)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h1
    cases hc : color Rg c <;> cases ht : color Rg t <;> simp_all
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hdist : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    have h1 : (cosetGraph Rg).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h2 : (cosetGraph Rg).dist t (alpha Rg) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    simpa only [h1,h2] using (cosetGraph_connected Rg).dist_triangle
      (u := c) (v := t) (w := alpha Rg)
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)
  have hFt := edge_preserves_seed_fixer h e hz hk u hR hcol hct K
    (inf_le_right.trans (Q_le_adjacent_h Rg ht hat))
  have hmove : ⁅F,Z Rg a'⁆ ≤ Z Rg (alpha Rg) :=
    small_critical_predecessor_commutator h e hz hk hb p hsmall F
      (inf_le_left.trans hbad) inf_le_right
  have hYmove : ⁅Y,Z Rg a'⁆ ≤ Z Rg (alpha Rg) :=
    commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      F (Z Rg (alpha Rg)) (Z Rg a') (Z Rg (alpha Rg))
      (Z_normalized Rg _) ((inf_le_left.trans hZV).trans
        ((sourceGeometry h).V_local _ rfl hb)) (Z_le_stabilizer Rg _) hmove
      (critical_seed_commutator_le h p)
  have hYn : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    apply sup_le
    · exact (le_inf hFt ((show Q Rg t ≤ stabilizer Rg (alpha Rg) from
        fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hYmove.trans le_sup_right)
  have hFB : F ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    le_sup_left.trans (normalized_radius_le_slice_of_critical_commutator h e hz hb p Y
      (sup_le (inf_le_left.trans hZV) (Z_le_VBall Rg _ 2)) hYn hYmove)
  let last := p.walk.getVert (p.walk.length-1)
  have helast : Adjacent Rg a' last := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1 = p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hlast : color Rg last = true := by
    have hh := adjacent_color_ne Rg helast
    rw [p.end_color] at hh
    cases he : color Rg last <;> simp_all
  have hpred : Q Rg (p.walk.getVert (p.walk.length-2)) ≤ Q Rg last := by
    apply Q_le_adjacent_h Rg hlast
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hZlast : Z Rg (alpha Rg) ≤ Q Rg last := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ rfl)
    rw [(sourceGeometry h).distance_constant _ rfl,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-1 < sourceDistance h
    omega
  let q : CriticalPath Rg (sourceGeometry h) a' (alpha Rg) :=
    CriticalPath.ofPair p.end_color (reverse_pair h e p)
  have hKfixed : K = Z Rg a' ⊓ centralizer
      (Z Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e q).symm
  let := finite_Z Rg a'
  let : Finite (U Rg a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg a')) (inclusion_injective _)
  have hfixindex : (centralizer (Z Rg (alpha Rg) : Set (FreeAmalgam Rg))).relIndex
      (U Rg a') ≤ 2 := by
    have hh : Q Rg (alpha Rg) ≤ centralizer
        (Z Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg _ rfl))
    exact ((relIndex_le_of_le_left hh index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg a') index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p hsmall).2
  have hcard := small_edge_fixed_card_at h e hz hk u hR p.end_color helast
    (Z Rg (alpha Rg)) hZlast p.critical.2 hfixindex
  rw [←hKfixed] at hcard
  let := finite_stabilizer Rg last
  let : Finite (Q Rg last) := Finite.of_injective
    (inclusion (show Q Rg last ≤ stabilizer Rg last from fun _ hx => hx.1)) (inclusion_injective _)
  have hKlast : K ≤ Q Rg last :=
    inf_le_left.trans (show Z Rg a' ≤ Q Rg last from
      (show Z Rg a' ≤ Q Rg a' from by
        apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
        rw [SimpleGraph.dist_self,(sourceGeometry h).distance_constant _ p.end_color]
        exact sourceDistance_pos h).trans (Q_le_adjacent_h Rg hlast helast))
  let : Finite (⁅K,Q Rg last⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion ((Subgroup.commutator_le_sup K (Q Rg last)).trans (sup_le hKlast le_rfl))) (inclusion_injective _)
  have hline : Nat.card (⁅U Rg c,K⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
    rw [commutator_comm]
    exact (card_le_of_le (commutator_mono le_rfl
      (((DistanceEight.U_le_Z Rg c).trans hbad).trans hpred))).trans hcard
  have hKc : K ≤ stabilizer Rg c :=
    (inf_le_right.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hidx := moving_small_commutator_fixed_index h e hz hk hcol K hKc hline
  let := finite_Z Rg c
  let : Finite (U Rg c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg c)) (inclusion_injective _)
  have hh := relIndex_le_of_le_left
    ((inf_le_inf_right _ (DistanceEight.U_le_Z Rg c)).trans hFB)
    (index_ne_zero_of_finite (H := (U Rg c ⊓ centralizer
      (K : Set (FreeAmalgam Rg))).subgroupOf (U Rg c)))
  rw [inf_relIndex_left] at hh
  exact (Nat.not_le_of_gt hindex) (hh.trans hidx)

include h e hz hk in
/-- A small critical actor selects a generating neighbor in the full
point-core branch. Perfectness lifts generation across the retained cubic
kernel, while both central-cover orders remain possible. -/
theorem small_image_full_point_generating_neighbor
    (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) := by
  let := h.relative_normal
  let A := (Z Rg a').comap (embedM Rg)
  have hmapA : A.map (embedM Rg) = Z Rg a' := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  have hne : ¬ A ≤ pCore 2 M := by
    intro hn
    have hh := map_mono (f := embedM Rg) hn
    rw [hmapA,←Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hh
    exact (reverse_pair h e p).2 hh
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color
  have hAtwo : IsPGroup 2 A :=
    (IsElementaryAbelian.isPGroup 2 (Z Rg a')).comap_of_injective _ (embedM_injective Rg)
  have hAn : A.map π ≠ ⊥ := by
    intro hn
    apply hne
    exact two_subgroup_le_core_of_le_extensionKernel h hz A hAtwo
      (CubicAction.projection_kernel h e hz hk ▸ (map_eq_bot_iff A).mp hn)
  let := finite_Z Rg (alpha Rg)
  let : Finite (U Rg (alpha Rg)) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg (alpha Rg))) (inclusion_injective _)
  have hC : Q Rg a' ≤ centralizer (Z Rg a' : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a' p.end_color))
  have hidx : (centralizer (Z Rg a' : Set (FreeAmalgam Rg))).relIndex (U Rg (alpha Rg)) ≤ 2 :=
    ((relIndex_le_of_le_left hC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg (alpha Rg)) index_ne_zero_of_finite)).trans_eq
      (small_critical_indices h e hz hk p hsmall).1
  have hidx' : (centralizer (A : Set M)).relIndex W ≤ 2 := by
    rw [←graph_U_map h e hz,←hmapA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective _ (embedM_injective Rg),
      relIndex_map_map_of_injective _ _ (embedM_injective Rg),inf_relIndex_left] at hidx
    exact hidx
  have hcodim : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim W π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)] at hidx'
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hidx'
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk) (naturalRepresentation (Fin 6))
      (coverMap h e hz hk) (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (A.map π)).trans hcodim
  obtain ⟨a,ha,hswap,_⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers (A.map π) hAn hnat
  obtain ⟨k,hkgen⟩ := PointCoreEvenGeneration.exists_even_conjugate_pointCore_generates_swap u a hswap
  have hkL : k.val ∈ (L.subgroupOf (L ⊔ R)).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact k.property
  obtain ⟨g,hg,hgk⟩ := hkL
  have hm : ((Rg).map (MulAut.conj g).toMonoidHom).map π =
      ((Rg).map π).map (MulAut.conj k.val).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change π (g*x*g⁻¹) = k.val*π x*k.val⁻¹
    rw [map_mul,map_mul,map_inv,hgk]
  have hQ : (pCore 2 M).map (MulAut.conj g).toMonoidHom = pCore 2 M :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  let F := (Rg).map (MulAut.conj g).toMonoidHom ⊔ A
  have hQF : pCore 2 M ≤ F := by
    rw [←hQ]
    exact (map_mono h.relative_radical.twoCore_le).trans le_sup_left
  have hfullF : F.map π = ⊤ := by
    rw [Subgroup.map_sup,hm,hfull]
    apply top_unique
    rw [←hkgen]
    exact sup_le_sup_left (zpowers_le.mpr ha) _
  have hFE : F ⊔ extensionKernel h = ⊤ := by
    have he := congrArg (Subgroup.comap π) hfullF
    rwa [comap_map_eq,CubicAction.projection_kernel h e hz hk,comap_top] at he
  have hEF : extensionKernel h ≤ F := by
    have he := extensionKernel_no_supplement h F (hFE ▸ le_top)
    rw [extensionKernel_twoCore h,sup_of_le_left hQF] at he
    exact he
  have hgen : (Rg).map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
    change F = ⊤
    rwa [sup_of_le_left hEF] at hFE
  let f := (embedM Rg g)⁻¹
  have hf : f ∈ stabilizer Rg (alpha Rg) := by
    change f ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act Rg f (alpha Rg) = alpha Rg := hf
  refine ⟨act Rg f (beta Rg),?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff Rg f (alpha Rg) (beta Rg)).mpr
      (base_adjacent Rg)
  · have hmapA : A.map (embedM Rg) = Z Rg a' :=
      map_comap_eq_self ((critical_Z_le_stabilizer Rg (sourceGeometry h)
        (alpha Rg) rfl (sourceDistance_pos h) p.critical).trans_eq
          (stabilizer_m_base Rg))
    have hh := congrArg (Subgroup.map (embedM Rg)) hgen
    rw [Subgroup.map_sup,hmapA,←MonoidHom.range_eq_map] at hh
    rw [Q_act,Q_beta]
    change _ = stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    have hmapR : ((Rg).map (embedM Rg)).map (MulAut.conj f⁻¹).toMonoidHom =
        ((Rg).map (MulAut.conj g).toMonoidHom).map (embedM Rg) := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f⁻¹*embedM Rg x*(f⁻¹)⁻¹=embedM Rg (g*x*g⁻¹)
      simp only [f,inv_inv,map_mul,map_inv]
    rw [hmapR]
    exact hh

include h e hz hk in
/-- The small-original-image backward step on a prescribed slice and
generating edge. The same conjugator retains every overlapping vertex. -/
theorem small_image_backward_shift_of_two_lt_slice
    (hb : 2 < sourceDistance h)
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' delta t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hdelta : Adjacent Rg delta (p.walk.getVert 1))
    (hindex : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg delta))
    (hat : Adjacent Rg (alpha Rg) t)
    (hgen : Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg)) :
    ∃ g ∈ stabilizer Rg (alpha Rg),
      act Rg g (p.walk.getVert 1) = t ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g delta)
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (act Rg g delta)) := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) ha1 hat
  let c := act Rg g delta
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g delta (p.walk.getVert 1)).mpr hdelta
  have hcol : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h1
    cases hc : color Rg c <;> cases ht : color Rg t <;> simp_all
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
  have hindexc : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg c) := by
    change 2 < (B Rg (alpha Rg) _).relIndex (U Rg (act Rg g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hindex
  have hbad : ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    exact small_image_backward_not_le h e hz hk hb u hR p hsmall hat hct hgen hindexc
  let w : (cosetGraph Rg).Walk c (alpha Rg) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hct)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  exact ⟨g,hg,hgt,q,hqt,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi,hindexc⟩

include h e hz hk in
/-- For a full point-core radical image, the small-image backward shift
constructs its generating edge in the original group, retaining the cubic
kernel, both cover orders and every overlapping vertex. -/
theorem small_full_point_backward_shift
    (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hdelta : Adjacent Rg delta (p.walk.getVert 1))
    (hindex : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg delta)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
      ∃ g ∈ stabilizer Rg (alpha Rg),
        act Rg g (p.walk.getVert 1) = t ∧
        ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g delta)
          (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (act Rg g delta)) := by
  obtain ⟨t,hat,hgen⟩ := small_image_full_point_generating_neighbor h e hz hk u hfull p hsmall
  exact ⟨t,hat,hgen,small_image_backward_shift_of_two_lt_slice h e hz hk
    (distance_gt_two h e hz hk) u hfull.le p hsmall hdelta hindex hat hgen⟩

omit hk in
include h e hz in
/-- Whole-core application of the actual small-image shift. Point-core
identification and the source strict-slice selection remain explicit branches;
the action, cubic kernel, generating edge and path construction are discharged. -/
theorem coreExhaustion_or_cubic_small_backward :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ u : Equiv.Perm (Fin 6),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ a' delta : Vertex Rg,
        ∀ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
        (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
        Adjacent Rg delta (p.walk.getVert 1) →
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta) →
        ∃ t, Adjacent Rg (alpha Rg) t ∧
          Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
          ∃ g ∈ stabilizer Rg (alpha Rg),
            act Rg g (p.walk.getVert 1) = t ∧
            ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g delta)
              (p.walk.getVert (p.walk.length-2)),
              q.walk.getVert 1 = t ∧
              (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
              2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
                (U Rg (act Rg g delta)) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,fun u hu a' delta p hp hd hi =>
      small_full_point_backward_shift h e hz hk u hu p hp hd hi⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application with the same quotient map and whole covers.
Final exclusion of the retained cubic branch remains with the reconstruction owner. -/
theorem rankTwo_or_cubic_small_backward :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ u : Equiv.Perm (Fin 6),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ a' delta : Vertex Rg,
        ∀ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
        (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
        Adjacent Rg delta (p.walk.getVert 1) →
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta) →
        ∃ t, Adjacent Rg (alpha Rg) t ∧
          Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
          ∃ g ∈ stabilizer Rg (alpha Rg),
            act Rg g (p.walk.getVert 1) = t ∧
            ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g delta)
              (p.walk.getVert (p.walk.length-2)),
              q.walk.getVert 1 = t ∧
              (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
              2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
                (U Rg (act Rg g delta)) :=
  (coreExhaustion_or_cubic_small_backward h e hz).imp (rankTwo_of_exhaustion h e hz) id


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
