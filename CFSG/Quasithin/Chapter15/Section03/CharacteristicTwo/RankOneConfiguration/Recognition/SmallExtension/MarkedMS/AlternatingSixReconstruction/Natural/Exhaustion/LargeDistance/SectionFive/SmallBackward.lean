module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardSlice

/-!
# Backward critical shifts for both full central covers

The point core moves a transposition's fixed subgroup into a line on either
of the permitted covers. On the augmentation cover this line is generated
by the four-coordinate word, whereas the critical transposition moves the
complementary duad word. Their difference is the retained central vector.
A small checked calculation on eight permutations and binary six-tuples
proves the bound before conjugation and equivariant transport. No equality
between these two lines, splitting, or zero fixed-subgroup premise is used.

Transport through the original quotient and edge embedding bounds the
commutator of the entire critical kernel with the last edge by two. Conversely,
a commutator of order at most two on the full cover has fixed index at most
two: projection to the natural quotient determines a cyclic transposition
image, and cyclic rank-nullity applies on the original cover.

For the backward step, the fixed subgroup of that critical kernel is
normalized by the selected edge. Its opposite-seed commutator lies in the
starting seed, by the exact small-kernel centralizer theorem. Generation
therefore puts the fixed subgroup in the starting Baumann slice. The
preceding index bound contradicts a prescribed slice index greater than two,
proving the missing small-original-image noncontainment. Combining this with
`BackwardSlice` handles both original-image sizes. In the full point-core
branch the generating edge is constructed for every critical image. The
original replacement application retains one transporter, the prescribed
first edge, and every overlapping path vertex, for both cover orders.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), (5.5)(a) and (5.7),
printed pp.866--867,915--919. The fixed-subgroup and normal-product arguments
adapt SymplecticSetup.SmallEdgeFixed and BackwardComplete, retaining the
augmentation cover rather than identifying it with its natural quotient.

The source still must supply the small-slice backward selection, the remaining
upper slice bounds, exact-four radius exclusion, intermediate R4/R6
noncentrality and both terminal contradictions. Those obligations and the
unconditional distance-two application remain with
qt-e-ms-small-a6-exhaustion-large-distance; whole-core reconstruction remains
with qt-e-ms-small-a6-reconstruction. This module does not assert a terminal
distance exclusion from the new backward estimates alone.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace SmallBackward
local notation "ρ" => coreRepresentation (Fin 6)
private abbrev a : S := swap01 * swap23
private abbrev b : S := Equiv.swap 0 2 * Equiv.swap 1 3
private def eight : List S := [1,a,b,a*b,swap45,swap45*a,swap45*b,swap45*(a*b)]
private theorem eight_closed : ∀ x ∈ eight, ∀ y ∈ eight, x*y ∈ eight := by
  have h : eight.all (fun x => eight.all (fun y => decide (x*y ∈ eight))) = true := by decide +kernel
  simpa only [List.all_eq_true,decide_eq_true_eq] using h
private theorem eight_inverses : ∀ x ∈ eight, x⁻¹ ∈ eight := by
  have h : eight.all (fun x => decide (x⁻¹ ∈ eight)) = true := by decide +kernel
  simpa only [List.all_eq_true,decide_eq_true_eq] using h
private def certificate : Subgroup S where
  carrier := {x | x ∈ eight}
  one_mem' := by decide +kernel
  mul_mem' := fun hx hy => eight_closed _ hx _ hy
  inv_mem' := eight_inverses _
private theorem core_in_certificate : pointCore ≤ certificate := by
  rw [pointCore_eq_closure,closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl <;> change _ ∈ eight <;> decide +kernel
private def lineVector : C := pairWord 0 1 + pairWord 2 3
private theorem displacement_certificate :
    ∀ g ∈ eight, ∀ v : Full (Fin 6), (∑ i, v i) = 0 → v 4 = v 5 →
      ∃ c : ZMod 2, representation (Fin 6) g v-v = c • lineVector.val := by
  have h : eight.all (fun g => decide (∀ v : Full (Fin 6), (∑ i, v i) = 0 → v 4 = v 5 →
    ∃ c : ZMod 2, representation (Fin 6) g v-v = c • lineVector.val)) = true := by
    decide +kernel
  simpa only [List.all_eq_true,decide_eq_true_eq] using h

private theorem canonical_displacement (g : S) (hg : g ∈ pointCore)
    (v : C) (hv : ρ swap45 v = v) :
    ρ g v-v ∈ Submodule.span (ZMod 2) {lineVector} := by
  have h45 : v.val 4 = v.val 5 := by
    have hh := congrArg (fun w : C => w.val 5) hv
    exact hh
  obtain ⟨c,hc⟩ := displacement_certificate g (core_in_certificate hg) v.val v.property h45
  exact Submodule.mem_span_singleton.mpr ⟨c,Subtype.ext hc.symm⟩

private theorem core_fixed_displacement_line (u t : S)
    (ht : t ∈ pointCore.map (MulAut.conj u).toMonoidHom) (hs : t.IsSwap) :
    subspaceCommutator ρ (fixedSpace ρ (zpowers t))
      (pointCore.map (MulAut.conj u).toMonoidHom) ≤
        Submodule.span (ZMod 2) {ρ u lineVector} := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,v,hv,rfl⟩
  have ht' := PointCoreTranspositionFixed.swap_eq_conjugate u t ht hs
  rw [ht'] at hv
  obtain ⟨k,hk,he⟩ := hg
  change u*k*u⁻¹=g at he
  rw [←he]
  let w := ρ u⁻¹ v
  have hw : ρ swap45 w=w := by
    have hh := (mem_fixedSpace_zpowers_iff _ _ _).mp hv
    have hh' := congrArg (ρ u⁻¹) hh
    simpa only [map_mul,Module.End.mul_apply,(ρ).inv_self_apply] using hh'
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (canonical_displacement k hk w hw)
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c,?_⟩
  have hh := congrArg (ρ u) hc
  rw [map_smul,map_sub] at hh
  simpa only [w,map_mul,Module.End.mul_apply,(ρ).self_inv_apply] using hh

private theorem fixed_movement_finrank_transport
    {Y W : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) S Y) (τ : Representation (ZMod 2) S W)
    (E : Y ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (σ g v) = τ g (E v))
    (A P : Subgroup S) :
    Module.finrank (ZMod 2) (subspaceCommutator σ (fixedSpace σ A) P) =
      Module.finrank (ZMod 2) (subspaceCommutator τ (fixedSpace τ A) P) := by
  have hF : (fixedSpace σ A).map E.toLinearMap = fixedSpace τ A := by
    ext w
    constructor
    · rintro ⟨v,hv,rfl⟩ a
      change τ a (E v) = E v
      exact (hE a v).symm.trans (congrArg E (hv a))
    · intro hw
      obtain ⟨v,rfl⟩ := E.surjective w
      refine ⟨v,?_,rfl⟩
      intro a
      apply E.injective
      change E (σ a v) = E v
      exact (hE a v).trans (hw a)
  have hm := subspaceCommutator_map_embedding τ σ (MonoidHom.id S) E.toLinearMap
    (fun g v => (hE g v).symm) P (fixedSpace σ A)
  rw [hF,map_id] at hm
  rw [hm,LinearEquiv.finrank_map_eq]

/-- The fixed hyperplane has at most a line of displacement in either full
cover. The line in the augmentation cover is retained in its original coordinates. -/
theorem model_small_fixed_movement
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (u : S) (A : Subgroup S)
    (hA : A ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hne : A ≠ ⊥) (hsmall : fixedCodim (naturalRepresentation (Fin 6)) A ≤ 1) :
    Module.finrank (ZMod 2) (subspaceCommutator σ (fixedSpace σ A)
      (pointCore.map (MulAut.conj u).toMonoidHom)) ≤ 1 := by
  obtain ⟨t,ht,hs,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers A hne hsmall
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
  · rw [fixed_movement_finrank_transport σ (naturalRepresentation (Fin 6)) E hE]
    have hh := Submodule.finrank_mono
      (PointCoreTranspositionFixed.small_image_fixed_displacement_le u A hA hne hsmall)
    apply hh.trans
    rw [he,PointCoreTranspositionFixed.moved_finrank u t (hA ht) hs]
  · rw [fixed_movement_finrank_transport σ ρ E hE,he]
    exact (Submodule.finrank_mono (core_fixed_displacement_line u t (hA ht) hs)).trans
      (by simpa using (finrank_span_le_card (R := ZMod 2) ({ρ u lineVector} : Set C)))

end SmallBackward

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
open scoped commutatorElement IsMulCommutative Pointwise
open Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

include s in
/-- The full cover's fixed hyperplane has at most two commutators with a
point-core radical, retaining the possible central line. -/
theorem cover_small_fixed_edge_card (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup d.overgroup) (hA : A ≤ d.radical)
    (hne : ¬ A ≤ pCore 2 d.overgroup)
    (hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2) :
    Nat.card (⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),d.radical⁆ :
      Subgroup d.overgroup) ≤ 2 := by
  let := replacementMoved_normal h d
  let U := replacementMoved d
  let D := subspaceCommutator (coverAction s) (fixedSpace (coverAction s) (A.map s.projection))
    (pointCore.map (MulAut.conj u).toMonoidHom)
  let T := D.toAddSubgroup.toSubgroup'.map U.subtype
  have hsmall : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) (A.map s.projection)).trans hsmall
  have hnA : A.map s.projection ≠ ⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff A).mp he)
  have hdim : Module.finrank (ZMod 2) D ≤ 1 :=
    SmallBackward.model_small_fixed_movement (coverAction s) (cover_model s) u
      (A.map s.projection) ((map_mono hA).trans hR) hnA hnat
  have hc : ⁅U ⊓ centralizer (A : Set d.overgroup),d.radical⁆ ≤ T := by
    apply commutator_le.mpr
    intro v hv r hr
    have hcu : ⁅v,r⁆ ∈ U := (commutator_le_left U d.radical)
      (commutator_mem_commutator hv.1 hr)
    refine ⟨⟨⁅v,r⁆,hcu⟩,?_,rfl⟩
    change Additive.ofMul (⟨⁅v,r⁆,hcu⟩ : U) ∈ D
    rw [NormalElementaryQuotient.vector_commutator U s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm) ⟨v,hv.1⟩ r]
    apply D.neg_mem_iff.mp
    rw [neg_sub]
    apply Submodule.subset_span
    refine ⟨s.projection r,hR (mem_map_of_mem _ hr),Additive.ofMul ⟨v,hv.1⟩,?_,rfl⟩
    exact (NormalElementaryQuotient.mem_fixedSpace_image U s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm) A _).mpr hv.2
  apply (card_le_of_le hc).trans
  rw [card_map_of_injective U.subtype_injective]
  change Nat.card D ≤ 2
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact (Nat.pow_le_pow_right (by decide : 0<2) hdim)

include s in
/-- A commutator of order at most two has fixed index at most two on the
whole marked cover. The cyclic image is deduced through the natural quotient. -/
theorem cover_small_commutator_fixed_index (A : Subgroup d.overgroup)
    (hcard : Nat.card (⁅replacementMoved d,A⁆ : Subgroup d.overgroup) ≤ 2) :
    (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
  let := replacementMoved_normal h d
  let : IsElementaryAbelian 2 (⁅replacementMoved d,A⁆ : Subgroup d.overgroup) :=
    IsElementaryAbelian.of_le (commutator_le_left (replacementMoved d) A)
  let π := coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)
  let D := subspaceCommutator (coverAction s) ⊤ (A.map s.projection)
  have hDcard : Nat.card D ≤ 2 := by
    have he := Nat.card_congr (NormalElementaryQuotient.movedEquiv
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm) A).toEquiv
    change Nat.card (⁅replacementMoved d,A⁆ : Subgroup d.overgroup) = Nat.card D at he
    rwa [←he]
  have hDdim : Module.finrank (ZMod 2) D ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hDcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hDcard
  have hm : D.map π = subspaceCommutator (naturalRepresentation (Fin 6)) ⊤
      (A.map s.projection) := by
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction s) (MonoidHom.id (Equiv.Perm (Fin 6))) π
      (fun g v => (coverMap_equivariant s g v).symm) (A.map s.projection) ⊤
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr (coverMap_surjective
      (h := h) (e := e) (hz := hz) (hn := hn) (d := d)),Subgroup.map_id] at hh
    exact hh.symm
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 := by
    rw [←NaturalPairing.moved_finrank_eq_fixedCodim,←hm]
    exact (Submodule.finrank_map_le π D).trans hDdim
  have hsmall : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    by_cases he : A.map s.projection = ⊥
    · rw [he,(fixedCodim_eq_zero_iff (coverAction s) ⊥).mpr (fixedSpace_bot (coverAction s))]
      omega
    · obtain ⟨t,_,_,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers
        (A.map s.projection) he hnat
      change Module.finrank (ZMod 2) (subspaceCommutator (coverAction s) ⊤
        (A.map s.projection)) ≤ 1 at hDdim
      rw [he,Representation.CyclicFixedRank.commutator_eq_range,
        ←fixedCodim_zpowers_eq_displacement_rank] at hDdim
      rwa [he]
  rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
    (replacementMoved d) s.projection s.surjective
    (s.projection_kernel.trans (moved_centralizer s).symm)]
  exact Nat.pow_le_pow_right (by decide : 0<2) hsmall

include s in
/-- The same inverse movement bound on the actual full cover at any vertex. -/
theorem moving_small_commutator_fixed_index (hc : DistanceTwo.CentralLayer d)
    {c : Vertex d.radical} (hcol : color d.radical c = false)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ stabilizer d.radical c)
    (hcard : Nat.card (⁅U d.radical c,A⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2) :
    (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2 := by
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc c hcol
  have hmA : (A.comap i).map i = A := map_comap_eq_self (hA.trans_eq hir.symm)
  have hh : Nat.card (⁅replacementMoved d,A.comap i⁆ : Subgroup d.overgroup) ≤ 2 := by
    rw [←card_map_of_injective hi,map_commutator,hiU,hmA]
    exact hcard
  have hf := cover_small_commutator_fixed_index s (A.comap i) hh
  rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
    map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
    inf_relIndex_left]
  exact hf

include s in
/-- The fixed part of the entire endpoint seed has at most two commutators
with its incident edge kernel. No equality with the critical moved line is used. -/
theorem small_edge_fixed_card_at (hc : DistanceTwo.CentralLayer d) (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t)
    (hne : ¬ A ≤ Q d.radical c)
    (hindex : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2) :
    Nat.card (⁅Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)),Q d.radical t⁆ :
      Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
  have hcoords : ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      d.radical.map i = Q d.radical t ∧ (pCore 2 d.overgroup).map i = Q d.radical c ∧
      (replacementMoved d).map i = U d.radical c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_⟩
      · have he := Q_act d.radical g (beta d.radical)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
      · have he := Q_act d.radical g (alpha d.radical)
        rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := U_act d.radical g (alpha d.radical)
        rw [hc.U_eq_moved] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · rw [hg.1] at hcol
      cases hcol
  obtain ⟨i,hi,hiR,hiQ,hiU⟩ := hcoords
  have hAi : A ≤ i.range := hA.trans (hiR ▸ map_le_range i _)
  have hmA : (A.comap i).map i = A := map_comap_eq_self hAi
  have hAr : A.comap i ≤ d.radical := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmA,hiR]
  have hAn : ¬ A.comap i ≤ pCore 2 d.overgroup := by
    intro hh
    apply hne
    have hm := map_mono (f := i) hh
    rwa [hmA,hiQ] at hm
  have hidx : (centralizer (A.comap i : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hcard := cover_small_fixed_edge_card s u hR (A.comap i) hAr hAn hidx
  rw [←card_map_of_injective hi,map_commutator,
    ←map_inf_centralizer_of_injective i hi,hiU,hmA,hiR] at hcard
  let F := U d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcol] at hh
    cases he : color d.radical t <;> simp_all
  have hseed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedA := hseed.trans (centralizer_le hA)
  have hseedN : Z d.radical t ≤ normalizer (U d.radical c : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical hcol hct).trans (Z_le_stabilizer d.radical c)).trans (U_normalized c)
  have heq : Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)) = F ⊔ Z d.radical t := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct,
      sup_comm (U d.radical c),inf_centralizer_sup_of_centralizing _ _ _ hseedN hseedA]
    exact sup_comm _ _
  have hbound : ⁅F ⊔ Z d.radical t,Q d.radical t⁆ ≤ ⁅F,Q d.radical t⁆ := by
    apply commutator_le.mpr
    intro x hx r hr
    have hn : Z d.radical t ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
      (le_inf hseedN (hseedA.trans (centralizer (A : Set (FreeAmalgam d.radical))).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    have hp : x ∈ (F : Set (FreeAmalgam d.radical)) * (Z d.radical t : Set (FreeAmalgam d.radical)) := by
      rw [←coe_mul_of_right_le_normalizer_left F (Z d.radical t) hn]
      exact hx
    obtain ⟨w,hw,z,hz,rfl⟩ := hp
    have hzero : ⁅z,r⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hseed hz r hr).symm
    rw [commutatorElement_mul_left_eq_conj_mul,hzero,mul_one,mul_inv_cancel,one_mul]
    exact commutator_mem_commutator hw hr
  let := finite_Z d.radical c
  have hFU : ⁅F,Q d.radical t⁆ ≤ U d.radical c :=
    (commutator_mono (show F ≤ U d.radical c from inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((show Q d.radical t ≤ stabilizer d.radical c from
          fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (U_normalized c)))
  let : Finite (⁅F,Q d.radical t⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hFU.trans (DistanceEight.U_le_Z d.radical c))) (inclusion_injective _)
  rw [heq]
  exact (card_le_of_le hbound).trans hcard

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

include s in
private theorem edge_preserves_seed_fixer (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t) :
    Q d.radical t ≤ normalizer ((Z d.radical c ⊓ centralizer
      (A : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let := pointCore_elementary
  let : IsElementaryAbelian 2 (pointCore.map (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
  let helem : IsElementaryAbelian 2 (d.radical.map s.projection) := IsElementaryAbelian.of_le hR
  have hbase : ⁅Q d.radical (beta d.radical),Q d.radical (beta d.radical)⁆ ≤
      Q d.radical (alpha d.radical) := by
    rw [Q_beta,Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d),←map_commutator]
    apply map_mono
    rw [←s.projection_kernel,←Subgroup.map_eq_bot_iff,map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr helem.toIsMulCommutative)
  have hderived : ⁅Q d.radical t,Q d.radical t⁆ ≤ Q d.radical c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hbase
      rw [map_commutator,←Q_act,←Q_act] at hh
      simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using hh
    · rw [hg.1] at hcol
      cases hcol
  have htG : Q d.radical t ≤ stabilizer d.radical c := fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  exact abelian_action_preserves_fixed _ _ A (htG.trans (Z_normalized d.radical c)) hA
    (hderived.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical c hcol))))

include s in
/-- In the small-original-image branch, a generating edge transports a
slice of index greater than two to a backward critical noncontainment.
The displacement line may differ from the original critical line. -/
theorem small_image_backward_not_le (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    ¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let F := Z d.radical c ⊓ centralizer (K : Set (FreeAmalgam d.radical))
  let Y := F ⊔ Z d.radical (alpha d.radical)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hZV : Z d.radical c ≤ V d.radical (alpha d.radical) :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)
  have hFt := edge_preserves_seed_fixer s u hR hcol hct K
    (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat))
  have hmove : ⁅F,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    small_critical_predecessor_commutator s hc hb p hsmall F
      (inf_le_left.trans hbad) inf_le_right
  have hYmove : ⁅Y,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
      F (Z d.radical (alpha d.radical)) (Z d.radical a') (Z d.radical (alpha d.radical))
      (Z_normalized d.radical _) ((inf_le_left.trans hZV).trans
        ((replacementGeometry h d).V_local _ rfl hb)) (Z_le_stabilizer d.radical _) hmove
      (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans (DistanceEight.U_le_Z d.radical _))
  have hYn : stabilizer d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    apply sup_le
    · exact (le_inf hFt ((show Q d.radical t ≤ stabilizer d.radical (alpha d.radical) from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Z_normalized d.radical _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hYmove.trans le_sup_right)
  have hFB : F ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    le_sup_left.trans (normalized_radius_le_slice_of_critical_commutator s hc hb p Y
      (sup_le (inf_le_left.trans hZV) (Z_le_VBall d.radical _ 2)) hYn hYmove)
  let last := p.walk.getVert (p.walk.length-1)
  have helast : Adjacent d.radical a' last := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1 = p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hlast : color d.radical last = true := by
    have hh := adjacent_color_ne d.radical helast
    rw [p.end_color] at hh
    cases he : color d.radical last <;> simp_all
  have hpred : Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical last := by
    apply Q_le_adjacent_h d.radical hlast
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hZlast : Z d.radical (alpha d.radical) ≤ Q d.radical last := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ rfl)
    rw [(replacementGeometry h d).distance_constant _ rfl,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-1 < replacementDistance h d
    omega
  have hKfixed : K = Z d.radical a' ⊓ centralizer
      (Z d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical _ rfl)))
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←C_eq_Q s hc _ rfl]
      exact ⟨critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
        (replacementDistance_pos h d) p.critical hx.1,hx.2⟩
  let := finite_Z d.radical a'
  let : Finite (U d.radical a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a')) (inclusion_injective _)
  have hfixindex : (centralizer (Z d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a') ≤ 2 := by
    have hh : Q d.radical (alpha d.radical) ≤ centralizer
        (Z d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical _ rfl))
    exact ((relIndex_le_of_le_left hh index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a') index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have hcard := small_edge_fixed_card_at s hc u hR p.end_color helast
    (Z d.radical (alpha d.radical)) hZlast p.critical.2 hfixindex
  rw [←hKfixed] at hcard
  let := finite_stabilizer d.radical last
  let : Finite (Q d.radical last) := Finite.of_injective
    (inclusion (show Q d.radical last ≤ stabilizer d.radical last from fun _ hx => hx.1)) (inclusion_injective _)
  have hKlast : K ≤ Q d.radical last :=
    inf_le_left.trans (show Z d.radical a' ≤ Q d.radical last from
      (show Z d.radical a' ≤ Q d.radical a' from by
        apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ p.end_color)
        rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ p.end_color]
        exact replacementDistance_pos h d).trans (Q_le_adjacent_h d.radical hlast helast))
  let : Finite (⁅K,Q d.radical last⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion ((Subgroup.commutator_le_sup K (Q d.radical last)).trans (sup_le hKlast le_rfl))) (inclusion_injective _)
  have hline : Nat.card (⁅U d.radical c,K⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
    rw [commutator_comm]
    exact (card_le_of_le (commutator_mono le_rfl
      (((DistanceEight.U_le_Z d.radical c).trans hbad).trans hpred))).trans hcard
  have hKc : K ≤ stabilizer d.radical c :=
    (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hidx := moving_small_commutator_fixed_index s hc hcol K hKc hline
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hh := relIndex_le_of_le_left
    ((inf_le_inf_right _ (DistanceEight.U_le_Z d.radical c)).trans hFB)
    (index_ne_zero_of_finite (H := (U d.radical c ⊓ centralizer
      (K : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical c)))
  rw [inf_relIndex_left] at hh
  exact (Nat.not_le_of_gt hindex) (hh.trans hidx)

include s in
/-- In the full point-core branch the actual critical actor selects a
generating neighbor. Only the quotient marking is used, so both central
cover orders remain possible. -/
theorem full_point_generating_neighbor
    (hc : DistanceTwo.CentralLayer d) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) := by
  by_cases hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))
  · exact large_image_full_point_generating_neighbor s hc u hfull p hlarge
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p (Nat.lt_of_not_ge hlarge)
  obtain ⟨k,hk⟩ := PointCoreEvenGeneration.exists_even_conjugate_pointCore_generates_swap u a hswap
  have hkL : k.val ∈ (replacementComponent d).map s.projection := by
    rw [s.component_image]
    exact k.property
  obtain ⟨g,hg,hgk⟩ := hkL
  let A := (Z d.radical a').comap (embedM d.radical)
  have hm : (d.radical.map (MulAut.conj g).toMonoidHom).map s.projection =
      (d.radical.map s.projection).map (MulAut.conj k.val).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change s.projection (g*x*g⁻¹) = k.val*s.projection x*k.val⁻¹
    rw [map_mul,map_mul,map_inv,hgk]
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hker : s.projection.ker ≤ d.radical.map (MulAut.conj g).toMonoidHom := by
    rw [s.projection_kernel,←hQ]
    exact map_mono (replacement_core_le_radical h d)
  have hgen : d.radical.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
    apply map_injective_of_ker_le s.projection (hker.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hm,hfull,map_top_of_surjective s.projection s.surjective]
    apply top_unique
    rw [←hk]
    exact sup_le_sup_left (zpowers_le.mpr ha) _
  let f := (embedM d.radical g)⁻¹
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act d.radical f (alpha d.radical) = alpha d.radical := hf
  refine ⟨act d.radical f (beta d.radical),?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff d.radical f (alpha d.radical) (beta d.radical)).mpr
      (base_adjacent d.radical)
  · have hmapA : A.map (embedM d.radical) = Z d.radical a' :=
      map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
        (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
          (stabilizer_m_base d.radical))
    have hh := congrArg (Subgroup.map (embedM d.radical)) hgen
    rw [Subgroup.map_sup,hmapA,←MonoidHom.range_eq_map] at hh
    rw [Q_act,Q_beta]
    change _ = stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    have hmapR : (d.radical.map (embedM d.radical)).map (MulAut.conj f⁻¹).toMonoidHom =
        (d.radical.map (MulAut.conj g).toMonoidHom).map (embedM d.radical) := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f⁻¹*embedM d.radical x*(f⁻¹)⁻¹=embedM d.radical (g*x*g⁻¹)
      simp only [f,inv_inv,map_mul,map_inv]
    rw [hmapR]
    exact hh


include s in
/-- Both original-image branches of the backward step on one prescribed
slice. The same conjugator retains every overlapping vertex of the walk. -/
theorem backward_shift_of_two_lt_slice
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' delta t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta))
    (hat : Adjacent d.radical (alpha d.radical) t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical)) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      act d.radical g (p.walk.getVert 1) = t ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  let c := act d.radical g delta
  have hct : Adjacent d.radical c t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g delta (p.walk.getVert 1)).mpr hdelta
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have hindexc : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) := by
    change 2 < (B d.radical (alpha d.radical) _).relIndex (U d.radical (act d.radical g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hindex
  have hbad : ¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    by_cases hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))
    · apply large_image_backward_not_le s hc hb u hR p hlarge hat hct hgen
      intro he
      have hi := relIndex_eq_one.mpr he
      omega
    · exact small_image_backward_not_le s hc hb u hR p (Nat.lt_of_not_ge hlarge) hat hct hgen hindexc
  let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  exact ⟨g,hg,hgt,q,hqt,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi,hindexc⟩

/-- On the original replacement, a full point-core image supplies the
backward critical shift for every prescribed slice of index greater than two.
The generating edge is constructed in both critical-image branches. -/
theorem full_point_backward_shift_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (u : S) (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
          (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical (act d.radical g delta)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t,hat,hgen⟩ := full_point_generating_neighbor s hc u hfull' p
  exact ⟨t,hat,hgen,backward_shift_of_two_lt_slice s hc hb u hfull'.le p hdelta hindex hat hgen⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
