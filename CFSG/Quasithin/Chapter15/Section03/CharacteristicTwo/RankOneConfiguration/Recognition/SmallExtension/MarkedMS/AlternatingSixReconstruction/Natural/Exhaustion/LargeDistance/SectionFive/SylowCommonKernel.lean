module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair
public import Theory.Representation.BinaryPermutationSixCover.SeedPreimage
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowMovingLine
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SmallBackward

/-!
# Predecessor control on the common full critical kernel

Above distance four, suppose the first-edge relative normalizer moves a
small critical line. Its endpoint-seed orbit has a common full fixed kernel
of index four. The commutator of this kernel with the whole first-edge core
has order at most two, lies in that edge seed, and is fixed by the entire
relative normalizer. Reversing the literal critical walk gives the same
bound for the actual predecessor core at the opposite endpoint. A final
application identifies the actor with the restricted original Sylow under
the given replacement embedding.

For the local calculation, conjugate the two-group image into the canonical
six-letter Sylow. A moved transposition and its conjugate are the two swaps
on its four-point orbit. Their common fixed vectors are constant on all
three pairs; the Sylow moves that subspace into a line. Small checked tables
establish this on the augmentation cover. Every fixed natural vector has a
fixed augmentation lift, so the calculation also applies to the natural
cover. Equivariant transport retains both possible moving-layer orders.
The full graph seed's edge-central attachment contributes no commutators
with the edge core. Normalization then makes its order-at-most-two
commutator fixed by the whole relative normalizer.

This supplies a common-kernel estimate for the non-elementary Sylow shift.
It does not bound the displacement of either entire critical hyperplane.
The remaining backward selection, non-elementary terminal exclusion and
distance-four estimates still belong to the large-distance assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the full-kernel and backward-selection arguments in (5.5)--(5.8),
printed pp.915--920, and the small-line argument in (5.11), pp.923--924.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open scoped commutatorElement Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCommonKernel
local notation "ρ" => coreRepresentation (Fin 6)
private def lineVector : C := pairWord 0 1 + pairWord 2 3

private theorem moving_swap_cert : ∀ i j : Fin 16,
    (sylowWords i).support.card = 2 →
    sylowWords j * sylowWords i * (sylowWords j)⁻¹ ≠ sylowWords i →
    (sylowWords i = swap01 ∧ sylowWords j * sylowWords i * (sylowWords j)⁻¹ = swap23) ∨
    (sylowWords i = swap23 ∧ sylowWords j * sylowWords i * (sylowWords j)⁻¹ = swap01) := by
  decide +kernel

private theorem displacement_cert :
    ∀ i : Fin 16, ∀ v : Full (Fin 6), (∑ j, v j) = 0 → v 0 = v 1 → v 2 = v 3 →
      ∃ c : ZMod 2, representation (Fin 6) (sylowWords i) v-v = c • lineVector.val := by
  decide +kernel

private theorem canonical_displacement (g : S) (hg : g ∈ sylowCarrier)
    (v : C) (h01 : ρ swap01 v = v) (h23 : ρ swap23 v = v) :
    ρ g v-v ∈ Submodule.span (ZMod 2) {lineVector} := by
  have h1 : v.val 0 = v.val 1 := congrArg (fun w : C => w.val 1) h01
  have h3 : v.val 2 = v.val 3 := congrArg (fun w : C => w.val 3) h23
  obtain ⟨i,rfl⟩ := (mem_sylowCarrier_iff g).mp hg
  obtain ⟨c,hc⟩ := displacement_cert i v.val v.property h1 h3
  exact Submodule.mem_span_singleton.mpr ⟨c,Subtype.ext hc.symm⟩

private theorem core_common_line (A B : Subgroup S) (hB : IsPGroup 2 B)
    (hAB : A ≤ B) (hn : B ≤ normalizer (A : Set S))
    (t : S) (ht : t ∈ A) (hs : t.IsSwap)
    (k : S) (hk : k ∈ B) (hm : k*t*k⁻¹ ≠ t) :
    ∃ z : C, subspaceCommutator ρ (fixedSpace ρ A) B ≤
      Submodule.span (ZMod 2) {z} := by
  obtain ⟨P,hBP⟩ := hB.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S P sylow
  let f := (MulAut.conj g).toMonoidHom
  have hBs : B.map f ≤ sylowCarrier := by
    rintro _ ⟨b,hb,rfl⟩
    change (MulAut.conj g) b ∈ (sylow : Subgroup S)
    rw [←hg]
    exact mem_map_of_mem f (hBP hb)
  have hts : f t ∈ sylowCarrier := hBs (mem_map_of_mem f (hAB ht))
  have hks : f k ∈ sylowCarrier := hBs (mem_map_of_mem f hk)
  obtain ⟨i,hi⟩ := (mem_sylowCarrier_iff (f t)).mp hts
  obtain ⟨j,hj⟩ := (mem_sylowCarrier_iff (f k)).mp hks
  have hsi : (sylowWords i).support.card = 2 := by
    rw [hi]
    change (g*t*g⁻¹).support.card = 2
    rw [Equiv.Perm.card_support_conj]
    exact Equiv.Perm.card_support_eq_two.mpr hs
  have hneq : sylowWords j*sylowWords i*(sylowWords j)⁻¹ ≠ sylowWords i := by
    rw [hi,hj,←map_inv,←map_mul,←map_mul]
    exact fun hh => hm ((MulAut.conj g).injective hh)
  have hp := moving_swap_cert i j hsi hneq
  rw [hi,hj] at hp
  refine ⟨ρ g⁻¹ lineVector,?_⟩
  apply Submodule.span_le.mpr
  rintro _ ⟨b,hb,v,hv,rfl⟩
  let w := ρ g v
  have hw (x : S) (hx : x ∈ A) : ρ (f x) w = w := by
    change ρ (g*x*g⁻¹) (ρ g v) = ρ g v
    simp only [map_mul,Module.End.mul_apply,(ρ).inv_self_apply]
    exact congrArg (ρ g) (show ρ x v = v from hv ⟨x,hx⟩)
  have htfix := hw t ht
  have hconjfix := hw (k*t*k⁻¹) ((mem_normalizer_iff.mp (hn hk) t).mp ht)
  rw [show f (k*t*k⁻¹) = f k*f t*(f k)⁻¹ by simp only [map_mul,map_inv]] at hconjfix
  have hpfix : ρ swap01 w = w ∧ ρ swap23 w = w := by
    rcases hp with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨h1 ▸ htfix,h2 ▸ hconjfix⟩
    · exact ⟨h2 ▸ hconjfix,h1 ▸ htfix⟩
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp
    (canonical_displacement (f b) (hBs (mem_map_of_mem f hb)) w hpfix.1 hpfix.2)
  refine Submodule.mem_span_singleton.mpr ⟨c,?_⟩
  have hh := congrArg (ρ g⁻¹) hc
  change ρ g⁻¹ (c • lineVector) = ρ g⁻¹ (ρ (g*b*g⁻¹) (ρ g v)-ρ g v) at hh
  simpa only [map_smul,map_sub,map_mul,Module.End.mul_apply,(ρ).inv_self_apply] using hh

private theorem natural_common_bound (A B : Subgroup S) (hB : IsPGroup 2 B)
    (hAB : A ≤ B) (hn : B ≤ normalizer (A : Set S))
    (t : S) (ht : t ∈ A) (hs : t.IsSwap)
    (k : S) (hk : k ∈ B) (hm : k*t*k⁻¹ ≠ t) :
    Module.finrank (ZMod 2) (subspaceCommutator (naturalRepresentation (Fin 6))
      (fixedSpace (naturalRepresentation (Fin 6)) A) B) ≤ 1 := by
  obtain ⟨z,hz⟩ := core_common_line A B hB hAB hn t ht hs k hk hm
  have hle : subspaceCommutator (naturalRepresentation (Fin 6))
      (fixedSpace (naturalRepresentation (Fin 6)) A) B ≤
      (subspaceCommutator ρ (fixedSpace ρ A) B).map (coreToNatural (Fin 6)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,v,hv,rfl⟩
    obtain ⟨w,rfl⟩ := coreToNatural_surjective v
    refine ⟨ρ b w-w,Submodule.subset_span ⟨b,hb,w,?_,rfl⟩,?_⟩
    · intro a
      exact SixCover.six_core_fixed_of_natural_fixed a w (hv a)
    · rw [map_sub,coreToNatural_equivariant]
  exact (Submodule.finrank_mono hle).trans
    ((Submodule.finrank_map_le _ _).trans ((Submodule.finrank_mono hz).trans
      (by simpa using finrank_span_le_card (R := ZMod 2) ({z} : Set C))))

private theorem model_common_fixed_movement
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (A B : Subgroup S) (hB : IsPGroup 2 B)
    (hAB : A ≤ B) (hn : B ≤ normalizer (A : Set S))
    (t : S) (ht : t ∈ A) (hs : t.IsSwap)
    (k : S) (hk : k ∈ B) (hmove : k*t*k⁻¹ ≠ t) :
    Module.finrank (ZMod 2) (subspaceCommutator σ (fixedSpace σ A) B) ≤ 1 := by
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
  · rw [SmallBackward.fixed_movement_finrank_transport σ (naturalRepresentation (Fin 6)) E hE]
    exact natural_common_bound A B hB hAB hn t ht hs k hk hmove
  · rw [SmallBackward.fixed_movement_finrank_transport σ ρ E hE]
    obtain ⟨z,hz⟩ := core_common_line A B hB hAB hn t ht hs k hk hmove
    exact (Submodule.finrank_mono hz).trans
      (by simpa using finrank_span_le_card (R := ZMod 2) ({z} : Set C))

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
open Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

private theorem cover_common_fixed_card (s : FullSymmetricAction h e hz hn d)
    (A B : Subgroup d.overgroup) (hp : IsPGroup 2 B)
    (hAB : A ≤ B) (hnorm : B ≤ normalizer (A : Set d.overgroup))
    (t : S) (ht : t ∈ A.map s.projection) (hs : t.IsSwap)
    (k : S) (hk : k ∈ B.map s.projection) (hmove : k*t*k⁻¹ ≠ t) :
    Nat.card (⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),B⁆ :
      Subgroup d.overgroup) ≤ 2 := by
  let := replacementMoved_normal h d
  let U := replacementMoved d
  let D := subspaceCommutator (coverAction s) (fixedSpace (coverAction s) (A.map s.projection))
    (B.map s.projection)
  let J := D.toAddSubgroup.toSubgroup'.map U.subtype
  have hd : Module.finrank (ZMod 2) D ≤ 1 :=
    model_common_fixed_movement (coverAction s) (cover_model s) _ _ (hp.map s.projection)
      (map_mono hAB) ((map_mono hnorm).trans (le_normalizer_map _)) t ht hs k hk hmove
  have hle : ⁅U ⊓ centralizer (A : Set d.overgroup),B⁆ ≤ J := by
    apply commutator_le.mpr
    intro v hv b hb
    have hcu : ⁅v,b⁆ ∈ U := (commutator_le_left U B) (commutator_mem_commutator hv.1 hb)
    refine ⟨⟨⁅v,b⁆,hcu⟩,?_,rfl⟩
    change Additive.ofMul (⟨⁅v,b⁆,hcu⟩ : U) ∈ D
    rw [NormalElementaryQuotient.vector_commutator U s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm) ⟨v,hv.1⟩ b]
    apply D.neg_mem_iff.mp
    rw [neg_sub]
    exact Submodule.subset_span ⟨s.projection b,mem_map_of_mem _ hb,Additive.ofMul ⟨v,hv.1⟩,
      (NormalElementaryQuotient.mem_fixedSpace_image U s.projection s.surjective
        (s.projection_kernel.trans (moved_centralizer s).symm) A _).mpr hv.2,rfl⟩
  apply (card_le_of_le hle).trans
  rw [card_map_of_injective U.subtype_injective]
  change Nat.card D ≤ 2
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hd

include e hz hn in
private theorem moving_endpoint_commutator_not_le_core
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ (normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a) ≤ centralizer
        ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ¬ ⁅normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a,Z d.radical a'⁆ ≤ Q d.radical a := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  intro hcore
  have hAG := critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ p.start_color
    (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
        exact replacementDistance_pos h d) p.critical
  have hcomm := hcore.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q d.radical a p.start_color)))
  have hnorm := SylowNormalizer.fixed_mod_central_normalizes
    (Z d.radical a') (Z d.radical a)
    (normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a)
    (hAG.trans (Z_normalized d.radical a)) (inf_le_right.trans (Z_normalized d.radical a)) hcomm
  rw [commutator_comm (Z d.radical a')] at hnorm
  exact hmove (hnorm.trans (normalizer_le_centralizer_of_card_two _
    (small_critical_commutator_card s hc p hsmall)))

include e hz hn in
/-- The common full critical kernel has at most a line of commutators with
its actual first-edge core, in the moving small-line branch. -/
theorem moving_common_kernel_edge_card_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ (normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a) ≤ centralizer
        ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a
    let E := componentOrbit (Z d.radical a') T
    let F := Z d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical))
    Nat.card (⁅F,Q d.radical (p.walk.getVert 1)⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let := replacementMoved_normal h d
  let t := p.walk.getVert 1
  let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  let E := componentOrbit (Z d.radical a') T
  let F := Z d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical))
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical t <;> simp_all
  have hi := SylowKernelPair.small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  have hEG : E ≤ stabilizer d.radical a := hi.1.trans
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  have hET : E ≤ T := le_inf (hi.1.trans (Q d.radical t).le_normalizer) hEG
  have hcoords : ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical a ∧ d.radical.map i = Q d.radical t ∧
      (pCore 2 d.overgroup).map i = Q d.radical a ∧
      (replacementMoved d).map i = U d.radical a := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
    · rcases hg with ⟨hga,hgt⟩
      rw [hga,hgt]
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_,?_⟩
      · rw [MonoidHom.range_comp]
        have he : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
          (stabilizer_m_base d.radical).symm
        rw [he]
        simpa only [alpha,act_mVertex,one_mul] using (stabilizer_act d.radical g (alpha d.radical)).symm
      · have he := Q_act d.radical g (beta d.radical)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
      · have he := Q_act d.radical g (alpha d.radical)
        rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := U_act d.radical g (alpha d.radical)
        rw [hc.U_eq_moved] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · have hcol := p.start_color
      rw [hg.1] at hcol
      cases hcol
  obtain ⟨i,hinj,hir,hiR,hiQ,hiU⟩ := hcoords
  let A₀ := (Z d.radical a').comap i
  let E₀ := E.comap i
  let T₀ := T.comap i
  have hAG : Z d.radical a' ≤ stabilizer d.radical a := (le_componentOrbit _ _).trans hEG
  have hmA : A₀.map i = Z d.radical a' := map_comap_eq_self (hAG.trans_eq hir.symm)
  have hmE : E₀.map i = E := map_comap_eq_self (hEG.trans_eq hir.symm)
  have hmT : T₀.map i = T := map_comap_eq_self (inf_le_right.trans_eq hir.symm)
  have hp : IsPGroup 2 T₀ := (SylowMovingLine.first_edge_normalizer_isPGroup
    (e := e) (hz := hz) (hn := hn) hb p).comap_of_injective i hinj
  let := finite_Z d.radical a
  have hidx : (centralizer (A₀ : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    have hC : Q d.radical a' ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color))
    let : Finite (U d.radical a) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
    have hh := ((relIndex_le_of_le_left hC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a) index_ne_zero_of_finite)).trans_eq
      (small_critical_indices s hc p hsmall).1
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,map_inf_centralizer_of_injective i hinj,
      relIndex_map_map_of_injective _ _ hinj,inf_relIndex_left] at hh
    exact hh
  have hneA : A₀.map s.projection ≠ ⊥ := by
    intro he
    have ha := (Subgroup.map_eq_bot_iff A₀).mp he
    rw [s.projection_kernel] at ha
    have hh := map_mono (f := i) ha
    rw [hmA,hiQ] at hh
    exact (critical_reverse_pair s hc p).2 hh
  have hsmallA : fixedCodim (coverAction s) (A₀.map s.projection) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hidx
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hidx
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A₀.map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) (A₀.map s.projection)).trans hsmallA
  obtain ⟨x,hx,hxs,hAx⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers _ hneA hnat
  have hnon : ¬ T₀.map s.projection ≤ centralizer (A₀.map s.projection : Set S) := by
    intro hcent
    have hcomm : ⁅T₀,A₀⁆ ≤ pCore 2 d.overgroup := by
      rw [←s.projection_kernel,←Subgroup.map_eq_bot_iff,map_commutator]
      exact commutator_eq_bot_iff_le_centralizer.mpr hcent
    have hh := map_mono (f := i) hcomm
    rw [map_commutator,hmA,hmT,hiQ] at hh
    exact moving_endpoint_commutator_not_le_core (e := e) (hz := hz) (hn := hn)
      hb p hsmall hmove hh
  have hex : ∃ k ∈ T₀.map s.projection, k*x*k⁻¹ ≠ x := by
    by_contra! hall
    apply hnon
    intro k hk y hy
    rw [hAx] at hy
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hy
    have hkx : Commute x k := (mul_inv_eq_iff_eq_mul.mp (hall k hk)).symm
    exact (hkx.zpow_left n).eq
  obtain ⟨k,hk,hkx⟩ := hex
  have hnE : T₀ ≤ normalizer (E₀ : Set d.overgroup) :=
    (comap_mono hi.2.1).trans (le_normalizer_comap i)
  have hcard := cover_common_fixed_card s E₀ T₀ hp (comap_mono hET) hnE x
    (map_mono (comap_mono (le_componentOrbit _ _)) hx) hxs k hk hkx
  rw [←card_map_of_injective hinj,map_commutator,
    ←map_inf_centralizer_of_injective i hinj,hiU,hmE,hmT] at hcard
  let F₀ := U d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical))
  have hseed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro z hz
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  have hseedE := hseed.trans (centralizer_le hi.1)
  have hseedN : Z d.radical t ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical p.start_color hat).trans (Z_le_stabilizer d.radical a)).trans (U_normalized a)
  have heq : F = F₀ ⊔ Z d.radical t := by
    change Z d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical)) = _
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d p.start_color hat,
      sup_comm (U d.radical a),inf_centralizer_sup_of_centralizing _ _ _ hseedN hseedE]
    exact sup_comm _ _
  have hedgeT : Q d.radical t ≤ T := le_inf (Q d.radical t).le_normalizer
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  have hbound : ⁅F,Q d.radical t⁆ ≤ ⁅F₀,T⁆ := by
    rw [heq]
    apply commutator_le.mpr
    intro z hz r hr
    have hnF : Z d.radical t ≤ normalizer (F₀ : Set (FreeAmalgam d.radical)) :=
      (le_inf hseedN (hseedE.trans (centralizer (E : Set (FreeAmalgam d.radical))).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    have hpz : z ∈ (F₀ : Set (FreeAmalgam d.radical)) * (Z d.radical t : Set (FreeAmalgam d.radical)) := by
      rw [←coe_mul_of_right_le_normalizer_left F₀ (Z d.radical t) hnF]
      exact hz
    obtain ⟨w,hw,z,hzedge,rfl⟩ := hpz
    have hzero : ⁅z,r⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hseed hzedge r hr).symm
    rw [commutatorElement_mul_left_eq_conj_mul,hzero,mul_one,mul_inv_cancel,one_mul]
    exact commutator_mem_commutator hw (hedgeT hr)
  have hFU : ⁅F₀,T⁆ ≤ U d.radical a :=
    (commutator_mono (show F₀ ≤ U d.radical a from inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans (U_normalized a)))
  let : Finite (⁅F₀,T⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hFU.trans (DistanceEight.U_le_Z d.radical a))) (inclusion_injective _)
  exact (card_le_of_le hbound).trans hcard

include e hz hn in
/-- The common full kernel has index four. Its commutator with the whole
first-edge core is in that edge's seed and is fixed by the whole relative
normalizer. The bound concerns the common kernel, not either hyperplane. -/
theorem moving_common_kernel_edge_control_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ (normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a) ≤ centralizer
        ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a
    let E := componentOrbit (Z d.radical a') T
    let F := Z d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical))
    let H := ⁅F,Q d.radical (p.walk.getVert 1)⁆
    F = ⨅ t : T, (Z d.radical a ⊓ Q d.radical a').map
      (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom ∧
      F.relIndex (Z d.radical a) = 4 ∧
      Nat.card H ≤ 2 ∧ H ≤ Z d.radical (p.walk.getVert 1) ∧
      H ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
  let t := p.walk.getVert 1
  let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  let E := componentOrbit (Z d.radical a') T
  let F := Z d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical))
  let H := ⁅F,Q d.radical t⁆
  have hi := SylowKernelPair.small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  have hd := SylowKernelPair.small_seed_orbit_dichotomy_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  have hindex : F.relIndex (Z d.radical a) = 4 := by
    rcases hd.2.2 with hh | hh
    · have hfix := hh.2.2.2
      rw [hh.2.2.1] at hfix
      exact (hmove (le_centralizer_iff.mp hfix)).elim
    · exact hh.1
  have hcard := moving_common_kernel_edge_card_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove
  change Nat.card H ≤ 2 at hcard
  have hTF : T ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    (le_inf (inf_le_right.trans (Z_normalized d.radical a))
      (hi.2.1.trans (normalizer_le_normalizer_centralizer E))).trans inf_normalizer_le_normalizer_inf
  have hTQ : T ≤ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) := inf_le_left
  have hTH : T ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅F,Q d.radical t⁆).map (MulAut.conj g).toMonoidHom = _
    rw [map_commutator]
    exact congrArg₂ (fun A B : Subgroup (FreeAmalgam d.radical) => ⁅A,B⁆)
      (mem_normalizer_iff_map_conj_eq.mp (hTF hg))
      (mem_normalizer_iff_map_conj_eq.mp (hTQ hg))
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical t <;> simp_all
  have hQT : Q d.radical t ≤ T := le_inf (Q d.radical t).le_normalizer
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  have hHF : H ≤ F := le_normalizer_iff_commutator_le_left.mp (hQT.trans hTF)
  let := finite_Z d.radical a
  let : Finite H := Finite.of_injective (inclusion (hHF.trans inf_le_left)) (inclusion_injective _)
  have hfixed : H ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
    by_cases he : H = ⊥
    · rw [he]; exact bot_le
    · have hh := (one_lt_card_iff_ne_bot H).mpr he
      exact le_centralizer_iff.mp (hTH.trans (normalizer_le_centralizer_of_card_two H (by omega)))
  have hZaQ : Z d.radical a ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical _ p.start_color)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ p.start_color]
    exact replacementDistance_pos h d
  have hHQ : H ≤ Q d.radical t := (hHF.trans inf_le_left).trans
    (hZaQ.trans (Q_le_adjacent_h d.radical ht hat))
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  refine ⟨hi.2.2.2,hindex,hcard,?_,hfixed⟩
  intro x hx
  change x ∈ Z d.radical t
  rw [Z,if_neg (by simp [ht])]
  exact mem_omegaCenter_iff.mpr ⟨hHQ hx,
    elemPow_eq_one_of_isElementaryAbelian x ((hHF.trans inf_le_left) hx),
    (hfixed.trans (centralizer_le hQT)) hx⟩

include e hz hn in
/-- At the reverse critical endpoint the actual predecessor core moves the
common full kernel into the last edge seed, with order at most two. The
last-edge relative normalizer fixes this displacement pointwise. -/
theorem moving_common_predecessor_control_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ (normalizer (Q d.radical (p.walk.getVert (p.walk.length-1)) :
        Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a') ≤ centralizer
        ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := normalizer (Q d.radical (p.walk.getVert (p.walk.length-1)) :
      Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a'
    let F := Z d.radical a' ⊓ centralizer (componentOrbit (Z d.radical a) T : Set (FreeAmalgam d.radical))
    let H := ⁅F,Q d.radical (p.walk.getVert (p.walk.length-2))⁆
    F = ⨅ t : T, (Z d.radical a' ⊓ Q d.radical a).map
      (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom ∧
      F.relIndex (Z d.radical a') = 4 ∧ Nat.card H ≤ 2 ∧
      H ≤ Z d.radical (p.walk.getVert (p.walk.length-1)) ∧
      H ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let r : CriticalPath d.radical (replacementGeometry h d) a' a := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc p }
  have hr : r.walk.getVert 1 = p.walk.getVert (p.walk.length-1) :=
    p.walk.getVert_reverse 1
  have hrs : (Q d.radical a).relIndex (Z d.radical a') < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  have hrm : ¬ (normalizer (Q d.radical (r.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a') ≤ centralizer
        ((⁅Z d.radical a',Z d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [hr,commutator_comm (Z d.radical a')]
  have he := moving_common_kernel_edge_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r hrs hrm
  dsimp only at he ⊢
  rw [hr] at he
  have hl : 2 < p.walk.length := p.length_eq_b ▸ (by omega : 2 < replacementDistance h d)
  have hct : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have het : Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical (p.walk.getVert (p.walk.length-1)) = true := by
    have hh := adjacent_color_ne d.radical het
    rw [p.end_color] at hh
    cases he : color d.radical (p.walk.getVert (p.walk.length-1)) <;> simp_all
  have hle := commutator_mono (show Z d.radical a' ⊓
    centralizer (componentOrbit (Z d.radical a)
      (normalizer (Q d.radical (p.walk.getVert (p.walk.length-1)) : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical a') : Set (FreeAmalgam d.radical)) ≤ _ from le_rfl)
    (Q_le_adjacent_h d.radical ht hct)
  let : Finite (Z d.radical (p.walk.getVert (p.walk.length-1))) := finite_Z _ _
  let : Finite (⁅Z d.radical a' ⊓
    centralizer (componentOrbit (Z d.radical a)
      (normalizer (Q d.radical (p.walk.getVert (p.walk.length-1)) : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical a') : Set (FreeAmalgam d.radical)),
      Q d.radical (p.walk.getVert (p.walk.length-1))⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion he.2.2.2.1) (inclusion_injective _)
  exact ⟨he.1,he.2.1,(card_le_of_le hle).trans he.2.2.1,
    hle.trans he.2.2.2.1,hle.trans he.2.2.2.2⟩

include e hz hn in
/-- Literal application to the restricted original Sylow and the actual
replacement edge. Both full kernels and the full edge seed are retained. -/
theorem original_sylow_common_kernel_control_knownSimple
    (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hmove : ¬ ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) ≤
      centralizer ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let F := Z d.radical (alpha d.radical) ⊓ centralizer
      (componentOrbit (Z d.radical a') T : Set (FreeAmalgam d.radical))
    let H := ⁅F,Q d.radical (beta d.radical)⁆
    F = ⨅ t : T, (Z d.radical (alpha d.radical) ⊓ Q d.radical a').map
      (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom ∧
      F.relIndex (Z d.radical (alpha d.radical)) = 4 ∧
      Nat.card H ≤ 2 ∧ H ≤ Z d.radical (beta d.radical) ∧
      H ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
  have hT := SylowSmallNormalizer.four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hm : ¬ (normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical)) ≤ centralizer
        ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [hfirst,hT]
  have hh := moving_common_kernel_edge_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hm
  dsimp only at hh ⊢
  rwa [hfirst,hT] at hh

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCommonKernel
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
