module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardFixedCore

/-!
# Rigidity of the full backward-kernel displacement

For a small nontrivial actor in the point core, the edge displacement of its
fixed hyperplane maps into its moved line in the natural quotient. If another
actor's whole-cover displacement lies there, the natural symplectic pairing
forces its image into the original cyclic transposition group. Lifting through
the literal quotient shows that it fixes the whole critical kernel. This
argument retains the constant line of the augmentation cover.

At the last edge of a critical path the full fixed seed and its moving part
have the same edge commutator: the extra edge seed centralizes the edge kernel.
The full reverse kernel is the moving reverse kernel times that edge seed.
Their predecessor-slice placement and every predecessor-core commutator agree.
Consequently, an endpoint actor whose full displacement is contained in the
reverse kernel's predecessor-core commutator must fix that full reverse kernel.

A reverse kernel in the predecessor Baumann slice is fixed modulo the
predecessor seed by its residual. Its core commutator has order at most two,
so it is fixed pointwise. The same residual element therefore preserves its
commutator with each transported subgroup of the predecessor core. This
excludes the equality between a nonzero backward-kernel commutator and the
full endpoint displacement used at the end of MS93 (5.8).

The original replacement factorization constructs a residual element moving
the last edge to the preceding edge. The final application uses the actual
moving reverse kernel, backward vertex and inverse transported seed, retaining that same element
on every vertex of the critical walk.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), printed pp.866--867,
and the residual-transport contradiction in (5.8), printed p.920.
The point-core containment, predecessor slice placement and nonzero backward
commutator remain explicit source premises. Their selection and upper slice
bounds, exact-four radius exclusion, intermediate R4/R6 noncentrality, both
terminal contradictions, largeDistance_knownSimple and replacementDistance = 2
remain with qt-e-ms-small-a6-exhaustion-large-distance. Whole-core reconstruction
remains with qt-e-ms-small-a6-reconstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

private theorem small_actor_le_of_moved_le
    (A D : Subgroup (Equiv.Perm (Fin 6))) (hA : A ≠ ⊥)
    (hsmall : fixedCodim (naturalRepresentation (Fin 6)) A ≤ 1)
    (hmoved : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ D ≤
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A) : D ≤ A := by
  open NaturalPairing in
  have hfixed : fixedSpace (naturalRepresentation (Fin 6)) A ≤
      fixedSpace (naturalRepresentation (Fin 6)) D := by
    rw [moved_eq_fixed_orthogonal,moved_eq_fixed_orthogonal] at hmoved
    have hh := form.orthogonal_le hmoved
    simpa only [LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl] using hh
  have hsup : fixedSpace (naturalRepresentation (Fin 6)) (A ⊔ D) =
      fixedSpace (naturalRepresentation (Fin 6)) A := by
    have hh : fixedSpace (naturalRepresentation (Fin 6)) (A ⊔ D) =
        fixedSpace (naturalRepresentation (Fin 6)) A ⊓ fixedSpace (naturalRepresentation (Fin 6)) D :=
      (naturalRepresentation (Fin 6)).invariants_comp_sup A D
    rw [hh,inf_eq_left.mpr hfixed]
  have hsupsmall : fixedCodim (naturalRepresentation (Fin 6)) (A ⊔ D) ≤ 1 := by
    change Module.finrank (ZMod 2) ((natural (Fin 6)) ⧸
      fixedSpace (naturalRepresentation (Fin 6)) (A ⊔ D)) ≤ 1
    rw [hsup]
    exact hsmall
  have hsupne : A ⊔ D ≠ ⊥ := fun he => hA (le_bot_iff.mp (he ▸ le_sup_left))
  obtain ⟨t,_,ht,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers
    (A ⊔ D) hsupne hsupsmall
  have hc : Nat.card (A ⊔ D : Subgroup (Equiv.Perm (Fin 6))) = 2 := by
    rw [he,Nat.card_zpowers,ht.orderOf]
  have hAc := (one_lt_card_iff_ne_bot A).mpr hA
  have heq : A = A ⊔ D := eq_of_le_of_card_ge le_sup_left (by omega)
  exact heq ▸ le_sup_right

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in

/-- The fixed hyperplane's edge displacement controls the entire actor image
through the original natural quotient; the full cover is retained. -/
theorem cover_actor_le_of_fixed_displacement (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (A D : Subgroup d.overgroup) (hA : A ≤ d.radical)
    (hne : ¬ A ≤ pCore 2 d.overgroup)
    (hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2)
    (hcomm : ⁅replacementMoved d,D⁆ ≤
      ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),d.radical⁆) :
    D ≤ pCore 2 d.overgroup ⊔ A := by
  let := replacementMoved_normal h d
  let U := replacementMoved d
  let f := coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)
  let W := subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map s.projection)
  let T := (W.comap f).toAddSubgroup.toSubgroup'.map U.subtype
  have hnA : A.map s.projection ≠ ⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff A).mp he)
  have hsmall : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      f (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) (A.map s.projection)).trans hsmall
  have hdisp := PointCoreTranspositionFixed.small_image_fixed_displacement_le u
    (A.map s.projection) ((map_mono hA).trans hR) hnA hnat
  have hT : ⁅U ⊓ centralizer (A : Set d.overgroup),d.radical⁆ ≤ T := by
    apply commutator_le.mpr
    intro v hv r hr
    have hcu : ⁅v,r⁆ ∈ U := (commutator_le_left U d.radical)
      (commutator_mem_commutator hv.1 hr)
    refine ⟨⟨⁅v,r⁆,hcu⟩,?_,rfl⟩
    change f (Additive.ofMul (⟨⁅v,r⁆,hcu⟩ : U)) ∈ W
    rw [NormalElementaryQuotient.vector_commutator U s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm) ⟨v,hv.1⟩ r,map_sub]
    change f (Additive.ofMul ⟨v,hv.1⟩) -
      f (coverAction s (s.projection r) (Additive.ofMul ⟨v,hv.1⟩)) ∈ W
    rw [show f (coverAction s (s.projection r) (Additive.ofMul ⟨v,hv.1⟩)) =
      naturalRepresentation (Fin 6) (s.projection r) (f (Additive.ofMul ⟨v,hv.1⟩)) from
        coverMap_equivariant s _ _]
    apply W.neg_mem_iff.mp
    rw [neg_sub]
    apply hdisp
    apply Submodule.subset_span
    refine ⟨s.projection r,hR (mem_map_of_mem _ hr),f (Additive.ofMul ⟨v,hv.1⟩),?_,rfl⟩
    have hfixed := (NormalElementaryQuotient.mem_fixedSpace_image U s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm) A
      (Additive.ofMul ⟨v,hv.1⟩)).mpr hv.2
    intro a
    change naturalRepresentation (Fin 6) a (f (Additive.ofMul ⟨v,hv.1⟩)) =
      f (Additive.ofMul ⟨v,hv.1⟩)
    exact (coverMap_equivariant s a _).symm.trans (congrArg f (hfixed a))
  have hspace : subspaceCommutator (coverAction s) ⊤ (D.map s.projection) ≤ W.comap f := by
    have hh : NormalElementaryQuotient.commutatorSpace U D =
        subspaceCommutator (coverAction s) ⊤ (D.map s.projection) :=
      NormalElementaryQuotient.commutatorSpace_eq U s.projection s.surjective
        (s.projection_kernel.trans (moved_centralizer s).symm) D
    rw [←hh]
    intro v hv
    change (v.toMul : d.overgroup) ∈ ⁅U,D⁆ at hv
    obtain ⟨w,hw,he⟩ := hT (hcomm hv)
    have he' : w = v.toMul := Subtype.ext he
    change Additive.ofMul w ∈ W.comap f at hw
    simpa only [he',ofMul_toMul] using hw
  have hm : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (D.map s.projection) =
      (subspaceCommutator (coverAction s) ⊤ (D.map s.projection)).map f := by
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction s) (MonoidHom.id _) f
      (fun g v => (coverMap_equivariant s g v).symm) (D.map s.projection) ⊤
    have hf : f.range = ⊤ := LinearMap.range_eq_top.mpr
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
    simpa only [Submodule.map_top,hf,map_id] using hh
  have him : D.map s.projection ≤ A.map s.projection :=
    small_actor_le_of_moved_le _ _ hnA hnat (hm ▸ Submodule.map_le_iff_le_comap.mpr hspace)
  have hle := (le_comap_map s.projection D).trans (comap_mono him)
  rw [Subgroup.comap_map_eq,s.projection_kernel] at hle
  exact hle.trans_eq (sup_comm _ _)

include h e hz in
private theorem full_fixed_seed_edge_commutator
    {c t : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t)
    (D : Subgroup (FreeAmalgam d.radical)) (hD : D ≤ Q d.radical t) :
    ⁅Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)),D⁆ =
      ⁅U d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)),D⁆ := by
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
  rw [heq]
  apply le_antisymm _ (commutator_mono le_sup_left le_rfl)
  apply commutator_le.mpr
  intro x hx r hr
  have hn : Z d.radical t ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    (le_inf hseedN (hseedA.trans (centralizer (A : Set (FreeAmalgam d.radical))).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hp : x ∈ (F : Set (FreeAmalgam d.radical)) * (Z d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [←coe_mul_of_right_le_normalizer_left F (Z d.radical t) hn]
    exact hx
  obtain ⟨w,hw,z,hz,rfl⟩ := hp
  have hzero : ⁅z,r⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hseed hz r (hD hr)).symm
  rw [commutatorElement_mul_left_eq_conj_mul,hzero,mul_one,mul_inv_cancel,one_mul]
  exact commutator_mem_commutator hw hr

include s in

/-- Transport the actor bound through the actual oriented edge. The fixed
part of the full seed has the same edge commutator as its moving part. -/
theorem edge_actor_le_of_fixed_displacement
    (hc : DistanceTwo.CentralLayer d) (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t)
    (A D : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t)
    (hD : D ≤ stabilizer d.radical c) (hne : ¬ A ≤ Q d.radical c)
    (hindex : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2)
    (hcomm : ⁅U d.radical c,D⁆ ≤
      ⁅Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)),Q d.radical t⁆) :
    D ≤ Q d.radical c ⊔ A := by
  have hcoords : ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical c ∧
      d.radical.map i = Q d.radical t ∧ (pCore 2 d.overgroup).map i = Q d.radical c ∧
      (replacementMoved d).map i = U d.radical c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_,?_⟩
      · change ((MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)).range = _
        have he : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
          (stabilizer_m_base d.radical).symm
        rw [MonoidHom.range_comp,he,←stabilizer_act]
        simp only [alpha,act_mVertex,one_mul]
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
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := hcoords
  have hmA : (A.comap i).map i = A := map_comap_eq_self
    (hA.trans (hiR ▸ map_le_range i _))
  have hmD : (D.comap i).map i = D := map_comap_eq_self (hD.trans_eq hir.symm)
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
  have hcomm' : ⁅replacementMoved d,D.comap i⁆ ≤
      ⁅replacementMoved d ⊓ centralizer (A.comap i : Set d.overgroup),d.radical⁆ := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [map_commutator,map_commutator,←map_inf_centralizer_of_injective i hi,
      hiU,hiR,hmA,hmD]
    rw [full_fixed_seed_edge_commutator (h := h) (e := e) (hz := hz) hcol hct A hA (Q d.radical t) le_rfl] at hcomm
    exact hcomm
  have hm := map_mono (f := i)
    (cover_actor_le_of_fixed_displacement s u hR (A.comap i) (D.comap i) hAr hAn hidx hcomm')
  rwa [Subgroup.map_sup,hiQ,hmA,hmD] at hm

include s in

/-- An endpoint actor controlled by the full reverse kernel's predecessor
commutator fixes that kernel pointwise and has only the original small image. -/
theorem critical_kernel_displacement_actor
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (D : Subgroup (FreeAmalgam d.radical)) (hD : D ≤ stabilizer d.radical a')
    (hcomm : ⁅U d.radical a',D⁆ ≤
      ⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical (p.walk.getVert (p.walk.length-2))⁆) :
    D ≤ Q d.radical a' ⊔ Z d.radical a ∧
      D ≤ centralizer (Z d.radical a' ⊓ Q d.radical a : Set (FreeAmalgam d.radical)) := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let t := p.walk.getVert (p.walk.length-1)
  have hat : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have hpred : Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical t := by
    apply Q_le_adjacent_h d.radical ht
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hZt : Z d.radical a ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-1 < replacementDistance h d
    omega
  have hfixed : Z d.radical a' ⊓ Q d.radical a =
      Z d.radical a' ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)))
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←C_eq_Q s hc a p.start_color]
      exact ⟨critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
        (by rw [(replacementGeometry h d).distance_constant a p.start_color]
            exact replacementDistance_pos h d) p.critical hx.1,hx.2⟩
  let := finite_Z d.radical a'
  let : Finite (U d.radical a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a')) (inclusion_injective _)
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a') ≤ 2 := by
    have hQC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a') index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have hupper := hcomm.trans (commutator_mono le_rfl hpred)
  rw [hfixed] at hupper
  have hle := edge_actor_le_of_fixed_displacement s hc u hR p.end_color hat
    (Z d.radical a) D hZt hD p.critical.2 hindex hupper
  refine ⟨hle,hle.trans (sup_le ?_ ?_)⟩
  · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))).trans (centralizer_le inf_le_left)
  · exact (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color)).trans (centralizer_le inf_le_right)


include h in

/-- The same residual element preserves the slice commutator while
transporting its core actor. No invariance of the slice itself is assumed. -/
theorem small_slice_commutator_residual_transport
    (hb : 2 < replacementDistance h d) {c : Vertex d.radical}
    (hcol : color d.radical c = false)
    (A : Subgroup (FreeAmalgam d.radical))
    (hAB : A ≤ B d.radical c ((replacementGeometry h d).Z_normal _))
    (hcard : Nat.card (⁅A,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2)
    (D : Subgroup (FreeAmalgam d.radical)) (hD : D ≤ Q d.radical c)
    (k : FreeAmalgam d.radical) (hk : k ∈ Ltilde d.radical c) :
    ⁅A,D.map (MulAut.conj k).toMonoidHom⁆ = ⁅A,D⁆ := by
  have hfixed := small_slice_core_commutator_le_fixedCore (h := h) hb hcol A hAB hcard
  have hVQ := (replacementGeometry h d).V_le_Q hb c hcol
  have hVG := hVQ.trans (show Q d.radical c ≤ stabilizer d.radical c from fun _ hx => hx.1)
  have hAQ : A ≤ Q d.radical c := by
    intro a ha
    exact hVQ (((mem_B_iff d.radical c _ hVG a).mp (hAB ha)).1)
  have hZQ : Z d.radical c ≤ centralizer (Q d.radical c : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c hcol)
  have he (a : FreeAmalgam d.radical) (ha : a ∈ A)
      (x : FreeAmalgam d.radical) (hx : x ∈ Q d.radical c) :
      ⁅a,k*x*k⁻¹⁆ = ⁅a,x⁆ := by
    have hx' : k*x*k⁻¹ ∈ Q d.radical c :=
      (mem_normalizer_iff.mp ((Q_normalized d.radical c) (Ltilde_le_stabilizer _ hk)) x).mp hx
    have hka : ⁅k,a⁆ ∈ Z d.radical c :=
      ((mem_B_iff d.radical c _ hVG a).mp (hAB ha)).2 k hk
    have hax' : ⁅a,k*x*k⁻¹⁆ ∈ Q d.radical c :=
      (Subgroup.commutator_le_sup _ _).trans (sup_le hAQ le_rfl)
        (commutator_mem_commutator ha hx')
    have hzero : ⁅⁅k,a⁆,k*x*k⁻¹⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hZQ hka _ hx').symm
    have hfix : k*⁅a,x⁆*k⁻¹ = ⁅a,x⁆ := by
      have hh := (hfixed (commutator_mem_commutator ha hx)).2 k hk
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

include s in

/-- The full endpoint displacement cannot equal a nonzero backward-kernel
commutator after the predecessor residual transport. Last-edge geometry
supplies the transported actor's endpoint containment. -/
theorem critical_kernel_residual_displacement_ne
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hslice : Z d.radical a' ⊓ Q d.radical a ≤
      B d.radical (p.walk.getVert (p.walk.length-2)) ((replacementGeometry h d).Z_normal _))
    (D : Subgroup (FreeAmalgam d.radical))
    (hD : D ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Z d.radical a' ⊓ Q d.radical a,D⁆ ≠ ⊥)
    (k : FreeAmalgam d.radical)
    (hk : k ∈ Ltilde d.radical (p.walk.getVert (p.walk.length-2))) :
    ⁅U d.radical a',D.map (MulAut.conj k).toMonoidHom⁆ ≠
      ⁅Z d.radical a' ⊓ Q d.radical a,D⁆ := by
  intro he
  have hcol : color d.radical (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have heven := replacementDistance_even h d
    rw [Nat.even_iff] at heven ⊢
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have hcard := small_critical_kernel_predecessor_card s hc hb u hR p hsmall
  have htransport := small_slice_commutator_residual_transport (h := h)
    hb hcol _ hslice hcard D hD k hk
  have hDk : D.map (MulAut.conj k).toMonoidHom ≤ stabilizer d.radical a' := by
    have hkQ : (Q d.radical (p.walk.getVert (p.walk.length-2))).map
        (MulAut.conj k).toMonoidHom = Q d.radical (p.walk.getVert (p.walk.length-2)) :=
      mem_normalizer_iff_map_conj_eq.mp ((Q_normalized d.radical _)
        (Ltilde_le_stabilizer _ hk))
    apply ((map_mono hD).trans_eq hkQ).trans
    have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
    let t := p.walk.getVert (p.walk.length-1)
    have hat : Adjacent d.radical a' t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
      rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
      exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
    have ht : color d.radical t = true := by
      have hh := adjacent_color_ne d.radical hat
      rw [p.end_color] at hh
      cases he : color d.radical t <;> simp_all
    apply (Q_le_adjacent_h d.radical ht ?_).trans
      (show Q d.radical t ≤ stabilizer d.radical a' from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hactor := (critical_kernel_displacement_actor s hc hb u hR p hsmall
    (D.map (MulAut.conj k).toMonoidHom) hDk
    (he.le.trans (commutator_mono le_rfl hD))).2
  apply hne
  rw [←htransport,commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hactor

/-- The source-(5.8) residual transporter cannot turn a nonzero backward
kernel commutator into the entire endpoint displacement. The quotient marking
and central layer are supplied by the original known-simple replacement. -/
theorem critical_kernel_residual_displacement_ne_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map (SourceReduction.projection h e hz hn d) ≤
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hslice : Z d.radical a' ⊓ Q d.radical a ≤
      B d.radical (p.walk.getVert (p.walk.length-2)) ((replacementGeometry h d).Z_normal _))
    (D : Subgroup (FreeAmalgam d.radical))
    (hD : D ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Z d.radical a' ⊓ Q d.radical a,D⁆ ≠ ⊥)
    (k : FreeAmalgam d.radical)
    (hk : k ∈ Ltilde d.radical (p.walk.getVert (p.walk.length-2))) :
    ⁅U d.radical a',D.map (MulAut.conj k).toMonoidHom⁆ ≠
      ⁅Z d.radical a' ⊓ Q d.radical a,D⁆ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hR' : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  exact critical_kernel_residual_displacement_ne s hc hb u hR' p hsmall hslice D hD hne k hk




include s in
/-- The full reverse kernel is the source moving kernel times the last edge
seed. That seed lies in the predecessor slice and centralizes its core, so
slice placement and every predecessor-core commutator agree for both kernels. -/
theorem critical_kernel_predecessor_moving
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    Z d.radical a' ⊓ Q d.radical a =
        (U d.radical a' ⊓ Q d.radical a) ⊔ Z d.radical (p.walk.getVert (p.walk.length-1)) ∧
      (Z d.radical a' ⊓ Q d.radical a ≤
          B d.radical (p.walk.getVert (p.walk.length-2)) ((replacementGeometry h d).Z_normal _) ↔
        U d.radical a' ⊓ Q d.radical a ≤
          B d.radical (p.walk.getVert (p.walk.length-2)) ((replacementGeometry h d).Z_normal _)) ∧
      ∀ D : Subgroup (FreeAmalgam d.radical),
        D ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) →
        ⁅Z d.radical a' ⊓ Q d.radical a,D⁆ = ⁅U d.radical a' ⊓ Q d.radical a,D⁆ := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let c := p.walk.getVert (p.walk.length-2)
  let t := p.walk.getVert (p.walk.length-1)
  have hat : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hct : Adjacent d.radical c t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hcol : color d.radical c = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have hZt : Z d.radical a ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-1 < replacementDistance h d
    omega
  have hfix (T : Subgroup (FreeAmalgam d.radical)) (hT : T ≤ Z d.radical a') :
      T ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) = T ⊓ Q d.radical a := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←C_eq_Q s hc a p.start_color]
      exact ⟨critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
        (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
            exact replacementDistance_pos h d) p.critical (hT hx.1),hx.2⟩
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)))
  have hseed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedN : Z d.radical t ≤ normalizer (U d.radical a' : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical p.end_color hat).trans (Z_le_stabilizer d.radical a')).trans (U_normalized a')
  have heq : Z d.radical a' ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
      (U d.radical a' ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))) ⊔ Z d.radical t := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d p.end_color hat,
      sup_comm (U d.radical a'),inf_centralizer_sup_of_centralizing _ _ _ hseedN
        (hseed.trans (centralizer_le hZt))]
    exact sup_comm _ _
  rw [hfix _ le_rfl,hfix _ (DistanceEight.U_le_Z d.radical a')] at heq
  refine ⟨heq,?_,?_⟩
  · rw [heq]
    have hseedB := (adjacent_Z_le d.radical hcol hct).trans (Escape.EdgeTransfer.Z_le_B hb c hcol)
    exact ⟨fun hh => le_sup_left.trans hh,fun hh => sup_le hh hseedB⟩
  · intro D hD
    have hh := full_fixed_seed_edge_commutator (h := h) (e := e) (hz := hz)
      p.end_color hat (Z d.radical a) hZt D (hD.trans (Q_le_adjacent_h d.radical ht hct))
    rwa [hfix _ le_rfl,hfix _ (DistanceEight.U_le_Z d.radical a')] at hh

include h in
private theorem residual_neighbor_transporter
    {c t v : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t) (hcv : Adjacent d.radical c v) :
    ∃ k ∈ Ltilde d.radical c, act d.radical k t = v := by
  have hsup : replacementComponent d ⊔ d.radical = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨l,hl,r,hr,rfl⟩ := replacement_product h d g
    exact mul_mem (mem_sup_left hl) (mem_sup_right hr)
  have hbase : Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (beta d.radical) =
      stabilizer d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d,Q_beta,←Subgroup.map_sup,hsup]
    exact (MonoidHom.range_eq_map (embedM d.radical)).symm.trans (stabilizer_m_base d.radical).symm
  have hgen : Ltilde d.radical c ⊔ Q d.radical t = stabilizer d.radical c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
      rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act] at he
      simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
    · rw [hg.1] at hcol
      cases hcol
  have hn : Q d.radical t ≤ normalizer (Ltilde d.radical c : Set (FreeAmalgam d.radical)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hxc : x⁻¹ ∈ stabilizer d.radical c :=
      (stabilizer d.radical c).inv_mem (hx.2 _ (adjacent_symm d.radical hct))
    have hh := Ltilde_act d.radical x⁻¹ c
    rw [inv_inv,show act d.radical x⁻¹ c = c from hxc] at hh
    exact hh.symm
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical c hct hcv
  have hprod : g ∈ (Q d.radical t : Set (FreeAmalgam d.radical)) *
      (Ltilde d.radical c : Set (FreeAmalgam d.radical)) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hn,
      sup_comm (Q d.radical t) (Ltilde d.radical c),hgen]
    exact hg
  obtain ⟨q,hq,k,hk,rfl⟩ := hprod
  refine ⟨k,hk,?_⟩
  have hqt : act d.radical q t = t := hq.1
  simpa only [act_mul,hqt] using hgt

/-- Construct the residual shift used in (5.8) on the same critical walk.
The element moves the last edge to the preceding edge, retains all transported
vertices, and cannot turn the nonzero backward kernel commutator into the
full endpoint displacement. Both original central covers are retained. -/
theorem critical_kernel_selected_residual_shift_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map (SourceReduction.projection h e hz hn d) ≤
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hslice : U d.radical a' ⊓ Q d.radical a ≤
      B d.radical (p.walk.getVert (p.walk.length-2)) ((replacementGeometry h d).Z_normal _))
    (delta : Vertex d.radical)
    (hD : Z d.radical delta ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅U d.radical a' ⊓ Q d.radical a,Z d.radical delta⁆ ≠ ⊥) :
    ∃ k ∈ Ltilde d.radical (p.walk.getVert (p.walk.length-2)),
      act d.radical k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3) ∧
      ⁅U d.radical a',Z d.radical (act d.radical k⁻¹ delta)⁆ ≠
        ⁅U d.radical a' ⊓ Q d.radical a,Z d.radical delta⁆ ∧
      (∀ i, (p.act k).walk.getVert i = act d.radical k (p.walk.getVert i)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hbridge := critical_kernel_predecessor_moving s hc hb p
  have hfullslice := hbridge.2.1.mpr hslice
  have hcomm := hbridge.2.2 (Z d.radical delta) hD
  have hfullne : ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical delta⁆ ≠ ⊥ := by
    rwa [hcomm]
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have hct : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hcv : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-3)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-3) (by omega)
    rw [show p.walk.length-3+1=p.walk.length-2 by omega] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  obtain ⟨k,hk,hkt⟩ := residual_neighbor_transporter (h := h) hcol hct hcv
  refine ⟨k,hk,hkt,?_,?_⟩
  · rw [Z_act,inv_inv]
    rw [←hcomm]
    exact critical_kernel_residual_displacement_ne_knownSimple
      (e := e) (hz := hz) (hn := hn) hb u hR p hsmall hfullslice (Z d.radical delta) hD hfullne k hk
  · intro i
    simp only [CriticalPath.act,actWalk_getVert]

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
