module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePairedEdges

/-!
# The same-radius action estimates for paired three-pair shifts

A subgroup of the three-pair group of order greater than two has the same
fixed vectors as the full three-pair group on either six-letter cover. On
the natural quotient a nonzero vector is a duad. A duad outside the marked
matching has at most two fixing words among the eight three-pair words;
a duad in the matching is fixed by all eight. The existing fixed-vector
lifting theorem gives the augmentation-cover result without discarding
its constant line. Equivariant transport retains the actual conjugate
marking and the original quotient projection.

At an incident edge, the full seed is its moved cover joined with the
central edge attachment. The fixed-space comparison therefore places every
full-seed vector fixed by a large edge actor in the edge seed. The original
and selected edge kernels in an EdgePairedBackwardShift generate the entire
intermediate stabilizer. Thus a selected critical line fixed by a large
actor in the original edge kernel is central at that intermediate vertex.

Apply this twice to the same endpoint radius V at z₄. Its full image at
c₂ controls R₄; the image of V intersect Q_c₂ at c₄ controls R₆. The actual
three-shift consumer retains the previously constructed four-group R₄R₆,
its radius centralization, every overlap vertex and both orientations.
These prove the two action implications in the last paragraph of (5.11).
The strict endpoint-radius bound and intermediate-stabilizer noncentrality
remain necessary for its contradiction. The original Sylow branches,
distance-four exclusion and unconditional replacement distance two remain
with the same assembly owner.

Both moved covers of orders sixteen and thirty-two, all central attachments,
the original nonsylow radical and the literal replacement graph are retained.
No exceptional reconstruction graph or full point-core hypothesis is used.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3), (5.5)--(5.6) and the last paragraph of (5.11), printed
pp.866--867,916--918,924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace CubeRadiusAction
local notation "S" => Equiv.Perm (Fin 6)
open NaturalGeometry

private theorem outside_pair_fixer_card : ∀ i j : Fin 6, i ≠ j →
    pair i j ∉ baseSyntheme →
    (Finset.univ.filter (fun k : Fin 8 =>
      pair (initialWords 3 k i) (initialWords 3 k j) = pair i j)).card ≤ 2 := by
  decide +kernel

private theorem inside_pair_fixed : ∀ i j : Fin 6, pair i j ∈ baseSyntheme →
    ∀ k : Fin 8, pair (initialWords 3 k i) (initialWords 3 k j) = pair i j := by
  decide +kernel

private theorem natural_large_fixed (A : Subgroup S) (hA : A ≤ D 6)
    (hcard : 2 < Nat.card A) :
    fixedSpace (naturalRepresentation (Fin 6)) A ≤
      fixedSpace (naturalRepresentation (Fin 6)) (D 6) := by
  intro v hv
  rcases vector_cases v with rfl | ⟨d,rfl⟩
  · exact Submodule.zero_mem _
  change pairVector d.val.1 d.val.2 ∈ _ at hv ⊢
  have hne : d.val.1 ≠ d.val.2 := ne_of_lt d.property
  have hin : pair d.val.1 d.val.2 ∈ baseSyntheme := by
    by_contra hout
    let F := Finset.univ.filter (fun k : Fin 8 =>
      pair (initialWords 3 k d.val.1) (initialWords 3 k d.val.2) = pair d.val.1 d.val.2)
    have hex (a : A) : ∃ k : Fin 8, initialWords 3 k = a.val :=
      (mem_disjointTranspositions_iff (3 : Fin 4) a.val).mp (hA a.property)
    let code (a : A) : F := ⟨(hex a).choose, by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [(hex a).choose_spec]
      apply (pairVector_eq_iff (a.val.injective.ne hne) hne).mp
      rw [←pairVector_map]
      exact hv a⟩
    have hi : Function.Injective code := by
      intro a b hab
      apply Subtype.ext
      have he := congrArg Subtype.val hab
      exact (hex a).choose_spec.symm.trans ((congrArg (initialWords 3) he).trans (hex b).choose_spec)
    have hc := Nat.card_le_card_of_injective code hi
    have hcF : Nat.card F ≤ 2 := by
      rw [Nat.card_eq_fintype_card,Fintype.card_coe]
      exact outside_pair_fixer_card _ _ hne hout
    omega
  intro g
  obtain ⟨k,hk⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) g.val).mp g.property
  change naturalRepresentation (Fin 6) g.val (pairVector d.val.1 d.val.2)=_
  rw [pairVector_map]
  apply (pairVector_eq_iff (g.val.injective.ne hne) hne).mpr
  rw [←hk]
  exact inside_pair_fixed _ _ hin k

private theorem core_large_fixed (A : Subgroup S) (hA : A ≤ D 6)
    (hcard : 2 < Nat.card A) :
    fixedSpace (coreRepresentation (Fin 6)) A ≤
      fixedSpace (coreRepresentation (Fin 6)) (D 6) := by
  intro v hv
  have hnat : coreToNatural (Fin 6) v ∈ fixedSpace (naturalRepresentation (Fin 6)) A := by
    intro a
    change naturalRepresentation (Fin 6) a.val (coreToNatural (Fin 6) v)=_
    rw [←coreToNatural_equivariant]
    exact congrArg (coreToNatural (Fin 6)) (hv a)
  have hf := natural_large_fixed A hA hcard hnat
  exact (core_fixed_disjointTranspositions_iff 6 3 v).mpr
    ((natural_fixed_disjointTranspositions_iff (by decide : 3 ≤ 6) 3 v).mp hf)

private theorem model_large_fixed {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y) (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (u : S) (A : Subgroup S)
    (hA : A ≤ (D 6).map (MulAut.conj u).toMonoidHom) (hcard : 2 < Nat.card A) :
    fixedSpace σ A ≤ fixedSpace σ ((D 6).map (MulAut.conj u).toMonoidHom) := by
  let f := (MulAut.conj u).toMonoidHom
  let A₀ := A.comap f
  have hmA : A₀.map f=A := map_comap_eq_self_of_surjective (MulAut.conj u).surjective A
  have ha₀ : A₀ ≤ D 6 := by
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj u).injective).mp
    rwa [hmA]
  have hc₀ : 2 < Nat.card A₀ := by
    rw [←card_map_of_injective (f := f) (K := A₀) (MulAut.conj u).injective,hmA]
    exact hcard
  intro v hv
  have hf : σ u⁻¹ v ∈ fixedSpace σ A₀ := by
    intro a
    have hh := congrArg (σ u⁻¹) (hv ⟨f a.val,a.property⟩)
    change σ u⁻¹ (σ (u*a.val*u⁻¹) v)=σ u⁻¹ v at hh
    simpa only [MonoidHom.comp_apply,Subgroup.coe_subtype,map_mul,Module.End.mul_apply,σ.inv_self_apply] using hh
  have hbase : σ u⁻¹ v ∈ fixedSpace σ (D 6) := by
    rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
    · have hEf : E (σ u⁻¹ v) ∈ fixedSpace (naturalRepresentation (Fin 6)) A₀ := by
        intro a
        simpa only [MonoidHom.comp_apply,Subgroup.coe_subtype,hE,MonoidHom.id_apply] using congrArg E (hf a)
      have hEall := natural_large_fixed A₀ ha₀ hc₀ hEf
      intro a
      apply E.injective
      simpa only [MonoidHom.comp_apply,Subgroup.coe_subtype,hE,MonoidHom.id_apply] using hEall a
    · have hEf : E (σ u⁻¹ v) ∈ fixedSpace (coreRepresentation (Fin 6)) A₀ := by
        intro a
        simpa only [MonoidHom.comp_apply,Subgroup.coe_subtype,hE,MonoidHom.id_apply] using congrArg E (hf a)
      have hEall := core_large_fixed A₀ ha₀ hc₀ hEf
      intro a
      apply E.injective
      simpa only [MonoidHom.comp_apply,Subgroup.coe_subtype,hE,MonoidHom.id_apply] using hEall a
  intro g
  obtain ⟨k,hk,hkg⟩ := g.property
  have hh := congrArg (σ u) (hbase ⟨k,hk⟩)
  change σ g.val v=v
  rw [←hkg]
  change σ (u*k*u⁻¹) v=v
  simpa only [MonoidHom.comp_apply,Subgroup.coe_subtype,map_mul,Module.End.mul_apply,σ.self_inv_apply] using hh
end CubeRadiusAction

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

include s in
private theorem cube_cover_large_fixed (u : S)
    (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    (A : Subgroup d.overgroup) (hA : A ≤ d.radical)
    (hlarge : 2 < (pCore 2 d.overgroup).relIndex A) :
    replacementMoved d ⊓ centralizer (A : Set d.overgroup) ≤
      centralizer (d.radical : Set d.overgroup) := by
  have hcard : 2 < Nat.card (A.map s.projection) := by
    rwa [←s.projection_kernel,relIndex_ker] at hlarge
  intro v hv k hk
  let w : Additive (replacementMoved d) := Additive.ofMul ⟨v,hv.1⟩
  have hfixed : w ∈ fixedSpace (coverAction s) (A.map s.projection) := by
    intro a
    obtain ⟨g,hg,he⟩ := a.property
    change coverAction s a.val w=w
    rw [←he]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [coverAction_conjugate]
    change g*v*g⁻¹=v
    rw [hv.2 g hg,mul_inv_cancel_right]
  have hfull := CubeRadiusAction.model_large_fixed (coverAction s) (cover_model s)
    u (A.map s.projection) ((map_mono hA).trans hR) hcard hfixed
  have hh := congrArg (fun a : Additive (replacementMoved d) => (a.toMul : d.overgroup))
    (hfull ⟨s.projection k,hR (mem_map_of_mem _ hk)⟩)
  simp only [MonoidHom.comp_apply,Subgroup.coe_subtype] at hh
  rw [coverAction_conjugate] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

include s in
/-- An actor of image order greater than two in an incident three-pair
kernel fixes only vectors in the edge seed. This retains the full central
attachment of the starting seed on either moved cover. -/
theorem cube_edge_large_fixed_le_seed (hc : DistanceTwo.CentralLayer d) (u : S)
    (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ Q d.radical t) (hlarge : 2 < (Q d.radical a).relIndex A) :
    Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) ≤ Z d.radical t := by
  have hcoords : ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical a ∧
      d.radical.map i = Q d.radical t ∧ (pCore 2 d.overgroup).map i = Q d.radical a ∧
      (replacementMoved d).map i = U d.radical a := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_,?_⟩
      · have he := stabilizer_act d.radical g (alpha d.radical)
        simpa only [i,alpha,act_mVertex,one_mul,stabilizer_m_base,Mbar,MonoidHom.range_comp] using he.symm
      · have he := Q_act d.radical g (beta d.radical)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
      · have he := Q_act d.radical g (alpha d.radical)
        rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := U_act d.radical g (alpha d.radical)
        rw [hc.U_eq_moved] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · rw [hg.1] at ha
      cases ha
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := hcoords
  have hmA : (A.comap i).map i=A := map_comap_eq_self (hA.trans (hiR ▸ map_le_range i _))
  have hAr : A.comap i ≤ d.radical := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmA,hiR]
  have hidx : 2 < (pCore 2 d.overgroup).relIndex (A.comap i) := by
    rw [←relIndex_map_map_of_injective _ _ hi,hmA,hiQ]
    exact hlarge
  have hU : U d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) ≤
      centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    have hh := (map_mono (f := i) (cube_cover_large_fixed s u hR (A.comap i) hAr hidx)).trans
      (map_centralizer_le_centralizer_image _ _)
    change (replacementMoved d ⊓ centralizer (A.comap i : Set d.overgroup)).map i ≤
      centralizer (d.radical.map i : Set (FreeAmalgam d.radical)) at hh
    rwa [←map_inf_centralizer_of_injective i hi,hiU,hmA,hiR] at hh
  have ht : color d.radical t=true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases he : color d.radical t <;> simp_all
  have hseed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedA := hseed.trans (centralizer_le hA)
  have hseedN : Z d.radical t ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical ha hat).trans (Z_le_stabilizer d.radical a)).trans (U_normalized a)
  have hfixed : Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) ≤
      centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d ha hat,
      sup_comm (U d.radical a),inf_centralizer_sup_of_centralizing _ _ _ hseedN hseedA]
    exact sup_le hseed hU
  have hZQ : Z d.radical a ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a ha)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant a ha]
    exact replacementDistance_pos h d
  intro x hx
  rw [Z,if_neg (by simp [ht])]
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a ha
  exact mem_omegaCenter_iff.mpr ⟨Q_le_adjacent_h d.radical ht hat (hZQ hx.1),
    elemPow_eq_one_of_isElementaryAbelian x hx.1,hfixed hx⟩

include e hz hn in
/-- The original and selected edge kernels now turn large-actor fixedness
into centrality of the selected critical line at the intermediate vertex. -/
theorem nonsylow_edge_paired_line_central_of_large_actor_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p)
    (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ Q d.radical (p.walk.getVert 1))
    (hlarge : 2 < (Q d.radical a).relIndex A)
    (hfixed : ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (A : Set (FreeAmalgam d.radical))) :
    ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ
      (i := 0) (p.length_eq_b ▸ replacementDistance_pos h d)
  have hline := nonsylow_paired_shift_commutator_knownSimple (e := e) (hz := hz) (hn := hn)
    hb hns p q.toPairedBackwardShift
  have hfirst := (le_inf hline.2.2.1 hfixed).trans
    (cube_edge_large_fixed_le_seed s hc u hR p.start_color hat A hA hlarge)
  exact (le_inf hfirst hline.2.1).trans q.edge_seed_intersection_central

include e hz hn in
/-- The two source-(5.11) action comparisons use the very same endpoint
radius. Its full image controls the first shifted line; its intersection
with the preceding core controls the next line. Both conclusions are at
the intermediate stabilizers, with both paired edge kernels accounted for. -/
theorem nonsylow_edge_paired_same_radius_actions_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p)
    (r : EdgePairedBackwardShift (h := h) q.path) :
    let z := p.walk.getVert (p.walk.length-2)
    let H := ⁅Z d.radical q.start,Z d.radical z⁆
    let K := ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆
    (2 < (Q d.radical a).relIndex (V d.radical z) →
      H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
    (2 < (Q d.radical q.start).relIndex (V d.radical z ⊓ Q d.radical a) →
      K ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) := by
  let z := p.walk.getVert (p.walk.length-2)
  let H := ⁅Z d.radical q.start,Z d.radical z⁆
  have hHQ : H ≤ centralizer (Q d.radical z : Set (FreeAmalgam d.radical)) :=
    (((critical_Z_commutator_le_moving (h := h) q.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical z)).trans
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical z q.path.end_color))
  have hHV : H ≤ centralizer (V d.radical z : Set (FreeAmalgam d.radical)) :=
    hHQ.trans (centralizer_le (V_le_Q d.radical (geometry := replacementGeometry h d)
      q.path.end_color (by change 2 < replacementDistance h d; omega)))
  have hVedge : V d.radical z ≤ Q d.radical (p.walk.getVert 1) := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) q.path.end_color
    have hl : p.walk.length=replacementDistance h d := p.length_eq_b
    have hd := SimpleGraph.dist_le ((p.walk.drop 1).take (p.walk.length-3))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
      inf_eq_left.mpr (by omega : p.walk.length-3 ≤ p.walk.length-1),
      SimpleGraph.Walk.drop_getVert,show 1+(p.walk.length-3)=p.walk.length-2 by omega] at hd
    change (cosetGraph d.radical).dist z (p.walk.getVert 1)+2 < replacementDistance h d
    rw [SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist (p.walk.getVert 1) (p.walk.getVert (p.walk.length-2))+2 < _
    omega
  have hedge : color d.radical q.edge=true := by
    have hh := adjacent_color_ne d.radical q.adjacent_start
    rw [p.start_color] at hh
    cases he : color d.radical q.edge <;> simp_all
  have hAedge : V d.radical z ⊓ Q d.radical a ≤ Q d.radical (q.path.walk.getVert 1) := by
    rw [q.first]
    exact inf_le_right.trans (Q_le_adjacent_h d.radical hedge q.adjacent_start)
  have hKfixed := (nonsylow_paired_shift_commutator_knownSimple (e := e) (hz := hz) (hn := hn)
    hb hns q.path r.toPairedBackwardShift).2.2.2.2.1
  constructor
  · intro hlarge
    exact nonsylow_edge_paired_line_central_of_large_actor_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns p q (V d.radical z) hVedge hlarge hHV
  · intro hlarge
    exact nonsylow_edge_paired_line_central_of_large_actor_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns q.path r
      (V d.radical z ⊓ Q d.radical a) hAedge hlarge
      (hKfixed.trans (centralizer_le inf_le_left))

include e hz hn in
/-- The original nonsylow replacement supplies the actual terminal plane
and both same-radius action estimates in one coherent three-shift chain.
The strict radius bound and intermediate noncentrality remain separate
source obligations; they are not hypotheses hidden in this construction. -/
theorem nonsylow_edge_paired_terminal_radius_actions_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ q : EdgePairedBackwardShift (h := h) p,
      ∃ r : EdgePairedBackwardShift (h := h) q.path,
        ∃ t : EdgePairedBackwardShift (h := h) r.path,
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          let z₆ := r.path.walk.getVert (r.path.walk.length-2)
          let R₄ := ⁅Z d.radical r.start,Z d.radical z₄⁆
          let R₆ := ⁅Z d.radical t.start,Z d.radical z₆⁆
          R₄ ⊓ R₆ = ⊥ ∧ Nat.card (R₄ ⊔ R₆ : Subgroup (FreeAmalgam d.radical)) = 4 ∧
          R₄ ⊔ R₆ ≤ Z d.radical r.start ⊓
            centralizer (V d.radical z₄ : Set (FreeAmalgam d.radical)) ∧
          (2 < (Q d.radical q.start).relIndex (V d.radical z₄) →
            R₄ ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) ∧
          (2 < (Q d.radical r.start).relIndex (V d.radical z₄ ⊓ Q d.radical q.start) →
            R₆ ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical))) := by
  obtain ⟨q,r,t,hdis,hcard,hplane⟩ := nonsylow_edge_paired_terminal_plane_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p
  have hact := nonsylow_edge_paired_same_radius_actions_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns q.path r t
  exact ⟨q,r,t,hdis,hcard,hplane,hact⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
