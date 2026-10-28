module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPrescribedUnequalComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourLargeEqualComparison
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalTerminalComparison
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourComparisonEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourUnequalRootCentrality
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourUnequalComparisonEscape

/-!
# The prescribed comparison for every first mover at large critical image

The prescribed first orbit identifies the complete fixed kernels. Individual
generation and actual endpoint nonnormality exclude a failed comparison:
normality of the seed intersection forces the moving layer into the neighbor;
the full central seed term also lies there. Equal seed orders force equality,
contrary to the actual nonnormality. This applies to the point branch as well.

The final producer combines the actual point, equal and unequal selections,
removing all first-mover premises. Internal imports reuse the existing
transport and escape proofs; no private names occur in public statements.
No prescribed-orbit assertion is made for an arbitrary initial neighbor.
Source: MS93 (5.12)(1), printed pp.924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem generated_root_not_le_nonnormal_neighbor
    {geometry : Geometry d.radical} {c e a w : Vertex d.radical}
    (path : CriticalPath d.radical geometry c e) (hb : 4 ≤ geometry.b d.radical)
    (hcw : Adjacent d.radical c w) (haw : Adjacent d.radical a w)
    (ha : color d.radical a=false)
    (hi : (Q d.radical c).relIndex (Z d.radical e)=Nat.card F)
    (hres : Ltilde d.radical c ≤ Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical e)
    (hn : ¬ Z d.radical e ≤ normalizer
      ((Z d.radical a ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ¬ ⁅Z d.radical c,Z d.radical e⁆ ≤ Z d.radical a := by
  intro hle
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical w) (Nat.card F^2)
  let I := Z d.radical c ⊓ Z d.radical a
  let S := stabilizer d.radical c
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 c (adjacent_symm _ hcw))
  have hJSa : J ≤ stabilizer d.radical a := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm _ haw))
  have hR : ⁅Z d.radical c,Z d.radical e⁆ ≤ I :=
    le_inf (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path) hle
  have hJN : J ≤ normalizer (I : Set (FreeAmalgam d.radical)) :=
    (le_inf (hJS.trans (Z_normalized d.radical c))
      (hJSa.trans (Z_normalized d.radical a))).trans inf_normalizer_le_normalizer_inf
  have hEN : Z d.radical e ≤ normalizer (I : Set (FreeAmalgam d.radical)) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono inf_le_left le_rfl).trans hR)
  have hLN := hres.trans (sup_le hJN hEN)
  have hQN : Q d.radical c ≤ normalizer (I : Set (FreeAmalgam d.radical)) :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical c path.start_color))).trans
      (centralizer_le inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)
  have hlocal : Ltilde d.radical c ⊔ Q d.radical c=S := by
    obtain ⟨i,hinj,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) path.start_color
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]
  have hSN : S ≤ normalizer (I : Set (FreeAmalgam d.radical)) :=
    hlocal.ge.trans (sup_le hLN hQN)
  obtain ⟨E,hE,f,hf,hfQ,hrest⟩ := h.replacement_inner_natural_action d geometry hb path.start_color
  let Z₀ := (Z d.radical c).subgroupOf S
  let I₀ := I.subgroupOf S
  let T := (Z d.radical e).subgroupOf S
  have hZcS : Z d.radical c ≤ S := Z_le_stabilizer d.radical c
  have hIS : I ≤ S := inf_le_left.trans hZcS
  have hES : Z d.radical e ≤ S := path.endpoint_Z_le_start_stabilizer (by omega)
  let : Z₀.Normal := (normal_subgroupOf_iff_le_normalizer hZcS).mpr (Z_normalized d.radical c)
  let : I₀.Normal := (normal_subgroupOf_iff_le_normalizer hIS).mpr hSN
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Matrix.symplecticGroup (Fin 2) E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hk : IsPGroup 2 f.ker := by
    have hp := Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) c path.start_color
    exact (hfQ.symm ▸ hp).of_injective
      (f.ker.equivMapOfInjective S.subtype S.subtype_injective).toMonoidHom
      (f.ker.equivMapOfInjective S.subtype S.subtype_injective).injective
  have hT : ¬ T ≤ f.ker := by
    intro hh
    have hm := map_mono (f := S.subtype) hh
    rw [map_subgroupOf_eq_of_le hES,hfQ] at hm
    have hone := relIndex_eq_one.mpr hm
    rw [hi] at hone
    exact (Finite.one_lt_card (α := F)).ne' hone
  have hc : ⁅Z₀,T⁆ ≤ I₀ := by
    apply (map_le_map_iff_of_injective S.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hZcS,
      map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hIS]
    exact hR
  have hwhole := commutator_pResidual_le_of_simple_kernel_escape 2 f hf hk Z₀ I₀ T hT hc
  have hUI : U d.radical c ≤ I := by
    have hh := map_mono (f := S.subtype) hwhole
    rwa [map_commutator,map_subgroupOf_eq_of_le hZcS,map_subgroupOf_eq_of_le hIS] at hh
  have hcenter : Z d.radical c ⊓ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) ≤
      Z d.radical a :=
    (central_seed_le_incident_edge (by omega : 2 < geometry.b d.radical)
      path.start_color hcw hcw).trans (adjacent_Z_le d.radical ha haw)
  have hZa : Z d.radical c ≤ Z d.radical a := by
    rw [h.replacement_Z_eq_U_sup_fixed d geometry hb path.start_color]
    exact sup_le (hUI.trans inf_le_right) hcenter
  have hcard : Nat.card (Z d.radical c)=Nat.card (Z d.radical a) := by
    obtain ⟨y,hy,he⟩ := stabilizer_transitive_neighbors d.radical w
      (adjacent_symm d.radical hcw) (adjacent_symm d.radical haw)
    rw [←he,Z_act,card_map_of_injective (MulAut.conj y⁻¹).injective]
  let := finite_Z d.radical c
  let := finite_Z d.radical a
  have heq : Z d.radical c=Z d.radical a := eq_of_le_of_card_ge hZa hcard.ge
  apply hn
  rw [←heq,sup_idem]
  exact hES.trans (Z_normalized d.radical c)

/-- Actual first and second orbit markings transfer the entire fixed
kernel. Individual generation and actual endpoint nonnormality exclude the literal failed
comparison, without a claim about the restricted commutator's invariance. -/
theorem Input.replacement_distance_four_prescribed_individual_comparison
    {geometry : Geometry d.radical} {a z u v s : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a) (hlast : back.walk.getVert 3=path.walk.getVert 1)
    (r : FreeAmalgam d.radical) (hr : r ∈ stabilizer d.radical a)
    (hru : act d.radical r (path.walk.getVert 2)=u)
    (hCa : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2 →
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical u)
    (hyv : act d.radical y a=v)
    (hnormal : ¬ Z d.radical (path.walk.getVert 2) ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hres : Ltilde d.radical u ≤ Subgroup.SmallMover.join (U d.radical v)
      (Q d.radical v) (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2)) :
    ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
        ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ := by
  by_contra hbad
  let e := path.walk.getVert 2
  let W := U d.radical v ⊓ Q d.radical z
  let R₁ := ⁅W,X d.radical e ⊓ Q d.radical u⁆
  let R₂ := ⁅Z d.radical u,Z d.radical e⁆
  let Ce := U d.radical e ⊓ centralizer (stabilizer d.radical e : Set (FreeAmalgam d.radical))
  let Cu := U d.radical u ⊓ centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical))
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  obtain ⟨hi,hi',_⟩ := h.replacement_distance_four_comparison_failure d path hb back hus hvs hbad
  obtain ⟨hR,hcard⟩ := h.replacement_distance_four_root_comparison_of_failure d path hb back hus hvs hbad
  obtain ⟨_,hWS,_,_,_⟩ := h.replacement_distance_four_comparison_actor d path hb back hus hvs
  have hroot : (Q d.radical u).relIndex (Z d.radical e) < Nat.card F^2 := by
    rw [hi']
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  have hCeR : Ce ≤ R₂ :=
    (inf_le_inf_left _ (centralizer_le (Ltilde_le_stabilizer e))).trans
      (le_sup_right.trans (h.replacement_critical_commutator_contains_fixed_kernels d back (by omega)))
  have hCeA : Ce ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) :=
    hCeR.trans (hCa hroot)
  have hCeMap : Ce.map (MulAut.conj r⁻¹).toMonoidHom=Ce :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hCeA ((stabilizer d.radical a).inv_mem hr)))
  have hkern : Cu=Ce := by
    have hh := moving_center_kernel_act r e
    rw [hru] at hh
    exact hh.trans hCeMap
  have hRZa : R₂ ≤ Z d.radical a :=
    (h.replacement_distance_four_root_original_fixed d path hb back hmid hlast hroot).trans inf_le_left
  have hCuZa : Cu ≤ Z d.radical a := hkern.symm ▸ hCeR.trans hRZa
  have hCuMap : Cu.map (MulAut.conj y⁻¹).toMonoidHom=Cu :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp (show Cu ≤ centralizer (stabilizer d.radical u : Set _) from inf_le_right)
        ((stabilizer d.radical u).inv_mem hy)))
  have hCeZv : Ce ≤ Z d.radical v := by
    have hh := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hCuZa
    rwa [hCuMap,←Z_act,hyv,hkern] at hh
  have hn : R₁ ≠ ⊥ := by
    intro he
    have hone : Nat.card R₁=1 := card_eq_one.mpr he
    have hq : 1 < Nat.card F := Finite.one_lt_card
    change Nat.card R₁=Nat.card F at hcard
    omega
  have hsplit := h.replacement_critical_commutator_eq_intersection_join_kernel d back hb4
    hi' hi W hWS hn hR hcard
  have hR₁v : R₁ ≤ Z d.radical v :=
    ((h.replacement_distance_four_root_seed_placement_of_failure d path hb back hmid hus hvs hbad).trans
      inf_le_right).trans (U_le_Z v)
  have hR₂v : R₂ ≤ Z d.radical v := hsplit.le.trans (sup_le hR₁v hCeZv)
  have hv : color d.radical v=false := by rw [←hyv,action_preserves_color]; exact path.start_color
  exact generated_root_not_le_nonnormal_neighbor h d back hb4 hus hvs hv hi' hres hnormal hR₂v

private theorem large_point_compared
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hce : c=path.walk.getVert 2)
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a)) :
    distanceFourComparedPaths path c t := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hnormal := h.replacement_path_neighbor_join_not_normal_of_four_le d path hb4
  rw [←hce] at hnormal
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hlarge' : Nat.card F < (Q d.radical a).relIndex (Z d.radical z) := by nlinarith
  obtain ⟨g,hg,haw,huw,hindex,htransport,hgen,hfixed,hn,hbackexists⟩ :=
    h.replacement_large_movement_selected_large_at_neighbor d path hb4 hat hfirst hct hnormal hlarge' hJm
  let u := act d.radical g⁻¹ c
  let w := act d.radical g⁻¹ t
  have hres : Ltilde d.radical a ≤ Subgroup.SmallMover.join (U d.radical u)
      (Q d.radical u) (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical z := by
    rw [←htransport,hgen]
    exact Ltilde_le_stabilizer a
  have hlen : path.walk.length=4 := path.length_eq_b.trans hb
  have hend : path.walk.getVert (path.walk.length-2)=path.walk.getVert 2 := by rw [hlen]
  rw [hend] at hbackexists
  obtain ⟨back,hback,hoverlap⟩ := hbackexists
  have hmid : back.walk.getVert 2=a := by simpa using hoverlap 0 (by omega)
  have hlast : back.walk.getVert 3=path.walk.getVert 1 := by
    simpa using hoverlap 1 (by omega)
  have hbacklen : back.walk.length=4 := back.length_eq_b.trans hb
  have hnextend : back.walk.getVert (back.walk.length-2)=a := by rw [hbacklen]; exact hmid
  have hut : Adjacent d.radical u (back.walk.getVert 1) := by rwa [hback]
  have hat' : Adjacent d.radical a (back.walk.getVert 1) := by rwa [hback]
  have hun : ¬ stabilizer d.radical u ≤ normalizer
      ((Z d.radical a ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    simpa only [hmid] using h.replacement_path_neighbor_join_not_normal_of_four_le d back hb4
  have hlargeJ : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical u)
      (Q d.radical u) (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) :
        Set (FreeAmalgam d.radical))).relIndex (U d.radical u) := by
    rw [hback]
    dsimp only [u,w]
    rw [own_index_act,own_index_neighbors _ hat hct]
    exact hJm
  refine ⟨g,hg,1,(Ltilde d.radical a).one_mem,u,w,Or.inl ⟨rfl,rfl⟩,haw,huw,
    back,hback,hoverlap,?_⟩
  by_cases hsmall₂ : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2
  · obtain ⟨g₂,hg₂,hus,hvs,hidx₂,htransport₂,hgen₂,hfixed₂,hn₂,hnext₂⟩ :=
      h.replacement_large_movement_selected_root_at_neighbor d back hb4 hut rfl hat'
        hun hsmall₂ hlargeJ
    have hres₂ : Ltilde d.radical u ≤
        Subgroup.SmallMover.join (U d.radical (act d.radical g₂⁻¹ a))
          (Q d.radical (act d.radical g₂⁻¹ a))
          (Q d.radical (act d.radical g₂⁻¹ (back.walk.getVert 1))) (Nat.card F^2) ⊔
            Z d.radical (path.walk.getVert 2) := by
      rw [←htransport₂,hgen₂]
      exact Ltilde_le_stabilizer u
    have hmove₂ := individual_generation_moves_root h d back hb4 hres₂
    have hCa := first_root_centrality h d path hb back hback hmid hlast hsmall₂ hres
    have hcmp := h.replacement_distance_four_prescribed_individual_comparison d path hb back hmid hlast
      g⁻¹ ((stabilizer d.radical a).inv_mem (Ltilde_le_stabilizer a hg))
      (by rw [←hce])
      (fun hs => first_root_centrality h d path hb back hback hmid hlast hs hres)
      hus hvs g₂⁻¹ ((stabilizer d.radical u).inv_mem (Ltilde_le_stabilizer u hg₂)) rfl hn₂ hres₂
    have hnotrap₂ := second_selector_not_trapped h d path hb back hus hvs g₂⁻¹
      ((stabilizer d.radical u).inv_mem (Ltilde_le_stabilizer u hg₂)) rfl hn₂ hCa hmove₂
    have hnext₂ := exists_backward_path_of_not_le geometry (by omega) back hus hvs hnotrap₂
    rw [hnextend] at hnext₂
    exact ⟨_,_,g₂⁻¹,(Ltilde d.radical u).inv_mem hg₂,rfl,rfl,hus,hvs,hn₂,hcmp,
      hnext₂⟩
  · have hq : 1 < Nat.card F := Finite.one_lt_card
    have hlarge : Nat.card F < (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) := by
      have hh := le_of_not_gt hsmall₂
      nlinarith
    obtain ⟨g₂,hg₂,hus,hvs,hidx₂,htransport₂,hgen₂,hfixed₂,hn₂,hnext₂⟩ :=
      h.replacement_large_movement_selected_large_at_neighbor d back hb4 hut rfl hat'
        hun hlarge hlargeJ
    have hcmp : ⁅U d.radical (act d.radical g₂⁻¹ a) ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
        ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
          ⁅U d.radical (act d.radical g₂⁻¹ a) ⊓ Q d.radical z,
            X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ := by
      by_contra hbad
      have hi := (h.replacement_distance_four_comparison_failure d path hb back hus hvs hbad).2.1
      apply hsmall₂
      rw [hi]
      nlinarith
    rw [hnextend] at hnext₂
    exact ⟨_,_,g₂⁻¹,(Ltilde d.radical u).inv_mem hg₂,rfl,rfl,hus,hvs,hn₂,hcmp,
      hnext₂⟩

omit h d in
private theorem compared_of_coherent_comparison
    {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}
    {a z c t : Vertex R} {q : ℕ} (path : CriticalPath R geometry a z)
    (hh : distanceFourCoherentComparison path c t q) :
    distanceFourComparedPaths path c t := by
  obtain ⟨g,hg,x,hx,u,w,hwhich,haw,huw,back,hback,hover,v,s,y,hy,hya,hys,hus,hvs,hn,
    xgen,hxgen,hgen,hcmp,hnext⟩ := hh
  exact ⟨g,hg,x,hx,u,w,hwhich,haw,huw,back,hback,hover,v,s,y,hy,hya,hys,hus,hvs,hn,hcmp,hnext⟩

/-- A large original critical image supplies two actual prescribed backward
paths and the literal comparison, with no first-mover equality, size or
movement premise. The original neighbor is exactly the second path vertex. -/
theorem Input.replacement_distance_four_large_prescribed_comparison
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z)) :
    distanceFourComparedPaths path (path.walk.getVert 2) (path.walk.getVert 1) := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  let t := path.walk.getVert 1
  let c := path.walk.getVert 2
  have hat : Adjacent d.radical a t := by
    simpa using (cosetGraph_adj _ _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
  have hct : Adjacent d.radical c t := adjacent_symm _ ((cosetGraph_adj _ _ _).mp
    (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 1 < path.walk.length)))
  have hnormal := h.replacement_path_neighbor_join_not_normal_of_four_le d path hb4
  by_cases hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2
  · by_cases hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2)
    · exact compared_of_coherent_comparison path
        (h.replacement_distance_four_large_equal_coherent_comparison d path hb hat rfl hct
          hnormal hequal hlarge hJm)
    · exact h.replacement_distance_four_large_prescribed_unequal_comparison d path hb hlarge hequal
  · exact large_point_compared h d path hb hat rfl hct rfl hlarge (lt_of_not_ge hJm)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
