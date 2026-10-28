module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootPath
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedEndpointAlignment
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IndividualSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NonplaneIndividualSelection
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EqualRootCommutator

/-!
# The full omega layers at distance four

The actual root critical path can be transported to every M-vertex. Its
full omega layer is therefore the source seed everywhere, and the existing
whole-seed splitting retains the entire vertex-fixed attachment. This
excludes the nonsplitting exception in the actual unequal selector, using
one marking and one selector in each original critical-image branch.

No equality of moving fixed kernels at different vertices, and no
unrestricted distance-four comparison, is asserted.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- At distance four the full omega center is the source seed at every
M-vertex; the actual root path is produced internally. -/
theorem Input.replacement_distance_four_X_eq_Z
    (geometry : Geometry d.radical) (hb : geometry.b d.radical=4)
    {v : Vertex d.radical} (hv : color d.radical v=false) :
    X d.radical v=Z d.radical v := by
  obtain ⟨u,e,path,_,hi⟩ := h.replacement_distance_four_exists_root_critical_path d geometry hb
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical path.start_color
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical hv
  let y := g⁻¹*j
  have hy : act d.radical y u=v := by
    rw [hg,act_mVertex]
    dsimp only [y]
    rw [mul_inv_cancel_left,←hj]
  let moved := path.act y
  have hadj : Adjacent d.radical (act d.radical y u) (moved.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (moved.walk.adj_getVert_succ (by rw [moved.length_eq_b]; omega : 0 < moved.walk.length))
  have hsmall : (Q d.radical (act d.radical y u)).relIndex (Z d.radical (act d.radical y e)) <
      Nat.card F^2 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective,hi]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  have hh := h.replacement_root_X_eq_Z d moved (by omega) hadj hsmall
  simpa only [hy] using hh

/-- The global full-X splitting keeps the entire ambient-fixed subgroup. -/
theorem Input.replacement_distance_four_X_split
    (geometry : Geometry d.radical) (hb : geometry.b d.radical=4)
    {v : Vertex d.radical} (hv : color d.radical v=false) :
    X d.radical v=U d.radical v ⊔
      (X d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))) := by
  rw [h.replacement_distance_four_X_eq_Z d geometry hb hv]
  exact h.replacement_Z_eq_U_sup_fixed d geometry (by omega) hv

/-- Every actual unequal neighboring pair has one residual selector with
individual generation, joined generation and whole-edge fixedness at
b=4. No critical-image or coordinate-containment premise is imposed. -/
theorem Input.replacement_distance_four_unequal_individual_generation_selector
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    let Jc := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)
    ∃ g ∈ Ltilde d.radical a,
      Ltilde d.radical a ≤ Jc.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z ∧
      (J ⊔ Jc).map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical a ∧
      Z d.radical t ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  by_cases hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2
  · exact h.replacement_unequal_root_individual_generation_selector
      d path hb4 hat hfirst hct hsmall hne
  have hlarge := le_of_not_gt hsmall
  obtain ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_generation_alternative_with_edge_original_fixed_normalized
      d path hb4 hat hct hne hlarge
  by_cases hcontained : ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
      (CentralRootGeometry.wing true).map unipotent.subtype
  · obtain ⟨u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hfixed,hAP,hedge,hD⟩ := hall hcontained
    have hindividual : pResidual 2 (stabilizer d.radical a) ≤
        (Z d.radical z).subgroupOf (stabilizer d.radical a) ⊔
          (Subgroup.SmallMover.join (U d.radical (act d.radical v.val⁻¹ c))
            (Q d.radical (act d.radical v.val⁻¹ c)) (Q d.radical (act d.radical v.val⁻¹ t))
            (Nat.card F^2)).subgroupOf (stabilizer d.radical a) := by
      rcases hD with hi | ⟨_,_,_,_,hns,_⟩
      · exact hi
      · exact (hns (h.replacement_distance_four_X_split d geometry hb path.start_color)).elim
    let S := stabilizer d.radical a
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    let Jc := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)
    let E := Subgroup.SmallMover.join (U d.radical (act d.radical v.val⁻¹ c))
      (Q d.radical (act d.radical v.val⁻¹ c)) (Q d.radical (act d.radical v.val⁻¹ t))
        (Nat.card F^2)
    have hES : E ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
      (fun _ hx => hx.2 a (adjacent_symm _ hat₁))
    have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
    have hEc : E=Jc.map (MulAut.conj v.val).toMonoidHom := by
      dsimp only [E,Jc]
      rw [U_act,Q_act,Q_act,inv_inv,
        Subgroup.SmallMover.join_map (MulAut.conj v.val).toMonoidHom (MulAut.conj v.val).injective]
    have hres : Ltilde d.radical a ≤ Jc.map (MulAut.conj v.val).toMonoidHom ⊔ Z d.radical z := by
      have hh := map_mono (f := S.subtype) hindividual
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hzS,map_subgroupOf_eq_of_le hES] at hh
      change Ltilde d.radical a ≤ Z d.radical z ⊔ E at hh
      rw [hEc,sup_comm] at hh
      exact hh
    have hJplane := h.replacement_contained_endpoint_aligns_mover d path hb4 hat hfirst hct hne
      B hB f hfQ hTf hindex hlarge hcontained
    have hwhole : Ltilde d.radical a ⊔ Q d.radical a=S := by
      obtain ⟨i,hinj,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel
        d.radical (h.replacement_two_group d) (h.replacement_core_le d) path.start_color
      rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
        h.replacement_inner_of_four_le d geometry hb4,←MonoidHom.range_eq_map,hir]
    have hQmap : (Q d.radical a).map (MulAut.conj v.val).toMonoidHom=Q d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a v.property)
    have hQJ : Q d.radical a ≤ J.map (MulAut.conj v.val).toMonoidHom := by
      have hh := map_mono (f := (MulAut.conj v.val).toMonoidHom)
        (core_le_mover h d path.start_color hat)
      rwa [hQmap] at hh
    have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm _ hat)
    have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
    have hJcS : Jc ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
    have hSmap : S.map (MulAut.conj v.val).toMonoidHom=S :=
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer v.property)
    have hgen : (J ⊔ Jc).map (MulAut.conj v.val).toMonoidHom ⊔ Z d.radical z=S := by
      rw [Subgroup.map_sup]
      apply le_antisymm
      · exact sup_le (sup_le ((map_mono hJS).trans_eq hSmap)
          ((map_mono hJcS).trans_eq hSmap)) hzS
      · rw [←hwhole]
        exact sup_le (hres.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
          (hQJ.trans (le_sup_left.trans le_sup_left))
    exact ⟨v.val,hv,hres,hgen,(hedge hJplane).2⟩
  · obtain ⟨g,hg,hres,_,hgen,hfixed⟩ :=
      h.replacement_unequal_nonplane_individual_selector d path hb4 hat hfirst hct hne
        B hB f hf hfQ hTf hTn hindex hcontained
    exact ⟨g,hg,hres,hgen,hfixed⟩


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
