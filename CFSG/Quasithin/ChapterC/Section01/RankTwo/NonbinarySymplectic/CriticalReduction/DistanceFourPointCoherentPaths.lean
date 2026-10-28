module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourCoherentPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PointRootPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PointLargePaths
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourComparisonEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourUnequalRootCentrality
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourUnequalComparisonEscape

/-!
# Two actual backward paths in the full point-mover branch

The original mover's fixed index is greater than q². Its point selector
gives individual generation for the same actual first critical path. The
own-layer index is invariant across the actual edge and its conjugate, so
the backward point selector also supplies individual generation. This
forces movement of the complete critical commutator. Its entire fixed
attachment is retained in the checked second trapping contradiction.

The private imports deliberately split this branch from the shared
internal center, movement and trapping arguments. They avoid copying
those proofs or changing frozen modules; no private helper occurs in
the public statement. Source: MS93 (5.5)--(5.8), (5.12), pp.915--925.
This establishes compatible paths, not the later source comparison or
the exclusion of critical distance four.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A strict neighboring index in the full point-mover root branch gives
both genuine backward critical paths, with the original and second actual
selectors and every overlap retained. -/
theorem Input.replacement_distance_four_strict_point_root_coherent_paths
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a)) :
    distanceFourCoherentPaths path c t := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  obtain ⟨g,hg,haw,huw,hindex,htransport,hgen,hfixed,hn,hbackexists⟩ :=
    h.replacement_large_movement_root_backward_path d path hb4 hat hfirst hct hmove hsmall hJm
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
    have hnotrap₂ := second_selector_not_trapped h d path hb back hus hvs g₂⁻¹
      ((stabilizer d.radical u).inv_mem (Ltilde_le_stabilizer u hg₂)) rfl hn₂ hCa hmove₂
    have hnext₂ := exists_backward_path_of_not_le geometry (by omega) back hus hvs hnotrap₂
    rw [hnextend] at hnext₂
    exact ⟨_,_,g₂⁻¹,(Ltilde d.radical u).inv_mem hg₂,rfl,rfl,hus,hvs,hn₂,
      hnext₂⟩
  · have hq : 1 < Nat.card F := Finite.one_lt_card
    have hlarge : Nat.card F < (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) := by
      have hh := le_of_not_gt hsmall₂
      nlinarith
    obtain ⟨g₂,hg₂,hus,hvs,hidx₂,htransport₂,hgen₂,hfixed₂,hn₂,hnext₂⟩ :=
      h.replacement_large_movement_selected_large_at_neighbor d back hb4 hut rfl hat'
        hun hlarge hlargeJ
    rw [hnextend] at hnext₂
    exact ⟨_,_,g₂⁻¹,(Ltilde d.radical u).inv_mem hg₂,rfl,rfl,hus,hvs,hn₂,
      hnext₂⟩

/-- Strict movement in the critical-root branch gives compatible actual
paths without any assumption on equality or size of the original smaller
mover. The three genuine selector constructions exhaust those cases. -/
theorem Input.replacement_distance_four_strict_root_coherent_paths
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2) :
    distanceFourCoherentPaths path c t := by
  by_cases hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2
  · by_cases hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2)
    · exact h.replacement_distance_four_strict_equal_root_coherent_paths d path hb
        hat hfirst hct hmove hequal hsmall hJm
    · exact h.replacement_distance_four_strict_unequal_root_coherent_paths d path hb
        hat hfirst hct hmove hsmall hequal
  · exact h.replacement_distance_four_strict_point_root_coherent_paths d path hb
      hat hfirst hct hmove hsmall (Nat.lt_of_not_ge hJm)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
