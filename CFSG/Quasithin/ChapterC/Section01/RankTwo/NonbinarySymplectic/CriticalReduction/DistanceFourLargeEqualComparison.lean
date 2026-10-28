module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourCoherentComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedOriginalFixedSelection
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourCoherentComparison

/-!
# The same comparison paths for a large original critical image

The original-versus-selected full fixed identities hold for the actual
smaller-mover pair at every critical image size. If the original image
has size at least q², an endpoint-nonnormal member cannot be trapped.
Its full fixed identity supplies first-root centrality whenever the
backward image is a root. The common checked second selector therefore
retains its actual next path, comparison and oriented generating triple.

This internal proof split deliberately imports the frozen comparison
helpers privately. No private helper appears in a public contract. The
final result removes the original small-critical-image premise from
the equal/small-mover source branch. It does not exclude distance four.
Source: MS93 (5.6)--(5.8), (5.12)(1), pp.918--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The large original critical image yields both actual comparison paths
for the same pair of selectors, with the whole fixed attachment retained. -/
theorem Input.replacement_distance_four_large_equal_coherent_comparison
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    distanceFourCoherentComparison path c t (Nat.card F) := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic d geometry hb4 path.start_color hat
  have hJP := h.replacement_small_mover_le_maximizing_plane_of_index_le d
    geometry hb4 path.start_color hat E hE f hfQ hTf hindex hmax hJm
  obtain ⟨g,hg,x,hx,hgen,_,hfixed,hxn,hxp,hO₁,hO₂⟩ :=
    h.replacement_smaller_mover_original_fixed_selection d path hb4 hat hfirst
      E hE f hf hfQ hTf hindex hJP
  let v := act d.radical g⁻¹ c
  let w := act d.radical g⁻¹ t
  let v' := act d.radical x v
  let w' := act d.radical x w
  let J₁ := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2)
  let J₂ := Subgroup.SmallMover.join (U d.radical v') (Q d.radical v') (Q d.radical w') (Nat.card F^2)
  have hgS := Ltilde_le_stabilizer a hg
  have hxS := Ltilde_le_stabilizer a hx
  have hga : act d.radical g⁻¹ a=a := (stabilizer d.radical a).inv_mem hgS
  have hxa : act d.radical x a=a := hxS
  have haw : Adjacent d.radical a w := by
    rw [←hga]
    exact (adjacent_act_iff _ _ _ _).mpr hat
  have hvw : Adjacent d.radical v w := (adjacent_act_iff _ _ _ _).mpr hct
  have haw' : Adjacent d.radical a w' := by
    rw [←hxa]
    exact (adjacent_act_iff _ _ _ _).mpr haw
  have hvw' : Adjacent d.radical v' w' := (adjacent_act_iff _ _ _ _).mpr hvw
  have hJ₁ : J₁=J.map (MulAut.conj g).toMonoidHom := by
    simpa only [J₁,v,w,mover_act,inv_inv] using
      congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hequal
  have hJ₂ : J₂=J₁.map (MulAut.conj x⁻¹).toMonoidHom := mover_act _ x v w
  have hgen₁ : (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
      stabilizer d.radical a := by rwa [hJ₁]
  have hO₁' : (Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
      centralizer (J₁ : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    rwa [hJ₁]
  have hO₂' : (Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
      centralizer (J₂ : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    rwa [hJ₂,hJ₁]
  have hn : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hn
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hn
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,Subgroup.map_sup] at hh
    have hS : (stabilizer d.radical a).map (MulAut.conj g⁻¹).toMonoidHom=stabilizer d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical a).le_normalizer
        ((stabilizer d.radical a).inv_mem hgS))
    have hvc : act d.radical g v=c := by
      dsimp only [v]
      rw [←act_mul,inv_mul_cancel,act_one]
    have hga' : act d.radical g a=a := hgS
    rw [hS,←Z_act,←Z_act,hvc,hga'] at hh
    exact hnormal hh
  have complete (u w : Vertex d.radical) (r : FreeAmalgam d.radical)
      (hr : r ∈ stabilizer d.radical a)
      (hrc : act d.radical r c=u) (hrt : act d.radical r t=w)
      (haw : Adjacent d.radical a w) (huw : Adjacent d.radical u w)
      (hnot : ¬ Z d.radical u ≤ Q d.radical (path.walk.getVert (path.walk.length-2)))
      (hO : (Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
        Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
      ∃ back : CriticalPath d.radical geometry u (path.walk.getVert 2),
        back.walk.getVert 1=w ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ∃ v s, ∃ y ∈ Ltilde d.radical u,
          act d.radical y a=v ∧ act d.radical y (back.walk.getVert 1)=s ∧
          Adjacent d.radical u s ∧ Adjacent d.radical v s ∧
          ¬ Z d.radical (path.walk.getVert 2) ≤ normalizer
            ((Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
          ∃ x₂ ∈ Ltilde d.radical u,
          (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
              (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2)) ⊔
            (Z d.radical (path.walk.getVert 2)).map (MulAut.conj x₂).toMonoidHom =
              stabilizer d.radical u ∧
          ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
            ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
              ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ ∧
          ∃ next : CriticalPath d.radical geometry v a,
            next.walk.getVert 1=s ∧
            ∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i := by
    have hlen : path.walk.length-2=2 := by rw [path.length_eq_b,hb]
    obtain ⟨back,hback,hover⟩ :
        ∃ back : CriticalPath d.radical geometry u (path.walk.getVert 2),
          back.walk.getVert 1=w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i := by
      have hh := exists_backward_path_of_not_le geometry (by omega) path haw huw hnot
      have he : path.walk.getVert (path.walk.length-2)=path.walk.getVert 2 := congrArg _ hlen
      rw [he] at hh
      exact hh
    have hmid : back.walk.getVert 2=a := by simpa only [SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
    have hlast : back.walk.getVert 3=path.walk.getVert 1 := hover 1 (by omega)
    have hra : act d.radical r a=a := hr
    have he : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) := by
      have hh := congrArg (Subgroup.map (MulAut.conj r⁻¹).toMonoidHom) hequal
      rw [←mover_act,←mover_act,hra,hrc,hrt] at hh
      simpa only [hback] using hh.symm
    have hi : (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical u) ≤ Nat.card F^2 := by
      rw [hback,←hrc,←hrt,own_index_act,own_index_neighbors _ hat hct]
      exact hJm
    have hCa (hs : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2) :
        ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
          centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
      have hOroot := h.replacement_distance_four_root_original_fixed d path hb back hmid hlast hs
      rw [hfirst] at hOroot
      have hSroot := h.replacement_root_critical_commutator_fixed_by_first_mover d back hb4 hs
      rw [hback] at hSroot
      exact ((le_inf hOroot hSroot).trans_eq hO).trans inf_le_right
    obtain ⟨v,s,y,hy,hya,hys,hus,hvs,hn,xgen,hxgen,hgen,hcompare,hnext⟩ :=
      second_path_of_full_root_centrality h d path hb back hmid he hi hCa
    have ht : back.walk.getVert (back.walk.length-2)=a := by
      rw [back.length_eq_b,hb]
      exact hmid
    rw [ht] at hnext
    exact ⟨back,hback,hover,v,s,y,hy,hya,hys,hus,hvs,hn,xgen,hxgen,hgen,hcompare,hnext⟩
  have hnotrap (u w : Vertex d.radical)
      (haw : Adjacent d.radical a w) (huw : Adjacent d.radical u w)
      (hn : ¬ Z d.radical z ≤ normalizer
        ((Z d.radical u ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
      ¬ Z d.radical u ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
    intro hk
    have hYV : Z d.radical u ≤ V d.radical a :=
      le_sup_left.trans (neighbor_seed_join_le_radius haw huw)
    have hYS : Z d.radical u ≤ stabilizer d.radical z :=
      (le_inf hYV hk).trans (truncated_radius_le_endpoint_stabilizer path (by omega))
    have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
    obtain ⟨_,hi⟩ := h.replacement_critical_indices_eq_field_of_seed_escape d path
      (by omega) (Z d.radical u) hYS hYQ hn
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  by_cases hn₁ : Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)
  · have hn₂ : ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v' ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      intro hn₂
      have hb' := paired_endpoint_normalizes_first_join x hxS hn₂
      apply hn
      rw [←hgen₁]
      refine sup_le (sup_le ((Subgroup.SmallMover.join_le _ _ _ _).trans
        (edge_normalizes_neighbor_seed_join haw hvw)) hn₁) ?_
      simpa only [Z_act,inv_inv] using hb'
    refine ⟨g,hg,x,hx,v',w',Or.inr ⟨rfl,rfl⟩,haw',hvw',?_⟩
    exact complete v' w' (g⁻¹*x)
      ((stabilizer d.radical a).mul_mem ((stabilizer d.radical a).inv_mem hgS) hxS)
      (by rw [act_mul]) (by rw [act_mul]) haw' hvw'
      (hnotrap v' w' haw' hvw' hn₂) hO₂'
  · exact ⟨g,hg,x,hx,v,w,Or.inl ⟨rfl,rfl⟩,haw,hvw,
      complete v w g⁻¹ ((stabilizer d.radical a).inv_mem hgS) rfl rfl haw hvw
        (hnotrap v w haw hvw hn₁) hO₁'⟩

/-- The actual equal/small-mover branch gives coherent comparison paths or
an explicit strict unequal neighbor, at every original critical image size. -/
theorem Input.replacement_distance_four_equal_coherent_comparison_or_strict_unequal_neighbor
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    (∃ c', Adjacent d.radical c' t ∧
      Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c') ∧
      Subgroup.SmallMover.join (U d.radical c') (Q d.radical c')
          (Q d.radical t) (Nat.card F^2) ≠
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical t) (Nat.card F^2)) ∨
    (∃ c', Adjacent d.radical c' t ∧
      Subgroup.SmallMover.join (U d.radical c') (Q d.radical c')
          (Q d.radical t) (Nat.card F^2) =
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical t) (Nat.card F^2) ∧
      distanceFourCoherentComparison path c' t (Nat.card F)) := by
  by_cases hs : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2
  · exact h.replacement_distance_four_coherent_comparison_or_strict_unequal_neighbor d
      path hb hat hfirst hct hnormal hequal hs hJm
  · exact Or.inr ⟨c,hct,hequal,
      h.replacement_distance_four_large_equal_coherent_comparison d path hb hat hfirst hct
        hnormal hequal (le_of_not_gt hs) hJm⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
