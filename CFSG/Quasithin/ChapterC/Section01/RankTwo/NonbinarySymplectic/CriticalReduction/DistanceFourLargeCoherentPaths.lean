module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootCoherentPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedOriginalFixedSelection
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourComparisonEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootCentrality
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourUnequalRootCentrality
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourUnequalComparisonEscape

/-!
# Coherent backward paths at distance four for every critical image

For a large original image, use the literal second path vertex. The original
smaller-mover pair retains its full fixed identities without identifying
neighboring movers. Full neighboring-mover fixedness transfers the backward
root to the selected original mover, so the same pair fixes the entire root
at the original vertex. The second actual selector then cannot be trapped.
The full point-mover branch uses its own individual generation instead.

Together with the root-image construction this supplies two compatible
backward critical paths at distance four without any image, mover-size,
movement, or equality premise. Private imports deliberately reuse the
internal full-attachment center, movement and trapping arguments. No private
helper occurs in a public statement. This proves path existence, not the
later comparison or exclusion of distance four. Source: MS93 (5.8),(5.12).
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
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem second_path_all_movers
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hCa : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2 →
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    ∃ v s, ∃ y ∈ Ltilde d.radical u,
      act d.radical y a=v ∧ act d.radical y (back.walk.getVert 1)=s ∧
      Adjacent d.radical u s ∧ Adjacent d.radical v s ∧
      ¬ Z d.radical (path.walk.getVert 2) ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ∃ next : CriticalPath d.radical geometry v a,
        next.walk.getVert 1=s ∧
        ∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hut : Adjacent d.radical u (back.walk.getVert 1) := by
    simpa using (cosetGraph_adj _ _ _).mp
      (back.walk.adj_getVert_succ (by rw [back.length_eq_b]; omega : 0 < back.walk.length))
  have hat : Adjacent d.radical a (back.walk.getVert 1) := by
    simpa only [hmid] using adjacent_symm d.radical ((cosetGraph_adj _ _ _).mp
      (back.walk.adj_getVert_succ (by rw [back.length_eq_b]; omega : 1 < back.walk.length)))
  have hun : ¬ stabilizer d.radical u ≤ normalizer
      ((Z d.radical a ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    simpa only [hmid] using h.replacement_path_neighbor_join_not_normal_of_four_le d back hb4
  have hend : back.walk.getVert (back.walk.length-2)=a := by
    rw [back.length_eq_b,hb]
    exact hmid
  have residual_selector (g x : FreeAmalgam d.radical)
      (hg : g ∈ Ltilde d.radical u) (hx : x ∈ Ltilde d.radical u)
      (v s : Vertex d.radical)
      (hs : (v=act d.radical g⁻¹ a ∧ s=act d.radical g⁻¹ (back.walk.getVert 1)) ∨
        (v=act d.radical x (act d.radical g⁻¹ a) ∧
          s=act d.radical x (act d.radical g⁻¹ (back.walk.getVert 1)))) :
      ∃ y ∈ Ltilde d.radical u,
        act d.radical y a=v ∧ act d.radical y (back.walk.getVert 1)=s := by
    rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨g⁻¹,(Ltilde d.radical u).inv_mem hg,rfl,rfl⟩
    · refine ⟨g⁻¹*x,(Ltilde d.radical u).mul_mem ((Ltilde d.radical u).inv_mem hg) hx,?_,?_⟩ <;>
        rw [act_mul]
  by_cases hs : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2
  · have finish (g x : FreeAmalgam d.radical) (hg : g ∈ Ltilde d.radical u)
        (hx : x ∈ Ltilde d.radical u) (v s : Vertex d.radical)
        (hwhich : (v=act d.radical g⁻¹ a ∧ s=act d.radical g⁻¹ (back.walk.getVert 1)) ∨
          (v=act d.radical x (act d.radical g⁻¹ a) ∧
            s=act d.radical x (act d.radical g⁻¹ (back.walk.getVert 1))))
        (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
        (hn : ¬ Z d.radical (path.walk.getVert 2) ≤ normalizer
          ((Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _))
        (hm : ¬ ⁅Z d.radical (path.walk.getVert 2),U d.radical u⁆ ≤ centralizer
          (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
            (Q d.radical s) (Nat.card F^2) : Set (FreeAmalgam d.radical))) :
        ∃ v s, ∃ y ∈ Ltilde d.radical u,
          act d.radical y a=v ∧ act d.radical y (back.walk.getVert 1)=s ∧
          Adjacent d.radical u s ∧ Adjacent d.radical v s ∧
          ¬ Z d.radical (path.walk.getVert 2) ≤ normalizer
            ((Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
          ∃ next : CriticalPath d.radical geometry v a,
            next.walk.getVert 1=s ∧
            ∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i := by
      obtain ⟨y,hy,hya,hys⟩ := residual_selector g x hg hx v s hwhich
      have hntrap := second_selector_not_trapped h d path hb back hus hvs y
        (Ltilde_le_stabilizer u hy) hya hn (hCa hs) hm
      have hnext := exists_backward_path_of_not_le geometry (by omega) back hus hvs hntrap
      rw [hend] at hnext
      exact ⟨v,s,y,hy,hya,hys,hus,hvs,hn,hnext⟩
    by_cases hJm : (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical u) ≤ Nat.card F^2
    · by_cases he : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) =
        Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical (back.walk.getVert 1)) (Nat.card F^2)
      · obtain ⟨E,hE,f,hf,hfQ,hTf,hidx,g,hg,x,hx,hu₁,ha₁,hu₂,ha₂,
          hgen₁,hgen₂,hfixed,hm₁,hm₂,hxn,hxp,v,hv,s,hwhich,hus,hvs,hn,hnext⟩ :=
          h.replacement_equal_small_index_selected_root_alternative d back hb4 hut rfl hat hun he hs hJm
        have hm : ¬ ⁅Z d.radical (path.walk.getVert 2),U d.radical u⁆ ≤ centralizer
            (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
              (Q d.radical s) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
          rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact hm₁
          · exact hm₂
        exact finish g x hg hx v s hwhich hus hvs hn hm
      · obtain ⟨g,hg,hus,hvs,hidx,htransport,hgen,hres,hfixed,hindividual,
          hquadU,hquadV,hcube,hnot,hlarge,hn,hnext⟩ :=
          h.replacement_unequal_individual_generation_root_at_neighbor d back hb4 hut rfl hat hun hs he
        exact finish g 1 hg (Ltilde d.radical u).one_mem _ _ (Or.inl ⟨rfl,rfl⟩)
          hus hvs hn (individual_generation_moves_root h d back hb4 hres)
    · obtain ⟨g,hg,hus,hvs,hidx,htransport,hgen,hfixed,hn,hnext⟩ :=
        h.replacement_large_movement_selected_root_at_neighbor d back hb4 hut rfl hat hun hs (lt_of_not_ge hJm)
      have hres : Ltilde d.radical u ≤
          Subgroup.SmallMover.join (U d.radical (act d.radical g⁻¹ a))
            (Q d.radical (act d.radical g⁻¹ a))
            (Q d.radical (act d.radical g⁻¹ (back.walk.getVert 1))) (Nat.card F^2) ⊔
              Z d.radical (path.walk.getVert 2) := by
        rw [←htransport,hgen]
        exact Ltilde_le_stabilizer u
      exact finish g 1 hg (Ltilde d.radical u).one_mem _ _ (Or.inl ⟨rfl,rfl⟩)
        hus hvs hn (individual_generation_moves_root h d back hb4 hres)
  · by_cases hJm : (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical u) ≤ Nat.card F^2
    · obtain ⟨E,hE,f,hf,hfQ,hTf,hidx,hcore,hTP,hquad,hmax⟩ :=
        h.replacement_maximizing_parabolic d geometry hb4 back.start_color hut
      have hJP := h.replacement_small_mover_le_maximizing_plane_of_index_le d
        geometry hb4 back.start_color hut E hE f hfQ hTf hidx hmax hJm
      obtain ⟨g,hg,x,hx,hu₁,ha₁,hu₂,ha₂,hgen₁,hgen₂,hfixed,hxn,hxp,
        v,hv,s,hwhich,hus,hvs,hn,hidx',hnext⟩ :=
        h.replacement_original_smaller_large_backward_path d back hb4 hut rfl hat hun
          E hE f hf hfQ hTf hidx (le_of_not_gt hs) hJP
      obtain ⟨y,hy,hya,hys⟩ := residual_selector g x hg hx v s hwhich
      rw [hend] at hnext
      exact ⟨v,s,y,hy,hya,hys,hus,hvs,hn,hnext⟩
    · have hq : 1 < Nat.card F := Finite.one_lt_card
      have hl : Nat.card F < (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) := by
        have hh := le_of_not_gt hs
        nlinarith
      obtain ⟨g,hg,hus,hvs,hidx,htransport,hgen,hfixed,hn,hnext⟩ :=
        h.replacement_large_movement_selected_large_at_neighbor d back hb4 hut rfl hat hun hl (lt_of_not_ge hJm)
      rw [hend] at hnext
      exact ⟨_,_,g⁻¹,(Ltilde d.radical u).inv_mem hg,rfl,rfl,hus,hvs,hn,hnext⟩

private theorem large_smaller_coherent
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    distanceFourCoherentPaths path c t := by
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
  let J₁ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical w) (Nat.card F^2)
  let J₂ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical w') (Nat.card F^2)
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
    simpa only [hga,inv_inv] using mover_act (Nat.card F^2) g⁻¹ a t
  have hJ₂ : J₂=J₁.map (MulAut.conj x⁻¹).toMonoidHom := by
    simpa only [hxa] using mover_act (Nat.card F^2) x a w
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
  have complete (u w : Vertex d.radical)
      (haw : Adjacent d.radical a w) (huw : Adjacent d.radical u w)
      (hn : ¬ Z d.radical z ≤ normalizer
        ((Z d.radical u ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
      (hO : (Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
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
          ∃ next : CriticalPath d.radical geometry v a,
            next.walk.getVert 1=s ∧
            ∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i := by
    have hnotrap : ¬ Z d.radical u ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
      intro hk
      have hYV : Z d.radical u ≤ V d.radical a :=
        le_sup_left.trans (neighbor_seed_join_le_radius haw huw)
      have hYS : Z d.radical u ≤ stabilizer d.radical z :=
        (le_inf hYV hk).trans (CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.truncated_radius_le_endpoint_stabilizer path (by omega))
      have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
      obtain ⟨_,hi⟩ := h.replacement_critical_indices_eq_field_of_seed_escape d path
        (by omega) (Z d.radical u) hYS hYQ hn
      have hq : 1 < Nat.card F := Finite.one_lt_card
      nlinarith
    have hbackexists := exists_backward_path_of_not_le geometry (by omega) path haw huw hnotrap
    have hlen : path.walk.length=4 := path.length_eq_b.trans hb
    have hend : path.walk.getVert (path.walk.length-2)=path.walk.getVert 2 := by rw [hlen]
    rw [hend] at hbackexists
    obtain ⟨back,hback,hoverlap⟩ := hbackexists
    have hmid : back.walk.getVert 2=a := by simpa using hoverlap 0 (by omega)
    have hlast : back.walk.getVert 3=path.walk.getVert 1 := by simpa using hoverlap 1 (by omega)
    have hCa (hs : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2) :
        ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
          centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
      have hOroot := h.replacement_distance_four_root_original_fixed d path hb back hmid hlast hs
      rw [hfirst] at hOroot
      have hSroot := h.replacement_root_critical_commutator_fixed_by_first_mover d back hb4 hs
      rw [hback] at hSroot
      have htrans := (le_inf (hOroot.trans inf_le_left) hSroot).trans
        (neighbor_full_fixed_le_original h d geometry hb4 path.start_color haw huw)
      exact ((le_inf hOroot htrans).trans_eq hO).trans inf_le_right
    exact ⟨back,hback,hoverlap,second_path_all_movers h d path hb back hmid hCa⟩
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
    exact ⟨g,hg,x,hx,v',w',Or.inr ⟨rfl,rfl⟩,haw',hvw',complete v' w' haw' hvw' hn₂ hO₂'⟩
  · exact ⟨g,hg,x,hx,v,w,Or.inl ⟨rfl,rfl⟩,haw,hvw,complete v w haw hvw hn₁ hO₁'⟩

/-- A large original critical image supplies coherent backward paths from
the literal second path vertex, for every original mover size and every
relation between neighboring movers. -/
theorem Input.replacement_distance_four_large_coherent_paths
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z)) :
    distanceFourCoherentPaths path (path.walk.getVert 2) (path.walk.getVert 1) := by
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
  · exact large_smaller_coherent h d path hb hat rfl hct hnormal hlarge hJm
  · have hq : 1 < Nat.card F := Finite.one_lt_card
    have hl : Nat.card F < (Q d.radical a).relIndex (Z d.radical z) := by nlinarith
    obtain ⟨g,hg,haw,huw,hidx,htransport,hgen,hfixed,hn,hbackexists⟩ :=
      h.replacement_large_movement_selected_large_at_neighbor d path hb4 hat rfl hct
        hnormal hl (lt_of_not_ge hJm)
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
    have hlast : back.walk.getVert 3=path.walk.getVert 1 := by simpa using hoverlap 1 (by omega)
    have hCa := fun hs => first_root_centrality h d path hb back hback hmid hlast hs hres
    exact ⟨g,hg,1,(Ltilde d.radical a).one_mem,u,w,Or.inl ⟨rfl,rfl⟩,haw,huw,
      back,hback,hoverlap,second_path_all_movers h d path hb back hmid hCa⟩

/-- Every actual distance-four critical path has two coherent backward
critical paths, with no critical-image, movement, mover-size or equality
premise. The selected original neighbor and both actual markings remain
part of the certificate. -/
theorem Input.replacement_distance_four_coherent_paths
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4) :
    ∃ c, Adjacent d.radical c (path.walk.getVert 1) ∧
      distanceFourCoherentPaths path c (path.walk.getVert 1) := by
  by_cases hs : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2
  · have hat : Adjacent d.radical a (path.walk.getVert 1) := by
      simpa using (cosetGraph_adj _ _ _).mp
        (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
    exact h.replacement_distance_four_root_coherent_paths d path hb hat rfl hs
  · refine ⟨path.walk.getVert 2,?_,h.replacement_distance_four_large_coherent_paths d path hb (le_of_not_gt hs)⟩
    exact adjacent_symm _ ((cosetGraph_adj _ _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 1 < path.walk.length)))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
