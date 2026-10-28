module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourLargeCoherentPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootPlacement
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalTerminalComparison
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourComparisonEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootCentrality
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourUnequalComparisonEscape

/-!
# The unequal comparison in the prescribed first orbit

When the actual first selector sends e=path[2] to u inside G_a, first-root
centrality identifies the complete moving fixed kernels at e and u. The
actual second selector sends a to v inside G_u and places that entire kernel
in Z_v. The failed comparison would therefore put the whole critical
commutator in Z_v, contrary to the unequal individual generation theorem.

The prescribed orbit is essential: no orbit relation with an arbitrary
initial neighbor is inferred. All central attachments are retained.
Source: MS93 (5.12)(1), printed pp.924--925.

The internal imports reuse the existing full-kernel transport, unequal
generation obstruction, and selected-path escape proofs within this package.
Their private declarations do not occur in the public contracts.
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
/-- The same two actual paths, with the literal comparison at their second
selected source. No full generating triple is asserted. -/
@[expose] def distanceFourComparedPaths {M : Type*} [Group M] {R : Subgroup M}
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (c t : Vertex R) : Prop :=
  ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
    let c₁ := act R g⁻¹ c
    let t₁ := act R g⁻¹ t
    ∃ u w, (u=c₁ ∧ w=t₁ ∨ u=act R x c₁ ∧ w=act R x t₁) ∧
      Adjacent R a w ∧ Adjacent R u w ∧
      ∃ back : CriticalPath R geometry u (path.walk.getVert 2),
        back.walk.getVert 1=w ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ∃ v s, ∃ y ∈ Ltilde R u,
          act R y a=v ∧ act R y (back.walk.getVert 1)=s ∧
          Adjacent R u s ∧ Adjacent R v s ∧
          ¬ Z R (path.walk.getVert 2) ≤ normalizer
            ((Z R v ⊔ Z R u : Subgroup (FreeAmalgam R)) : Set _) ∧
          ⁅U R v ⊓ Q R z,Z R (path.walk.getVert 2)⁆ ≤
            ⁅Z R u,Z R (path.walk.getVert 2)⁆ ⊔
              ⁅U R v ⊓ Q R z,X R (path.walk.getVert 2) ⊓ Q R u⁆ ∧
          ∃ next : CriticalPath R geometry v a,
            next.walk.getVert 1=s ∧
            ∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Actual first and second orbit markings transfer the entire fixed
kernel. Individual unequal generation then excludes the literal failed
comparison, without a claim about the restricted commutator's invariance. -/
theorem Input.replacement_distance_four_prescribed_unequal_comparison
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
    (hne : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical s) (Nat.card F^2) ≠
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u) (Q d.radical s) (Nat.card F^2))
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
  exact generated_commutator_not_le_neighbor h d back hb4 hus hvs hv hi' hne hres hR₂v

private theorem prescribed_second_unequal_paths
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a) (hlast : back.walk.getVert 3=path.walk.getVert 1)
    (r : FreeAmalgam d.radical) (hr : r ∈ stabilizer d.radical a)
    (hru : act d.radical r (path.walk.getVert 2)=u)
    (hne : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) ≠
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2))
    (hCa : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2 →
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    ∃ v s, ∃ y ∈ Ltilde d.radical u,
      act d.radical y a=v ∧ act d.radical y (back.walk.getVert 1)=s ∧
      Adjacent d.radical u s ∧ Adjacent d.radical v s ∧
      ¬ Z d.radical (path.walk.getVert 2) ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
        ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
          ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ ∧
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
  have hend : back.walk.getVert (back.walk.length-2)=a := by rw [back.length_eq_b,hb]; exact hmid
  by_cases hs : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2
  · obtain ⟨g,hg,hus,hvs,hidx,htransport,hgen,hres,hfixed,hindividual,
      hquadU,hquadV,hcube,hnot,hlarge,hn,hnext⟩ :=
      h.replacement_unequal_individual_generation_root_at_neighbor d back hb4 hut rfl hat hun hs hne
    let v := act d.radical g⁻¹ a
    let s := act d.radical g⁻¹ (back.walk.getVert 1)
    have hgu : act d.radical g⁻¹ u=u :=
      (stabilizer d.radical u).inv_mem (Ltilde_le_stabilizer u hg)
    have hne' : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical s) (Nat.card F^2) ≠
        Subgroup.SmallMover.join (U d.radical u) (Q d.radical u) (Q d.radical s) (Nat.card F^2) := by
      intro he
      have hma := mover_act (Nat.card F^2) g⁻¹ a (back.walk.getVert 1)
      have hmu := mover_act (Nat.card F^2) g⁻¹ u (back.walk.getVert 1)
      rw [hgu,inv_inv] at hmu
      rw [inv_inv] at hma
      apply hne
      apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
      exact hma.symm.trans (he.trans hmu)
    have hcmp := h.replacement_distance_four_prescribed_unequal_comparison d path hb back hmid hlast
      r hr hru hCa hus hvs g⁻¹
      ((stabilizer d.radical u).inv_mem (Ltilde_le_stabilizer u hg)) rfl hne' hres
    have hm := individual_generation_moves_root h d back hb4 hres
    have hnt := second_selector_not_trapped h d path hb back hus hvs g⁻¹
      ((stabilizer d.radical u).inv_mem (Ltilde_le_stabilizer u hg)) rfl hn (hCa hs) hm
    have hnext := exists_backward_path_of_not_le geometry (by omega) back hus hvs hnt
    rw [hend] at hnext
    exact ⟨v,s,g⁻¹,(Ltilde d.radical u).inv_mem hg,rfl,rfl,hus,hvs,hn,hcmp,hnext⟩
  · have hJm := (h.replacement_unequal_original_quadratic d geometry hb4 back.start_color hut hat hne).1.le
    obtain ⟨E,hE,f,hf,hfQ,hTf,hidx,hcore,hTP,hquad,hmax⟩ :=
      h.replacement_maximizing_parabolic d geometry hb4 back.start_color hut
    have hJP := h.replacement_small_mover_le_maximizing_plane_of_index_le d
      geometry hb4 back.start_color hut E hE f hfQ hTf hidx hmax hJm
    obtain ⟨g,hg,x,hx,hu₁,ha₁,hu₂,ha₂,hgen₁,hgen₂,hfixed,hxn,hxp,
      v,hv,s,hwhich,hus,hvs,hn,hidx',hnext⟩ :=
      h.replacement_original_smaller_large_backward_path d back hb4 hut rfl hat hun
        E hE f hf hfQ hTf hidx (le_of_not_gt hs) hJP
    have hcmp : ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
        ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
          ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ := by
      by_contra hbad
      obtain ⟨_,hi,_⟩ := h.replacement_distance_four_comparison_failure d path hb back hus hvs hbad
      apply hs
      rw [hi]
      have hq : 1 < Nat.card F := Finite.one_lt_card
      nlinarith
    rw [hend] at hnext
    rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨_,_,g⁻¹,(Ltilde d.radical u).inv_mem hg,rfl,rfl,hus,hvs,hn,hcmp,hnext⟩
    · refine ⟨_,_,g⁻¹*x,(Ltilde d.radical u).mul_mem ((Ltilde d.radical u).inv_mem hg) hx,
        ?_,?_,hus,hvs,hn,hcmp,hnext⟩ <;> rw [act_mul]

private theorem prescribed_large_unequal_compared
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hce : c=path.walk.getVert 2)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) (Nat.card F^2) ≠
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    distanceFourComparedPaths path c t := by
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
      (r : FreeAmalgam d.radical) (hr : r ∈ stabilizer d.radical a)
      (hrc : act d.radical r c=u) (hrt : act d.radical r t=w)
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
          ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
            ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
              ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ ∧
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
    have hru : act d.radical r (path.walk.getVert 2)=u := by simpa only [hce] using hrc
    have hne' : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) ≠
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) := by
      intro he
      rw [hback] at he
      have hra : act d.radical r a=a := hr
      have hmc := mover_act (Nat.card F^2) r c t
      have hma := mover_act (Nat.card F^2) r a t
      rw [hrc,hrt] at hmc
      rw [hra,hrt] at hma
      apply hne
      apply map_injective (f := (MulAut.conj r⁻¹).toMonoidHom) (MulAut.conj r⁻¹).injective
      exact hmc.symm.trans (he.symm.trans hma)
    exact ⟨back,hback,hoverlap,
      prescribed_second_unequal_paths h d path hb back hmid hlast r hr hru hne' hCa⟩
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
    refine ⟨g,hg,x,hx,v',w',Or.inr ⟨rfl,rfl⟩,haw',hvw',
      complete v' w' (g⁻¹*x) ((stabilizer d.radical a).mul_mem
        ((stabilizer d.radical a).inv_mem hgS) hxS) ?_ ?_ haw' hvw' hn₂ hO₂'⟩ <;> rw [act_mul]
  · exact ⟨g,hg,x,hx,v,w,Or.inl ⟨rfl,rfl⟩,haw,hvw,
      complete v w g⁻¹ ((stabilizer d.radical a).inv_mem hgS) rfl rfl haw hvw hn₁ hO₁'⟩

/-- A large original critical image and an unequal prescribed neighbor give
both actual backward paths and the literal second comparison. The original
neighbor is exactly path[2]; all conjugators are retained in the certificate. -/
theorem Input.replacement_distance_four_large_prescribed_unequal_comparison
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hne : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) ≠
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2)) :
    distanceFourComparedPaths path (path.walk.getVert 2) (path.walk.getVert 1) := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    simpa using (cosetGraph_adj _ _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
  have hct : Adjacent d.radical (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm _ ((cosetGraph_adj _ _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 1 < path.walk.length)))
  have hnormal := h.replacement_path_neighbor_join_not_normal_of_four_le d path hb4
  have hJm := (h.replacement_unequal_original_quadratic d geometry hb4 path.start_color hat hct hne).1.le
  exact prescribed_large_unequal_compared h d path hb hat rfl hct rfl hne hnormal hlarge hJm

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
