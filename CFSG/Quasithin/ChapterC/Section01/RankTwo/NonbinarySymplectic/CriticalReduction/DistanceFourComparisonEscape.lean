module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootCentrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallerLargePaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNeighbor
public import Theory.GroupTheory.NormalizedSupCard

/-!
# A genuine second backward critical path at distance four

Retain the same first equal-root selector at an arbitrary initial neighbor.
For a compatible backward path, choose the second selector in the residual
orbit of the original midpoint. A trapped member has a displacement D of
order q. It is disjoint from the entire moving fixed kernel C at the second
source, because their intersection would be fixed at the selected vertex.
The full critical commutator is D joined with C, by its exact order including
that kernel. The selected mover fixes both factors, contradicting the actual
movement clause of this same selector. Thus the selected member is not trapped.

The large-image second case already supplies its backward critical path.
The small-image premise occurs only in intermediate producers and is split
internally here. All fixed attachments and original path overlaps are retained.
Source: MS93 (5.12), printed p.925, the transition after (1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource

private theorem mover_act {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) (y : FreeAmalgam R) (v t : Vertex R) :
    Subgroup.SmallMover.join (U R (act R y v)) (Q R (act R y v))
        (Q R (act R y t)) q =
      (Subgroup.SmallMover.join (U R v) (Q R v) (Q R t) q).map
        (MulAut.conj y⁻¹).toMonoidHom := by
  rw [U_act,Q_act,Q_act,←Subgroup.SmallMover.join_map _ (MulAut.conj y⁻¹).injective]

private theorem own_index_act {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) (y : FreeAmalgam R) (v t : Vertex R) :
    (centralizer (Subgroup.SmallMover.join (U R (act R y v)) (Q R (act R y v))
      (Q R (act R y t)) q : Set (FreeAmalgam R))).relIndex (U R (act R y v)) =
      (centralizer (Subgroup.SmallMover.join (U R v) (Q R v)
        (Q R t) q : Set (FreeAmalgam R))).relIndex (U R v) := by
  rw [mover_act,U_act,Subgroup.SmallMover.centralizer_index_map _ (MulAut.conj y⁻¹).injective]

private theorem own_index_neighbors {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) {a t c : Vertex R} (hat : Adjacent R a t) (hct : Adjacent R c t) :
    (centralizer (Subgroup.SmallMover.join (U R c) (Q R c)
      (Q R t) q : Set (FreeAmalgam R))).relIndex (U R c) =
      (centralizer (Subgroup.SmallMover.join (U R a) (Q R a)
        (Q R t) q : Set (FreeAmalgam R))).relIndex (U R a) := by
  obtain ⟨y,hy,hya⟩ := stabilizer_transitive_neighbors R t
    (adjacent_symm R hat) (adjacent_symm R hct)
  have hyt : act R y t=t := hy
  simpa only [hya,hyt] using own_index_act q y a t

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem second_selector_not_trapped
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical u)
    (hya : act d.radical y a=v)
    (hn : ¬ Z d.radical (path.walk.getVert 2) ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hCa : ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (hmove : ¬ ⁅Z d.radical (path.walk.getVert 2),U d.radical u⁆ ≤ centralizer
      (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))) :
    ¬ Z d.radical v ≤ Q d.radical (back.walk.getVert (back.walk.length-2)) := by
  intro htrap
  let e := path.walk.getVert 2
  let A := X d.radical e ⊓ Q d.radical u
  let D := ⁅Z d.radical v,A⁆
  let T := ⁅Z d.radical u,Z d.radical e⁆
  let C := U d.radical u ⊓ centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical))
  let J := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
    (Q d.radical t) (Nat.card F^2)
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hv : color d.radical v=false := by rw [←hya,action_preserves_color]; exact path.start_color
  obtain ⟨hDU,hDcard,hDUindex,hDZindex,hDsource,_⟩ :=
    h.replacement_trapped_root_exact_indices d back hb4 hut hvt hn htrap
  change D=⁅U d.radical v,A⁆ at hDU
  change Nat.card D=Nat.card F at hDcard
  have hAS : A ≤ stabilizer d.radical v := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two u v back.start_color hv
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hut hvt))
  have hDZ : D ≤ Z d.radical v :=
    le_normalizer_iff_commutator_le_left.mp (hAS.trans (Z_normalized d.radical v))
  have hDT : D ≤ T := by
    change ⁅Z d.radical v,X d.radical e ⊓ Q d.radical u⁆ ≤ T
    rw [hDsource]
    have hh := h.replacement_trapped_root_commutator_le_critical d back hb4 hut hvt hn htrap
    exact hh.trans (commutator_mono le_rfl (U_le_Z e))
  let Cv := stabilizer d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))
  let := finite_Z d.radical v
  let : Finite D := Finite.of_injective (inclusion hDZ) (inclusion_injective _)
  have hDidx : Cv.relIndex D=Nat.card D := by
    have hh := h.replacement_displacement_central_index d geometry hb4 hv A hAS
    rw [commutator_comm] at hh
    exact hh.trans (hDZindex.trans hDcard.symm)
  have hdisv : Disjoint D Cv := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) (D ⊓ Cv) D
      bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hDidx] at hm
    apply disjoint_iff.mpr
    apply card_eq_one.mp
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := D))
    simpa only [one_mul] using hm
  have hIcent : D ⊓ C ≤ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical)) := by
    let I := D ⊓ C
    have hIa : I ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) :=
      (inf_le_left.trans hDT).trans hCa
    have hIu : I ≤ centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical)) :=
      inf_le_right.trans inf_le_right
    have hIg : I.map (MulAut.conj y⁻¹).toMonoidHom=I :=
      mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
        (le_centralizer_iff.mp hIu ((stabilizer d.radical u).inv_mem hy)))
    have hh := (map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hIa).trans
      (map_centralizer_le_centralizer_image _ _)
    change I.map (MulAut.conj y⁻¹).toMonoidHom ≤ centralizer
      ((stabilizer d.radical a).map (MulAut.conj y⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh
    rwa [hIg,←stabilizer_act,hya] at hh
  have hdis : Disjoint D C := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    exact (le_inf inf_le_left (le_inf
      (inf_le_left.trans (hDZ.trans (Z_le_stabilizer d.radical v))) hIcent)).trans hdisv.le_bot
  have hCT : C ≤ T :=
    (inf_le_inf_left _ (centralizer_le (Ltilde_le_stabilizer u))).trans
      (le_sup_left.trans (h.replacement_critical_commutator_contains_fixed_kernels d back (by omega)))
  have hTZ : T ≤ Z d.radical u := critical_commutator_le_start_seed back
  let := finite_Z d.radical u
  let : Finite T := Finite.of_injective (inclusion hTZ) (inclusion_injective _)
  have hroot : (Q d.radical e).relIndex (Z d.radical u)=Nat.card F := by
    have hYS : Z d.radical v ≤ stabilizer d.radical e :=
      (le_inf (le_sup_left.trans (neighbor_seed_join_le_radius hut hvt)) htrap).trans
        (truncated_radius_le_endpoint_stabilizer back (by omega))
    exact (h.replacement_critical_indices_eq_field_of_seed_escape d back (by omega)
      (Z d.radical v) hYS
      ((le_sup_left.trans (neighbor_seed_join_le_radius hut hvt)).trans
        (geometry.V_le_Q (by omega) u back.start_color)) hn).1
  have hTcard : Nat.card T=Nat.card F*Nat.card C := by
    have hh := h.replacement_critical_commutator_card d back hb4
    rwa [hroot] at hh
  have hCD : C ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le (hDT.trans (hTZ.trans (Z_le_stabilizer d.radical u))))
  have hsplit : D ⊔ C=T := eq_of_le_of_card_ge (sup_le hDT hCT) (by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint D C
      (hCD.trans (Subgroup.centralizer_le_normalizer _)) hdis,hDcard,hTcard])
  have ht : color d.radical t=true := by
    have hh := adjacent_color_ne d.radical hut
    rw [back.start_color] at hh
    cases hcol : color d.radical t <;> simp_all
  have hAT : A ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht hut)
  have hDJ : D ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    rw [hDU]
    exact h.replacement_small_mover_join_centralizes_field_displacement d geometry hb4
      hv hvt A hAT hDUindex.le
  have hJS : J ≤ stabilizer d.radical u := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 u (adjacent_symm _ hut))
  have hTJ : T ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    rw [←hsplit]
    exact sup_le hDJ (inf_le_right.trans (centralizer_le hJS))
  apply hmove
  have hwhole := h.replacement_Z_commutator_eq_U d geometry hb4 back.start_color
    (Z d.radical e) (back.endpoint_Z_le_start_stabilizer (by omega))
  rw [commutator_comm,←hwhole]
  exact hTJ

/-- The same first equal-root selector admits an actual second backward
critical path for every compatible first backward path. The chosen second
member is in the residual orbit of the original midpoint, and every literal
path overlap is retained. No small second image or trapping premise remains. -/
theorem Input.replacement_distance_four_equal_root_second_backward_path
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
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let t₁ := act d.radical g⁻¹ t
      let c₁ := act d.radical g⁻¹ c
      let t₂ := act d.radical x t₁
      let c₂ := act d.radical x c₁
      ∃ u ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
        (u=c₁ ∧ w=t₁ ∨ u=c₂ ∧ w=t₂) ∧
        Adjacent d.radical a w ∧ Adjacent d.radical u w ∧
        ¬ Z d.radical z ≤ normalizer
          ((Z d.radical u ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ((∃ back : CriticalPath d.radical geometry u (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∨
        (Z d.radical u ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
          Nat.card F ≤ (centralizer (Z d.radical u : Set (FreeAmalgam d.radical))).relIndex
            (Z d.radical z ⊓ Q d.radical a) ∧
          X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical u : Set _) ∧
          ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical u⁆,Z d.radical u⁆=⊥)) ∧
        (∀ (back : CriticalPath d.radical geometry u (path.walk.getVert 2)),
          back.walk.getVert 1=w → back.walk.getVert 2=a →
          back.walk.getVert 3=path.walk.getVert 1 →
          ∃ v s, ∃ y ∈ Ltilde d.radical u,
            act d.radical y a=v ∧ act d.radical y (back.walk.getVert 1)=s ∧
            Adjacent d.radical u s ∧ Adjacent d.radical v s ∧
            ¬ Z d.radical (path.walk.getVert 2) ≤ normalizer
              ((Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
            ∃ next : CriticalPath d.radical geometry v (back.walk.getVert (back.walk.length-2)),
              next.walk.getVert 1=s ∧
              ∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i) := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  obtain ⟨g,hg,x,hx,u,hu,w,hwhich,haw,huw,hn,hnext,hCa⟩ :=
    h.replacement_distance_four_first_selector_root_centrality d path hb hat hfirst hct
      hnormal hequal hsmall hJm
  have hcindex : (centralizer (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical c) ≤ Nat.card F^2 := by
    rw [own_index_neighbors _ hat hct]
    exact hJm
  have selected (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical a) :
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (act d.radical y t)) (Nat.card F^2) =
        Subgroup.SmallMover.join (U d.radical (act d.radical y c))
          (Q d.radical (act d.radical y c)) (Q d.radical (act d.radical y t)) (Nat.card F^2) ∧
      (centralizer (Subgroup.SmallMover.join (U d.radical (act d.radical y c))
        (Q d.radical (act d.radical y c)) (Q d.radical (act d.radical y t))
          (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
            (U d.radical (act d.radical y c)) ≤ Nat.card F^2 := by
    have hya : act d.radical y a=a := hy
    constructor
    · conv_lhs => rw [←hya]
      rw [mover_act,mover_act,hequal]
    · rw [own_index_act]
      exact hcindex
  have hdata : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical w) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical w) (Nat.card F^2) ∧
      (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical u) ≤ Nat.card F^2 := by
    rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact selected g⁻¹ ((stabilizer d.radical a).inv_mem (Ltilde_le_stabilizer a hg))
    · have hy := (stabilizer d.radical a).mul_mem
        ((stabilizer d.radical a).inv_mem (Ltilde_le_stabilizer a hg))
        (Ltilde_le_stabilizer a hx)
      simpa only [act_mul] using selected (g⁻¹*x) hy
  refine ⟨g,hg,x,hx,u,hu,w,hwhich,haw,huw,hn,hnext,?_⟩
  intro back hback hmid hlast
  have hbackequal : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) =
    Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) := by
    rw [hback]
    exact hdata.1
  have hbackindex : (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical u) ≤ Nat.card F^2 := by
    rw [hback]
    exact hdata.2
  have residual_selector (g₂ x₂ : FreeAmalgam d.radical)
      (hg₂ : g₂ ∈ Ltilde d.radical u) (hx₂ : x₂ ∈ Ltilde d.radical u)
      (v s : Vertex d.radical)
      (hs : (v=act d.radical g₂⁻¹ a ∧ s=act d.radical g₂⁻¹ (back.walk.getVert 1)) ∨
        (v=act d.radical x₂ (act d.radical g₂⁻¹ a) ∧
          s=act d.radical x₂ (act d.radical g₂⁻¹ (back.walk.getVert 1)))) :
      ∃ y ∈ Ltilde d.radical u,
        act d.radical y a=v ∧ act d.radical y (back.walk.getVert 1)=s := by
    rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨g₂⁻¹,(Ltilde d.radical u).inv_mem hg₂,rfl,rfl⟩
    · refine ⟨g₂⁻¹*x₂,(Ltilde d.radical u).mul_mem
        ((Ltilde d.radical u).inv_mem hg₂) hx₂,?_,?_⟩ <;> rw [act_mul]
  have hut₀ : Adjacent d.radical u (back.walk.getVert 1) := by rwa [hback]
  have hat₀ : Adjacent d.radical a (back.walk.getVert 1) := by rwa [hback]
  have hun : ¬ stabilizer d.radical u ≤ normalizer
      ((Z d.radical a ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    simpa only [hmid] using h.replacement_path_neighbor_join_not_normal_of_four_le d back hb4
  by_cases hsmall₂ : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2
  · obtain ⟨E,hE,f,hf,hfQ,hTf,hidx,g₂,hg₂,x₂,hx₂,hu₁,ha₁,hu₂,ha₂,
        hgen₁,hgen₂,hfixed,hmove₁,hmove₂,hxn,hxp,v,hv,s,hwhich₂,hus,hvs,hn₂,hnext₂⟩ :=
      h.replacement_equal_small_index_selected_root_alternative d back hb4 hut₀ rfl hat₀
        hun hbackequal hsmall₂ hbackindex
    obtain ⟨y,hy,hya,hys⟩ := residual_selector g₂ x₂ hg₂ hx₂ v s hwhich₂
    have hmove : ¬ ⁅Z d.radical (path.walk.getVert 2),U d.radical u⁆ ≤ centralizer
        (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
          (Q d.radical s) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
      rcases hwhich₂ with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hmove₁
      · exact hmove₂
    have hnot := second_selector_not_trapped h d path hb back hus hvs y
      (Ltilde_le_stabilizer u hy) hya hn₂ (hCa back hback hmid hlast hsmall₂) hmove
    exact ⟨v,s,y,hy,hya,hys,hus,hvs,hn₂,
      exists_backward_path_of_not_le geometry (by omega) back hus hvs hnot⟩
  · have hlarge₂ := le_of_not_gt hsmall₂
    obtain ⟨E,hE,f,hf,hfQ,hTf,hidx,g₂,hg₂,x₂,hx₂,hu₁,ha₁,hu₂,ha₂,
        hgen₁,hgen₂,hfixed,hxn,hxp,v,hv,s,hwhich₂,hus,hvs,hn₂,hmove,hnext₂⟩ :=
      h.replacement_equal_small_index_large_backward_path d back hb4 hut₀ rfl hat₀
        hun hbackequal hlarge₂ hbackindex
    obtain ⟨y,hy,hya,hys⟩ := residual_selector g₂ x₂ hg₂ hx₂ v s hwhich₂
    exact ⟨v,s,y,hy,hya,hys,hus,hvs,hn₂,hnext₂⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
