module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFirstCentrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourEqualRootCentrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourCentralObstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallerLargePaths

/-!
# The source comparison for the actual equal-root selectors

Construct the initial selector at an arbitrary prescribed neighboring seed.
For every compatible backward path, construct the second selector in the
residual orbit of the original midpoint and retain its full path alternative.
If the second critical image is small, a failed comparison is central at both
source vertices, contradicting the full-cover commutator obstruction. If it
is large, failure forces that same image to have order q, a contradiction.

Equality of the original neighboring movers transports through the actual
first selector. Conjugation of the whole U-layer also transports its fixed
index, so no extra second-mover or centrality hypothesis is imposed.
Source: MS93 (5.12)(1), printed pp.924--925, equal-mover root branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
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

/-- The actual first and second equal-root selections satisfy the source
comparison, with both geometric alternatives and the literal second residual
conjugator retained. The initial neighboring seed remains arbitrary. -/
theorem Input.replacement_distance_four_equal_root_selected_comparison
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
            ((∃ next : CriticalPath d.radical geometry v (back.walk.getVert (back.walk.length-2)),
              next.walk.getVert 1=s ∧
              ∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i) ∨
            (Z d.radical v ≤ Q d.radical (back.walk.getVert (back.walk.length-2)) ∧
              Nat.card F ≤ (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
                (Z d.radical (path.walk.getVert 2) ⊓ Q d.radical u) ∧
              X d.radical (path.walk.getVert 2) ⊓ Q d.radical u ≤
                normalizer (Z d.radical v : Set _) ∧
              ⁅⁅X d.radical (path.walk.getVert 2) ⊓ Q d.radical u,Z d.radical v⁆,
                Z d.radical v⁆=⊥)) ∧
            ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
              ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
                ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆) := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  obtain ⟨g,hg,x,hx,u,hu,w,hwhich,haw,huw,hn,hnext,hCa⟩ :=
    h.replacement_distance_four_first_root_selected_centrality d path hb hat hfirst hct
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
  by_cases hsmall₂ : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2
  · obtain ⟨g₂,hg₂,x₂,hx₂,v,hv,s,hwhich₂,hus,hvs,hn₂,hnext₂,hCu⟩ :=
      h.replacement_distance_four_equal_root_selected_centrality d path hb back hmid
        hbackequal hsmall₂ hbackindex
    obtain ⟨y,hy,hya,hys⟩ := residual_selector g₂ x₂ hg₂ hx₂ v s hwhich₂
    refine ⟨v,s,y,hy,hya,hys,hus,hvs,hn₂,hnext₂,?_⟩
    by_contra hbad
    exact h.replacement_distance_four_comparison_not_two_centers d path hb back hus hvs y
      (Ltilde_le_stabilizer u hy) hya hbad
      (le_inf (hCa back hback hmid hlast v s hus hvs hbad) (hCu hbad))
  · have hlarge₂ := le_of_not_gt hsmall₂
    have hun : ¬ stabilizer d.radical u ≤ normalizer
        ((Z d.radical a ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      simpa only [hmid] using h.replacement_path_neighbor_join_not_normal_of_four_le d back hb4
    have hut₀ : Adjacent d.radical u (back.walk.getVert 1) := by rwa [hback]
    have hat₀ : Adjacent d.radical a (back.walk.getVert 1) := by rwa [hback]
    obtain ⟨E,hE,f,hf,hfQ,hTf,hidx,g₂,hg₂,x₂,hx₂,hu₁,ha₁,hu₂,ha₂,
        hgen₁,hgen₂,hfixed,hxn,hxp,v,hv,s,hwhich₂,hus,hvs,hn₂,hmove,hnext₂⟩ :=
      h.replacement_equal_small_index_large_backward_path d back hb4 hut₀ rfl hat₀
        hun hbackequal hlarge₂ hbackindex
    obtain ⟨y,hy,hya,hys⟩ := residual_selector g₂ x₂ hg₂ hx₂ v s hwhich₂
    refine ⟨v,s,y,hy,hya,hys,hus,hvs,hn₂,Or.inl hnext₂,?_⟩
    by_contra hbad
    have hi := (h.replacement_distance_four_comparison_failure d path hb back hus hvs hbad).2.1
    have hq : 1 < Nat.card F := Finite.one_lt_card
    rw [hi] at hlarge₂
    nlinarith

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
