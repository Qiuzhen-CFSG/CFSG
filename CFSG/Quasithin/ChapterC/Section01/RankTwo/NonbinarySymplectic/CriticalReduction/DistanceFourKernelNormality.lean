module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourCoherentComparison

/-!
# Actual normality of the selected distance-four kernel join

Enrich one coherent comparison certificate without replacing any of its
selectors or paths. The literal comparison makes the endpoint normalize
W joined with Z_u, where W is the original U_v intersect Q_z. The equal
selected mover normalizes this join because its commutator on Z_v lies in
Z_u. It need not normalize the distant Q_z itself.

The local equal-root calculation is transported from the original root
critical path to u; its endpoint is not identified with the actual backward
endpoint. Thus no small-image assumption on the backward path is needed.
The full seed and fixed attachments are retained, along with the actual
second conjugator, its generating triple, and all path overlaps.
Source: the normality step following MS93 (5.12)(1), printed pp.925--926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open scoped Pointwise commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

/-- Two actual backward paths and comparison (1) on their same selected
second source, with the first pair's exact selectors and the second residual orbit. -/
@[expose] def distanceFourNormalizedComparison {M : Type*} [Group M] {R : Subgroup M}
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (c t : Vertex R) (q : ℕ) : Prop :=
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
          Subgroup.SmallMover.join (U R v) (Q R v) (Q R s) (q^2) ⊔
            Z R (path.walk.getVert 2) ≤ normalizer
              (((U R v ⊓ Q R z) ⊔ Z R u : Subgroup (FreeAmalgam R)) : Set _) ∧
          ∃ x₂ ∈ Ltilde R u,
          ((Subgroup.SmallMover.join (U R v) (Q R v) (Q R s) (q^2) ⊔
            Z R (path.walk.getVert 2)) ⊔
              (Z R (path.walk.getVert 2)).map (MulAut.conj x₂).toMonoidHom = stabilizer R u) ∧
          ⁅U R v ⊓ Q R z,Z R (path.walk.getVert 2)⁆ ≤
            ⁅Z R u,Z R (path.walk.getVert 2)⁆ ⊔
              ⁅U R v ⊓ Q R z,X R (path.walk.getVert 2) ⊓ Q R u⁆ ∧
          ∃ next : CriticalPath R geometry v a,
            next.walk.getVert 1=s ∧
            ∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i

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

private theorem normalizes_join_of_commutators {G : Type*} [Group G] (I B C : Subgroup G)
    (hB : ⁅I,B⁆ ≤ B ⊔ C) (hC : ⁅I,C⁆ ≤ B ⊔ C) :
    I ≤ normalizer ((B ⊔ C : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hm (S : Subgroup G) (hS : S ≤ B ⊔ C) (hcom : ⁅I,S⁆ ≤ B ⊔ C) :
      S.map (MulAut.conj g).toMonoidHom ≤ B ⊔ C := by
    rintro _ ⟨a,ha,rfl⟩
    change g*a*g⁻¹ ∈ B ⊔ C
    have he : g*a*g⁻¹ = ⁅g,a⁆*a := by simp [commutatorElement_def,mul_assoc]
    rw [he]
    exact (B ⊔ C).mul_mem (hcom (commutator_mem_commutator hg ha)) (hS ha)
  have hmap : (B ⊔ C).map (MulAut.conj g).toMonoidHom ≤ B ⊔ C := by
    rw [Subgroup.map_sup]
    exact sup_le (hm B le_sup_left hB) (hm C le_sup_right hC)
  exact hmap (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)


variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem comparison_kernel_normalized
    {geometry : Geometry d.radical} {a z u v s : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
    (hequal : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical s) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical s) (Nat.card F^2))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical s) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical u) ≤ Nat.card F^2)
    (hcompare : ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
        ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆) :
    Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2) ≤
      normalizer (((U d.radical v ⊓ Q d.radical z) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  let W := U d.radical v ⊓ Q d.radical z
  let e := path.walk.getVert 2
  let J := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
    (Q d.radical s) (Nat.card F^2)
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical path.start_color
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical back.start_color
  let r := g⁻¹*j
  have hra : act d.radical r a=u := by
    rw [hg,act_mVertex]
    dsimp only [r]
    rw [mul_inv_cancel_left,←hj]
  have hroot : (Q d.radical (act d.radical r a)).relIndex
      (Z d.radical (act d.radical r z)) < Nat.card F^2 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj r⁻¹).injective]
    exact hsmall
  obtain ⟨hOmega,hcomm⟩ := h.replacement_equal_root_neighbor_commutator d (path.act r)
    hb4 (by rw [hra]; exact hus) hvs hroot
    (by simpa only [hra] using hJm) (by simpa only [hra] using hequal)
  rw [hra,←hequal] at hOmega hcomm
  have hJZu : ⁅J,Z d.radical u⁆ ≤ Z d.radical u := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.SmallMover.join_le _ _ _ _).trans
        ((show Q d.radical s ≤ stabilizer d.radical u from
          fun _ hx => hx.2 u (adjacent_symm _ hus)).trans (Z_normalized d.radical u)))
  have hJW : ⁅J,W⁆ ≤ Z d.radical u := by
    rw [commutator_comm]
    exact ((commutator_mono (inf_le_left.trans (U_le_Z v)) le_rfl).trans hcomm).trans hOmega
  have hJn : J ≤ normalizer ((W ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) :=
    normalizes_join_of_commutators J W (Z d.radical u)
      (hJW.trans le_sup_right) (hJZu.trans le_sup_right)
  have hAn := (h.replacement_distance_four_comparison_actor d path hb back hus hvs).2.2.2.2
  have hAW : ⁅W,X d.radical e ⊓ Q d.radical u⁆ ≤ W :=
    le_normalizer_iff_commutator_le_left.mp hAn
  have hR : ⁅Z d.radical u,Z d.radical e⁆ ≤ Z d.radical u :=
    critical_commutator_le_start_seed back
  have hEW : ⁅Z d.radical e,W⁆ ≤ W ⊔ Z d.radical u := by
    rw [commutator_comm]
    exact hcompare.trans (sup_le (hR.trans le_sup_right) (hAW.trans le_sup_left))
  have hEu : ⁅Z d.radical e,Z d.radical u⁆ ≤ W ⊔ Z d.radical u := by
    rw [commutator_comm]
    exact hR.trans le_sup_right
  exact sup_le hJn (normalizes_join_of_commutators (Z d.radical e) W
    (Z d.radical u) hEW hEu)

/-- The equal/small original branch reduces to two coherent actual paths
with their same-member comparison and actual kernel-join normality, or an explicit strict-index neighbor with
unequal mover. The uniform bound and both trapping alternatives are discharged internally. Rebased neighbors are
recorded, rather than identified with the prescribed original neighbor. -/
theorem Input.replacement_distance_four_normalized_comparison_or_strict_unequal_neighbor
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
      distanceFourNormalizedComparison path c' t (Nat.card F)) := by
  obtain hchoice := h.replacement_distance_four_coherent_comparison_or_strict_unequal_neighbor d
    path hb hat hfirst hct hnormal hequal hsmall hJm
  rcases hchoice with hunequal | ⟨c',hc',hequal',hcoherent⟩
  · exact Or.inl hunequal
  obtain ⟨g,hg,x,hx,u,w,hwhich,haw,huw,back,hback,hover,v,s,y,hy,hya,hys,hus,hvs,
      hn,x₂,hx₂,hgen,hcompare,next,hnext,hovernext⟩ := hcoherent
  have huData : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical w) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical w) (Nat.card F^2) ∧
      (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical u) ≤ Nat.card F^2 := by
    have transport (r : FreeAmalgam d.radical) (hr : r ∈ stabilizer d.radical a) :
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
            (Q d.radical (act d.radical r t)) (Nat.card F^2) =
          Subgroup.SmallMover.join (U d.radical (act d.radical r c'))
            (Q d.radical (act d.radical r c')) (Q d.radical (act d.radical r t)) (Nat.card F^2) ∧
        (centralizer (Subgroup.SmallMover.join (U d.radical (act d.radical r c'))
            (Q d.radical (act d.radical r c')) (Q d.radical (act d.radical r t))
            (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical (act d.radical r c')) ≤ Nat.card F^2 := by
      have hra : act d.radical r a=a := hr
      constructor
      · conv_lhs => rw [←hra]
        rw [mover_act,mover_act,hequal']
      · rw [own_index_act,own_index_neighbors _ hat hc']
        exact hJm
    rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact transport g⁻¹ ((stabilizer d.radical a).inv_mem (Ltilde_le_stabilizer a hg))
    · simpa only [act_mul] using transport (g⁻¹*x)
        ((stabilizer d.radical a).mul_mem
          ((stabilizer d.radical a).inv_mem (Ltilde_le_stabilizer a hg)) (Ltilde_le_stabilizer a hx))
  have hyu : act d.radical y u=u := Ltilde_le_stabilizer u hy
  have hyw : act d.radical y w=s := by simpa only [hback] using hys
  have he : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical s) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical s) (Nat.card F^2) := by
    have hh := congrArg (Subgroup.map (MulAut.conj y⁻¹).toMonoidHom) huData.1
    rwa [←mover_act,←mover_act,hya,hyw,hyu] at hh
  have hi : (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical s) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical u) ≤ Nat.card F^2 := by
    have hh := own_index_act (Nat.card F^2) y u w
    rw [hyu,hyw] at hh
    exact hh.trans_le huData.2
  have hnormalized := comparison_kernel_normalized h d path hb hsmall back hus hvs he hi hcompare
  exact Or.inr ⟨c',hc',hequal',g,hg,x,hx,u,w,hwhich,haw,huw,back,hback,hover,
    v,s,y,hy,hya,hys,hus,hvs,hn,hnormalized,x₂,hx₂,hgen,hcompare,next,hnext,hovernext⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
