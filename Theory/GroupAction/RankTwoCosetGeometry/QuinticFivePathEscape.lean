module
public import Theory.GroupAction.RankTwoCosetGeometry.FourPathCore
public import Theory.GroupAction.RankTwoCosetGeometry.SecondBallKernel
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon
public import Theory.GroupAction.RankTwoCosetGeometry.PathKernelTransport

/-!
# Cubic escape after five edges

Suppose every four-edge path from a quintic vertex has its fixer in the
middle first-ball kernel. If all five-path fixers lay in their cubic
endpoint kernels, extending and shifting a path would put its fixer in
the penultimate second-ball kernel. A cardinality comparison forces
equality. Shifting once more would identify second kernels at distinct
quintic neighbors, contradicting their separation.

Under five-path transitivity, failure of escape for one path propagates
to all paths, so each five-path fixer escapes. Only the vertex stabilizers
must be finite. The original source application supplies the cardinality
comparison by counting 320 rooted paths and the earlier second-kernel bound.
Source: the path and kernel conventions of Aschbacher--Smith F.3.2--4 and
F.7.3, pp.270,311--312; application to14.2.20--21, pp.988--989.
-/

public section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- Two incident index-two restrictions bound the middle kernel by four times the path fixer. -/
theorem four_path_middle_card_le
    {a : Vertex F} (p : BasedWalk (graph F) 4 a) (hp : p.Nonbacktracking)
    [Finite (stabilizer F (p.2.1 : Vertex F))]
    (hb : Nat.card ((graph F).neighborSet (p.1 : Vertex F)) = 3)
    (hd : Nat.card ((graph F).neighborSet (p.2.2.1 : Vertex F)) = 3)
    (hib : (ballKernel F (p.1 : Vertex F) 1).relIndex
      (ballKernel F (p.2.1 : Vertex F) 1) ≤ 2)
    (hid : (ballKernel F (p.2.2.1 : Vertex F) 1).relIndex
      (ballKernel F (p.2.1 : Vertex F) 1) ≤ 2) :
    Nat.card (ballKernel F (p.2.1 : Vertex F) 1) ≤
      4 * Nat.card (pathStabilizer F p) := by
  let Q := ballKernel F (p.2.1 : Vertex F) 1
  let P := pathStabilizer F p
  have hPm : P ≤ stabilizer F (p.2.1 : Vertex F) := by
    intro g hg
    exact hg _ (by
      change (p.2.1 : Vertex F) ∈ a :: (p.1 : Vertex F) :: p.2.2.vertices
      simp only [List.mem_cons]
      exact Or.inr (Or.inr (origin_mem_vertices F p.2.2)))
  let : Finite P := Finite.of_injective (inclusion hPm) (inclusion_injective hPm)
  let : Finite Q := Finite.of_injective (inclusion (ballKernel_le_stabilizer F _ 1))
    (inclusion_injective _)
  let : Finite (Q ⊓ P : Subgroup G) :=
    Finite.of_injective (inclusion inf_le_left : (Q ⊓ P : Subgroup G) → Q)
      (inclusion_injective _)
  have hP : P = ballKernel F (p.1 : Vertex F) 1 ⊓
      ballKernel F (p.2.2.1 : Vertex F) 1 :=
    pathStabilizer_four_eq_cubic_kernels F p hp hb hd
  have hi : P.relIndex Q ≤ 4 := by
    rw [hP]
    exact relIndex_inf_le.trans (Nat.mul_le_mul hib hid)
  have hc := ((Q ⊓ P).subgroupOf Q).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (show Q ⊓ P ≤ Q from inf_le_left)).toEquiv] at hc
  change (Q ⊓ P).relIndex Q * Nat.card (Q ⊓ P : Subgroup G) = Nat.card Q at hc
  rw [inf_relIndex_left] at hc
  have hl : Nat.card (Q ⊓ P : Subgroup G) ≤ Nat.card P := card_le_of_le inf_le_right
  change Nat.card Q ≤ 4 * Nat.card P
  rw [←hc]
  exact Nat.mul_le_mul hi hl

private theorem type_two_steps {a b c : Vertex F}
    (hab : (graph F).Adj a b) (hbc : (graph F).Adj b c) : a.type = c.type := by
  have h1 := hab.1
  have h2 := hbc.1
  cases ha : a.type <;> cases hb : b.type <;> cases hc : c.type <;> simp_all

/-- If all five-path fixers fail to escape, they lie in the second kernel
at the penultimate vertex. The middle four-path condition supplies the
first kernel before varying the last edge. -/
theorem five_fixer_le_penultimate_second_kernel
    (hdeg : BasedWalk.HasTwoNeighbors (graph F))
    (hcubic : ∀ v : Vertex F, v.type = false → Nat.card ((graph F).neighborSet v) = 3)
    (hfour : ∀ {a : Vertex F}, a.type = true →
      ∀ p : BasedWalk (graph F) 4 a, p.Nonbacktracking →
        pathStabilizer F p ≤ ballKernel F (p.2.1 : Vertex F) 1)
    (hfail : ∀ {a : Vertex F}, a.type = true →
      ∀ p : BasedWalk (graph F) 5 a, p.Nonbacktracking →
        pathStabilizer F p ≤ ballKernel F p.endpoint 1)
    {a : Vertex F} (ha : a.type = true)
    (p : BasedWalk (graph F) 5 a) (hp : p.Nonbacktracking) :
    pathStabilizer F p ≤ ballKernel F p.penultimate 2 := by
  have hfirst : ∀ {a : Vertex F}, a.type = true →
      ∀ p : BasedWalk (graph F) 5 a, p.Nonbacktracking →
        pathStabilizer F p ≤ ballKernel F p.penultimate 1 := by
    intro a ha p hp
    rcases p with ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,⟨⟨d,hcd⟩,⟨⟨e,hde⟩,⟨⟨f,hef⟩,pend⟩⟩⟩⟩⟩
    obtain ⟨g,hfg,hge⟩ := hdeg f e
    let q : BasedWalk (graph F) 4 c :=
      ⟨⟨d,hcd⟩,⟨⟨e,hde⟩,⟨⟨f,hef⟩,⟨⟨g,hfg⟩,PUnit.unit⟩⟩⟩⟩
    have hq : q.Nonbacktracking := ⟨hp.2.2.1,hp.2.2.2.1,hge,trivial⟩
    have hc : c.type = true := (type_two_steps F hab hbc).symm.trans ha
    intro x hx
    apply hfour hc q hq
    have hxf := hfail ha _ hp hx
    change ∀ z ∈ [c,d,e,f,g], x • z = z
    change ∀ z ∈ [a,b,c,d,e,f], x • z = z at hx
    simp only [List.forall_mem_cons] at hx ⊢
    exact ⟨hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2.1,hx.2.2.2.2.2.1,
      hxf g ((mem_ball_one F _ _).mpr (.inl hfg)),by intro z hz; cases hz⟩
  rcases p with ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,⟨⟨d,hcd⟩,⟨⟨e,hde⟩,⟨⟨f,hef⟩,pend⟩⟩⟩⟩⟩
  intro x hx z hz
  have hxe := hfirst ha _ hp hx
  have hneighbor (v : Vertex F) (hev : (graph F).Adj e v) : x ∈ ballKernel F v 1 := by
    by_cases hvd : v = d
    · subst v
      let q : BasedWalk (graph F) 2 c := ⟨⟨d,hcd⟩,⟨⟨e,hde⟩,PUnit.unit⟩⟩
      have hdcard : Nat.card ((graph F).neighborSet d) = 3 := by
        apply hcubic
        have hc : c.type = true := (type_two_steps F hab hbc).symm.trans ha
        have hh := hcd.1
        change c.type ≠ d.type at hh
        rw [hc] at hh
        cases ht : d.type with
        | false => rfl
        | true => exact (hh ht.symm).elim
      exact (pathStabilizer_two_eq_ballKernel_one F q ⟨hp.2.2.1,trivial⟩ hdcard) ▸
        (show x ∈ pathStabilizer F q from by
          change ∀ z ∈ [c,d,e], x • z = z
          intro z hz
          exact hx z (by simp only [BasedWalk.vertices,List.mem_cons] at hz ⊢; tauto))
    · let q : BasedWalk (graph F) 5 a :=
        ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,⟨⟨d,hcd⟩,⟨⟨e,hde⟩,⟨⟨v,hev⟩,PUnit.unit⟩⟩⟩⟩⟩
      have hq : q.Nonbacktracking := ⟨hp.1,hp.2.1,hp.2.2.1,hvd,trivial⟩
      apply hfail ha q hq
      change ∀ z ∈ [a,b,c,d,e,v], x • z = z
      change ∀ z ∈ [a,b,c,d,e,f], x • z = z at hx
      simp only [List.forall_mem_cons] at hx ⊢
      exact ⟨hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2.1,
        hxe v ((mem_ball_one F _ _).mpr (.inl hev)),by intro z hz; cases hz⟩
  have hdist : (graph F).edist e z ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp : (2 : ℕ∞) ≠ ⊤) hz
  obtain ⟨q,hq⟩ := SimpleGraph.exists_walk_of_edist_ne_top hdist
  have hlen : q.length ≤ 2 := ENat.natCast_le_natCast.mp (hq ▸ hz)
  cases q with
  | nil => exact hxe e (center_mem_ball F e 1)
  | @cons _ v _ hev q =>
    exact hneighbor v hev z (q.edist_le.trans
      (ENat.natCast_le_natCast.mpr (by simpa using hlen)))
/-- Five-path fixers cannot all be trapped in their cubic endpoint kernels
when the second kernels are small and separated across cubic vertices. -/
theorem not_all_five_fixers_le_endpoint_kernel
    [∀ i, Finite (F i)]
    (hdeg : BasedWalk.HasTwoNeighbors (graph F))
    (hcubic : ∀ v : Vertex F, v.type = false → Nat.card ((graph F).neighborSet v) = 3)
    (hfour : ∀ {a : Vertex F}, a.type = true →
      ∀ p : BasedWalk (graph F) 4 a, p.Nonbacktracking →
        pathStabilizer F p ≤ ballKernel F (p.2.1 : Vertex F) 1)
    (hcard : ∀ {a : Vertex F}, a.type = true →
      ∀ p : BasedWalk (graph F) 5 a, p.Nonbacktracking →
        Nat.card (ballKernel F p.penultimate 2) ≤ Nat.card (pathStabilizer F p))
    (hsep : ∀ u w v : Vertex F, u.type = true → (graph F).Adj u w →
      (graph F).Adj w v → u ≠ v → ballKernel F u 2 ≠ ballKernel F v 2)
    {a : Vertex F} (ha : a.type = true)
    (p : BasedWalk (graph F) 5 a) (hp : p.Nonbacktracking) :
    ¬ (∀ {a : Vertex F}, a.type = true →
      ∀ p : BasedWalk (graph F) 5 a, p.Nonbacktracking →
        pathStabilizer F p ≤ ballKernel F p.endpoint 1) := by
  intro hfail
  have heq {a : Vertex F} (ha : a.type = true)
      (p : BasedWalk (graph F) 5 a) (hp : p.Nonbacktracking) :
      pathStabilizer F p = ballKernel F p.penultimate 2 := by
    let : Finite (ballKernel F p.penultimate 2) :=
      Finite.of_injective (inclusion (ballKernel_le_stabilizer F _ 2)) (inclusion_injective _)
    exact eq_of_le_of_card_ge
      (five_fixer_le_penultimate_second_kernel F hdeg hcubic hfour hfail ha p hp)
      (hcard ha p hp)
  rcases p with ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,⟨⟨d,hcd⟩,⟨⟨e,hde⟩,⟨⟨f,hef⟩,pend⟩⟩⟩⟩⟩
  obtain ⟨g,hfg,hge⟩ := hdeg f e
  let p : BasedWalk (graph F) 5 a :=
    ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,⟨⟨d,hcd⟩,⟨⟨e,hde⟩,⟨⟨f,hef⟩,pend⟩⟩⟩⟩⟩
  let q : BasedWalk (graph F) 5 g :=
    ⟨⟨f, show (graph F).Adj g f from hfg.symm⟩,
      ⟨⟨e, show (graph F).Adj f e from hef.symm⟩,
        ⟨⟨d, show (graph F).Adj e d from hde.symm⟩,
          ⟨⟨c, show (graph F).Adj d c from hcd.symm⟩,
            ⟨⟨b, show (graph F).Adj c b from hbc.symm⟩,PUnit.unit⟩⟩⟩⟩⟩
  have hq : q.Nonbacktracking :=
    ⟨Ne.symm hge,Ne.symm hp.2.2.2.1,Ne.symm hp.2.2.1,Ne.symm hp.2.1,trivial⟩
  have hc : c.type = true := (type_two_steps F hab hbc).symm.trans ha
  have he : e.type = true := (type_two_steps F hcd hde).symm.trans hc
  have hg : g.type = true := (type_two_steps F hef hfg).symm.trans he
  have hP : pathStabilizer F p = pathStabilizer F q := by
    apply le_antisymm
    · intro x hx
      have hf := hfail ha p hp hx
      change ∀ z ∈ [a,b,c,d,e,f], x • z = z at hx
      change ∀ z ∈ [g,f,e,d,c,b], x • z = z
      simp only [List.forall_mem_cons] at hx ⊢
      exact ⟨hf g ((mem_ball_one F _ _).mpr (.inl hfg)),
        hx.2.2.2.2.2.1,hx.2.2.2.2.1,hx.2.2.2.1,hx.2.2.1,hx.2.1,
        by intro z hz; cases hz⟩
    · intro x hx
      have hb := hfail hg q hq hx
      change ∀ z ∈ [g,f,e,d,c,b], x • z = z at hx
      change ∀ z ∈ [a,b,c,d,e,f], x • z = z
      simp only [List.forall_mem_cons] at hx ⊢
      exact ⟨hb a ((mem_ball_one F _ _).mpr (.inl hab.symm)),
        hx.2.2.2.2.2.1,hx.2.2.2.2.1,hx.2.2.2.1,hx.2.2.1,hx.2.1,
        by intro z hz; cases hz⟩
  have hce := (heq hg q hq).symm.trans (hP.symm.trans (heq ha p hp))
  exact hsep c d e hc hcd hde (Ne.symm hp.2.2.1) hce
/-- Five-path transitivity makes the endpoint-escape obstruction uniform,
so the separated second kernels exclude it for each individual path. -/
theorem five_path_kernel_escape_of_transitive
    [∀ i, Finite (F i)]
    (hdeg : BasedWalk.HasTwoNeighbors (graph F))
    (hcubic : ∀ v : Vertex F, v.type = false → Nat.card ((graph F).neighborSet v) = 3)
    (hfour : ∀ {a : Vertex F}, a.type = true →
      ∀ p : BasedWalk (graph F) 4 a, p.Nonbacktracking →
        pathStabilizer F p ≤ ballKernel F (p.2.1 : Vertex F) 1)
    (hcard : ∀ {a : Vertex F}, a.type = true →
      ∀ p : BasedWalk (graph F) 5 a, p.Nonbacktracking →
        Nat.card (ballKernel F p.penultimate 2) ≤ Nat.card (pathStabilizer F p))
    (hsep : ∀ u w v : Vertex F, u.type = true → (graph F).Adj u w →
      (graph F).Adj w v → u ≠ v → ballKernel F u 2 ≠ ballKernel F v 2)
    (ht : RootPathTransitive (graph F) G (base F true) 5)
    (p : BasedWalk (graph F) 5 (base F true)) (hp : p.Nonbacktracking) :
    ¬ pathStabilizer F p ≤ ballKernel F p.endpoint 1 := by
  intro hle
  apply not_all_five_fixers_le_endpoint_kernel F hdeg hcubic hfour hcard hsep rfl p hp
  intro a ha q hq
  obtain ⟨g,hg⟩ := exists_path_translate_of_rootPathTransitive F ht p hp ha q hq
  exact pathStabilizer_le_endpoint_ballKernel_of_vertices F p q g hg 1 hle
end Subgroup.CosetGeometry.RankTwo
