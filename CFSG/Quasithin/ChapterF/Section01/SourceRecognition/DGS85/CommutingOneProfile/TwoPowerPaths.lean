module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.MixedPathRegularity

/-!
# Five-walk counting for the characteristic-two source profiles

With forward valences 2^a and 2^b, a fixed edge has 2^(2(a+b))
nonbacktracking five-walk extensions. An edge two-core of that order acts
freely when the five-walk fixers have odd order, hence transitively.
Local transitivity aligns the first edge. Neither the completion nor the
graph is assumed finite; the finite sets used in the proof are established
from their orders.

When a and b are positive, transitivity makes shorter walks regular and
odd longer fixers cannot be transitive on their even exit sets. The exact
regular nonbacktracking lengths are therefore zero through four.
UnitaryPathParameters supplies all hypotheses from the original marked branch.
Source: DGS85, Groups and Graphs (1985), (3.4)(c), (11.8)(g),
printed pp.74,176--177.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
private def edgePathsEquiv {V : Type*} (Γ : SimpleGraph V) (n : ℕ)
    (a : V) (b : Γ.neighborSet a) :
    {p : BasedWalk Γ (n+1) a // p.Nonbacktracking ∧ p.1 = b} ≃
      BasedWalk.Forward Γ n a b :=
  (show {p : BasedWalk Γ (n+1) a // p.Nonbacktracking ∧ p.1 = b} ≃
      {p : BasedWalk Γ n b // Avoids Γ a p} from {
    toFun := by
      rintro ⟨⟨c,p⟩,hp,hc⟩
      change c = b at hc
      subst c
      exact ⟨p,by cases n <;> exact hp⟩
    invFun := fun p => ⟨⟨b,p.val⟩,by cases n <;> exact p.property,rfl⟩
    left_inv := by rintro ⟨⟨c,p⟩,hp,hc⟩; change c = b at hc; subst c; rfl
    right_inv := by intro p; rfl }).trans (forwardEquiv Γ n a b).symm

private theorem first_smul {G : Type*} [Group G] (F : Bool → Subgroup G)
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) (n+1) a)
    (g : stabilizer F a) : ((actPath F g p).1 : Vertex F) = (g : G) • (p.1 : Vertex F) := by
  have hh := congrArg (fun l : List (Vertex F) => l.tail.head?) (vertices_actPath F g p)
  simpa only [BasedWalk.vertices, List.tail_cons, List.map_cons, head_vertices,
    List.head?_map, Option.map_some, Option.some.injEq] using hh

private theorem edge_transitive_of_odd {G : Type*} [Group G]
    (F : Bool → Subgroup G) (e : Bool → ℕ) (hval : ∀ v : Vertex F,
      Nat.card ((graph F).neighborSet v) = 2^(e v.type)+1)
    {a : Vertex F} (b : (graph F).neighborSet a)
    (T : Subgroup G) (hT : T ≤ stabilizer F a ⊓ stabilizer F b)
    (hTc : Nat.card T = 2^(2*(e false+e true))) (hTp : IsPGroup 2 T)
    (hodd : ∀ p : BasedWalk (graph F) 5 a, p.Nonbacktracking →
      Odd (Nat.card (pathStabilizer F p))) :
    ∀ p q : BasedWalk (graph F) 5 a, p.Nonbacktracking → q.Nonbacktracking →
      p.1 = b → q.1 = b → ∃ g ∈ T, p.vertices.map (g • ·) = q.vertices := by
  classical
  let : MulAction (stabilizer F a) (BasedWalk (graph F) 5 a) := pathAction F 5 a
  intro p q hp hq hpb hqb
  let Y := {p : BasedWalk (graph F) 5 a // p.Nonbacktracking ∧ p.1 = b}
  let : ∀ v : Vertex F, Finite ((graph F).neighborSet v) :=
    fun v => Nat.finite_of_card_ne_zero (by rw [hval]; exact Nat.succ_ne_zero _)
  have hflip : ∀ {v w : Vertex F}, (graph F).Adj v w → w.type = !v.type := by
    intro v w hvw
    have hn := hvw.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have hY : Nat.card Y = 2^(2*(e false+e true)) := by
    rw [Nat.card_congr (edgePathsEquiv (graph F) 4 a b),
      card_forward (graph F) (fun v => v.type) (fun i => 2^(e i)+1) hflip hval 4 a b b.property]
    cases (b : Vertex F).type <;>
      simp only [BasedWalk.forwardCount, Bool.not_false, Bool.not_true,
        Nat.add_sub_cancel, mul_one] <;>
      rw [←pow_add,←pow_add,←pow_add] <;> congr 1 <;> omega
  let : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY]; positivity)
  let : Finite T := Nat.finite_of_card_ne_zero (by rw [hTc]; positivity)
  let : Finite (pathStabilizer F p) := Nat.finite_of_card_ne_zero (by
    have hh := hodd p hp; intro hz; rw [hz] at hh; exact (by decide : ¬Odd (0:ℕ)) hh)
  let j : T →* stabilizer F a := inclusion (hT.trans inf_le_left)
  let f : T → Y := fun x => ⟨j x • p,
    (nonbacktracking_smul_path F (j x) p).mpr hp,by
      apply Subtype.ext
      change ((actPath F (j x) p).1 : Vertex F) = b
      rw [first_smul,hpb]
      exact (hT x.property).2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hs : j x • p = j y • p := congrArg Subtype.val hxy
    have hz : ((j x)⁻¹ * j y) • p = p := by
      rw [mul_smul,←hs,inv_smul_smul]
    have hfix : ((x : G)⁻¹ * y) ∈ pathStabilizer F p :=
      (mem_pathStabilizer_iff F p ((j x)⁻¹ * j y)).mpr hz
    obtain ⟨k,hk⟩ := hTp (x⁻¹*y)
    have hd : orderOf ((x : G)⁻¹*y) ∣ 2^k := by
      change orderOf ((x⁻¹*y : T) : G) ∣ 2^k
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hk
    have ho : orderOf ((x : G)⁻¹*y) ∣ Nat.card (pathStabilizer F p) := by
      simpa only [Subgroup.orderOf_mk] using orderOf_dvd_natCard
        (⟨_,hfix⟩ : pathStabilizer F p)
    apply Subtype.ext
    exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes ((hodd p hp).coprime_two_right.pow_right k) ho hd))
  obtain ⟨x,hx⟩ := (hf.bijective_of_nat_card_le (by omega : Nat.card Y ≤ Nat.card T)).surjective ⟨q,hq,hqb⟩
  exact ⟨x,x.property,(vertices_smul_path F (j x) p).symm.trans
    (congrArg BasedWalk.vertices (congrArg Subtype.val hx))⟩

/-- Equality of the free edge-core orbit and the five-walk extension count
gives transitivity in each vertex orbit. -/
theorem two_power_graph_five_walk_transitive_of_edge_cores {G : Type*} [Group G]
    (F : Bool → Subgroup G) (e : Bool → ℕ) (hval : ∀ v : Vertex F,
      Nat.card ((graph F).neighborSet v) = 2^(e v.type)+1)
    (hcard : ∀ {a b : Vertex F}, (graph F).Adj a b →
      Nat.card ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) = 2^(2*(e false+e true)))
    (hodd : ∀ {a : Vertex F} (p : BasedWalk (graph F) 5 a), p.Nonbacktracking →
      Odd (Nat.card (pathStabilizer F p))) (a : Vertex F) :
    RootPathTransitive (graph F) G a 5 := by
  let : MulAction (stabilizer F a) (BasedWalk (graph F) 5 a) := pathAction F 5 a
  intro p q hp hq
  obtain ⟨g,hga,hg⟩ := locally_transitive F p.1.property q.1.property
  let g' : stabilizer F a := ⟨g,hga⟩
  let p' := g' • p
  have hp' : p'.Nonbacktracking := (nonbacktracking_smul_path F g' p).mpr hp
  have hfirst : p'.1 = q.1 := Subtype.ext ((first_smul F p g').trans hg)
  let E := stabilizer F a ⊓ stabilizer F (q.1 : Vertex F)
  obtain ⟨t,ht,htq⟩ := edge_transitive_of_odd F e hval q.1 (E.pCoreIn 2)
    (E.pCoreIn_le 2) (hcard q.1.property) (isPGroup_pCoreIn 2 E) hodd
    p' q hp' hq hfirst rfl
  refine ⟨t*g,?_,?_⟩
  · rw [mul_smul,hga]
    exact ((E.pCoreIn_le 2) ht).1
  · rw [show p'.vertices = p.vertices.map (g • ·) from vertices_smul_path F g' p,
      List.map_map] at htq
    simpa only [Function.comp_def,mul_smul] using htq


open Theory.GroupAction.CubicTree
private theorem two_neighbors {G : Type*} [Group G] (F : Bool → Subgroup G) (e : Bool → ℕ)
    (hval : ∀ v : Vertex F, Nat.card ((graph F).neighborSet v) = 2^(e v.type)+1) :
    HasTwoNeighbors (graph F) := by
  intro a b
  exact Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet a) (by
    rw [←Nat.card_coe_set_eq,hval]; have := pow_pos (by decide : 0 < (2:ℕ)) (e a.type); omega) b

private theorem right_regular_of_root_transitive {G : Type*} [Group G]
    (F : Bool → Subgroup G) {n : ℕ} {a : Vertex F}
    (ht : RootPathTransitive (graph F) G a (n+1))
    (p : BasedWalk (graph F) n a) (hp : p.Nonbacktracking) : RightRegular (A := G) p := by
  intro z w hz hw
  have haz := forward_adj p hz
  have haw := forward_adj p hw
  obtain ⟨g,_,hg⟩ := ht (p.snoc haz) (p.snoc haw)
    ((forward_iff_snoc_nonbacktracking p hp haz).mp hz)
    ((forward_iff_snoc_nonbacktracking p hp haw).mp hw)
  rw [vertices_snoc,vertices_snoc,List.map_append,List.map_singleton] at hg
  have hs := List.append_inj hg (by simp : (p.vertices.map (g • ·)).length = p.vertices.length)
  refine ⟨g,?_,?_⟩
  · simpa only [List.map_id, id_eq] using (List.map_inj_left (l := p.vertices)
      (f := (g • ·)) (g := id)).mp (hs.1.trans (List.map_id p.vertices).symm)
  · simpa only [List.singleton_inj] using hs.2

private theorem exits_card {G : Type*} [Group G] (F : Bool → Subgroup G) (e : Bool → ℕ)
    (hval : ∀ v : Vertex F, Nat.card ((graph F).neighborSet v) = 2^(e v.type)+1)
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) (n+1) a) :
    Nat.card {z : Vertex F // Theory.GroupAction.CubicTree.Forward p z} =
      2^(e p.endpoint.type) := by
  classical
  let : Finite ((graph F).neighborSet p.endpoint) :=
    Nat.finite_of_card_ne_zero (by rw [hval]; exact Nat.succ_ne_zero _)
  let := Fintype.ofFinite ((graph F).neighborSet p.endpoint)
  let E : {z : Vertex F // Theory.GroupAction.CubicTree.Forward p z} ≃
      {z : (graph F).neighborSet p.endpoint // z ≠ ⟨p.penultimate,p.adj_penultimate_endpoint.symm⟩} := {
    toFun z := ⟨⟨z,z.property.1⟩,fun he => z.property.2 (congrArg Subtype.val he)⟩
    invFun z := ⟨z.val,z.val.property,fun he => z.property (Subtype.ext he)⟩
    left_inv z := rfl
    right_inv z := rfl }
  rw [Nat.card_congr E,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    ←Nat.card_eq_fintype_card,hval]
  simp

private theorem not_right_regular_of_odd {G : Type*} [Group G]
    (F : Bool → Subgroup G) (e : Bool → ℕ) (hpos : ∀ i, 0 < e i)
    (hval : ∀ v : Vertex F, Nat.card ((graph F).neighborSet v) = 2^(e v.type)+1)
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) (n+1) a)
    (hodd : Odd (Nat.card (pathStabilizer F p))) : ¬ RightRegular (A := G) p := by
  intro hr
  let D : Set (Vertex F) := {z | Theory.GroupAction.CubicTree.Forward p z}
  have hD := exits_card F e hval p
  obtain ⟨z,hz⟩ : D.Nonempty := Set.nonempty_of_ncard_ne_zero (by
    rw [←Nat.card_coe_set_eq]
    change Nat.card {z // Theory.GroupAction.CubicTree.Forward p z} ≠ 0
    rw [hD]; positivity)
  have hact : GraphAction (graph F) G :=
    ⟨fun g _ _ hadj => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj hadj⟩
  have he : MulAction.orbit (pathStabilizer F p) z = D := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g,rfl⟩
      exact forward_smul_of_fixes hact p g g.property hz
    · intro w hw
      obtain ⟨g,hg,hgw⟩ := hr z w hz hw
      exact ⟨⟨g,hg⟩,hgw⟩
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (pathStabilizer F p) z)
  rw [Nat.card_prod,he] at hc
  have hDeven : Even (Nat.card D) := by
    change Even (Nat.card {z // Theory.GroupAction.CubicTree.Forward p z})
    rw [hD]
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hpos p.endpoint.type))
    rw [hj,pow_succ]
    exact ⟨2^j,by omega⟩
  exact (Nat.not_even_iff_odd.mpr hodd) (hc ▸ hDeven.mul_right _)

/-- Five-walk transitivity and odd longer fixers determine regularity
when both forward valences are positive powers of two. -/
theorem two_power_graph_regular_iff_of_five_transitive
    {G : Type*} [Group G] (F : Bool → Subgroup G) (e : Bool → ℕ) (hpos : ∀ i, 0 < e i)
    (hval : ∀ v : Vertex F, Nat.card ((graph F).neighborSet v) = 2^(e v.type)+1)
    (hfive : ∀ a : Vertex F, RootPathTransitive (graph F) G a 5)
    (hodd : ∀ {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) n a),
      p.Nonbacktracking → 5 ≤ n → Odd (Nat.card (pathStabilizer F p)))
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) n a) (hp : p.Nonbacktracking) :
    Regular (A := G) p ↔ n ≤ 4 := by
  constructor
  · intro hr
    by_contra hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact not_right_regular_of_odd F e hpos hval p (hodd p hp (by omega)) hr.2
  · intro hn
    apply regular_of_all_rightRegular (fun v q hq => ?_) p hp
    exact right_regular_of_root_transitive F
      ((hfive v).mono (two_neighbors F e hval) (by omega : n+1 ≤ 5)) q hq


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
