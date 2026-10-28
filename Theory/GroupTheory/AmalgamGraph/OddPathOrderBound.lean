module
public import Theory.GroupTheory.AmalgamGraph.PathSupplement

/-!
# Upper orders from an odd path fixer

A two-subgroup fixing an edge acts freely on the orbit of a nonbacktracking
path through that edge when the path fixer has odd order. Counting paths
with that fixed first edge bounds the subgroup by the alternating product
of the forward valences. Only vertex stabilizers are finite.

Source: the path-counting argument in DGS85, Groups and Graphs,
(3.4) and (12.7)--(12.9), printed pp.74,184--187.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
namespace Subgroup.CosetGeometry.RankTwo
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


/-- An odd path fixer bounds every two-subgroup of its initial edge by the
number of continuations of that edge. No transitivity premise is needed. -/
theorem two_subgroup_card_le_forwardCount_of_odd_fixer
    {G : Type*} [Group G] (F : Bool → Subgroup G) [∀ i, Finite (F i)]
    (degree : Bool → ℕ)
    (hval : ∀ v : Vertex F, Nat.card ((graph F).neighborSet v) = degree v.type)
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) (n+1) a)
    (hp : p.Nonbacktracking) (T : Subgroup G)
    (hT : T ≤ stabilizer F a ⊓ stabilizer F (p.1 : Vertex F))
    (hTp : IsPGroup 2 T) (hodd : Odd (Nat.card (pathStabilizer F p))) :
    Nat.card T ≤ BasedWalk.forwardCount degree n (p.1 : Vertex F).type := by
  let : MulAction (stabilizer F a) (BasedWalk (graph F) (n+1) a) := pathAction F (n+1) a
  let b := p.1
  let Y := {q : BasedWalk (graph F) (n+1) a // q.Nonbacktracking ∧ q.1 = b}
  let : ∀ v : Vertex F, Finite ((graph F).neighborSet v) :=
    fun v => Theory.GroupTheory.AmalgamGraph.finite_neighbors F v
  let : Finite Y := Finite.of_equiv (BasedWalk.Forward (graph F) n a b)
    (edgePathsEquiv (graph F) n a b).symm
  let : Finite T := Finite.of_injective (inclusion (hT.trans inf_le_left)) (inclusion_injective _)
  let : Finite (pathStabilizer F p) := Finite.of_injective
    (inclusion (pathStabilizer_le F p)) (inclusion_injective _)
  have hflip : ∀ {v w : Vertex F}, (graph F).Adj v w → w.type = !v.type := by
    intro v w hvw
    exact Bool.eq_not_iff.mpr hvw.1.symm
  have hY : Nat.card Y = BasedWalk.forwardCount degree n (b : Vertex F).type := by
    rw [Nat.card_congr (edgePathsEquiv (graph F) n a b),
      card_forward (graph F) (fun v => v.type) degree hflip hval n a b b.property]
  let j : T →* stabilizer F a := inclusion (hT.trans inf_le_left)
  let f : T → Y := fun x => ⟨j x • p,
    (nonbacktracking_smul_path F (j x) p).mpr hp,by
      apply Subtype.ext
      change ((actPath F (j x) p).1 : Vertex F) = b
      rw [first_smul]
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
      simpa only [Subgroup.orderOf_mk] using _root_.orderOf_dvd_natCard
        (⟨_,hfix⟩ : pathStabilizer F p)
    apply Subtype.ext
    exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_right.pow_right k) ho hd))
  exact (Nat.card_le_card_of_injective f hf).trans_eq hY

end Subgroup.CosetGeometry.RankTwo
