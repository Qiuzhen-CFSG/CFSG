module
public import Theory.GroupTheory.AmalgamGraph.OddPathOrderBound
import all Theory.GroupTheory.AmalgamGraph.OddPathOrderBound

/-!
# Transitivity at the exact odd-fixer order bound

A two-subgroup of an edge acts freely on the orbit of a path whose fixer
has odd order. If its order is the number of continuations of that edge,
the orbit is the whole set. Local transitivity aligns the first edge and
therefore gives transitivity on all paths from the original root.

Source: DGS85, Groups and Graphs, (3.4) and (12.9), pp.74,186--187.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
namespace Subgroup.CosetGeometry.RankTwo

private theorem edge_transitive_of_odd {G : Type*} [Group G]
    (F : Bool → Subgroup G) [∀ i, Finite (F i)]
    (degree : Bool → ℕ) (hval : ∀ v : Vertex F,
      Nat.card ((graph F).neighborSet v) = degree v.type) {n : ℕ}
    {a : Vertex F} (b : (graph F).neighborSet a)
    (T : Subgroup G) (hT : T ≤ stabilizer F a ⊓ stabilizer F b)
    (hTc : Nat.card T = BasedWalk.forwardCount degree n (b : Vertex F).type) (hTp : IsPGroup 2 T)
    (p : BasedWalk (graph F) (n+1) a) (hp : p.Nonbacktracking)
    (hpb : p.1 = b) (hodd : Odd (Nat.card (pathStabilizer F p))) :
    ∀ q : BasedWalk (graph F) (n+1) a, q.Nonbacktracking →
      q.1 = b → ∃ g ∈ T, p.vertices.map (g • ·) = q.vertices := by
  classical
  let : MulAction (stabilizer F a) (BasedWalk (graph F) (n+1) a) := pathAction F (n+1) a
  intro q hq hqb
  let Y := {p : BasedWalk (graph F) (n+1) a // p.Nonbacktracking ∧ p.1 = b}
  let : ∀ v : Vertex F, Finite ((graph F).neighborSet v) :=
    fun v => Theory.GroupTheory.AmalgamGraph.finite_neighbors F v
  have hflip : ∀ {v w : Vertex F}, (graph F).Adj v w → w.type = !v.type := by
    intro v w hvw
    exact Bool.eq_not_iff.mpr hvw.1.symm
  have hY : Nat.card Y = BasedWalk.forwardCount degree n (b : Vertex F).type := by
    rw [Nat.card_congr (edgePathsEquiv (graph F) n a b),
      card_forward (graph F) (fun v => v.type) degree hflip hval n a b b.property]
  let : Finite Y := Finite.of_equiv (BasedWalk.Forward (graph F) n a b)
    (edgePathsEquiv (graph F) n a b).symm
  let : Finite T := Finite.of_injective (inclusion (hT.trans inf_le_left)) (inclusion_injective _)
  let : Finite (pathStabilizer F p) := Finite.of_injective
    (inclusion (pathStabilizer_le F p)) (inclusion_injective _)
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
      simpa only [Subgroup.orderOf_mk] using _root_.orderOf_dvd_natCard
        (⟨_,hfix⟩ : pathStabilizer F p)
    apply Subtype.ext
    exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_right.pow_right k) ho hd))
  obtain ⟨x,hx⟩ := (hf.bijective_of_nat_card_le (by omega : Nat.card Y ≤ Nat.card T)).surjective ⟨q,hq,hqb⟩
  exact ⟨x,x.property,(vertices_smul_path F (j x) p).symm.trans
    (congrArg BasedWalk.vertices (congrArg Subtype.val hx))⟩

/-- A two-subgroup of the first edge whose order equals the number of
continuations acts transitively on all paths from that root when one fixer is odd. -/
theorem rootPathTransitive_of_odd_fixer_and_card {G : Type*} [Group G]
    (F : Bool → Subgroup G) [∀ i, Finite (F i)]
    (degree : Bool → ℕ) (hval : ∀ v : Vertex F,
      Nat.card ((graph F).neighborSet v) = degree v.type) {n : ℕ}
    {a : Vertex F} (p : BasedWalk (graph F) (n+1) a) (hp : p.Nonbacktracking)
    (T : Subgroup G) (hT : T ≤ stabilizer F a ⊓ stabilizer F (p.1 : Vertex F))
    (hTc : Nat.card T = BasedWalk.forwardCount degree n (p.1 : Vertex F).type)
    (hTp : IsPGroup 2 T) (hodd : Odd (Nat.card (pathStabilizer F p))) :
    RootPathTransitive (graph F) G a (n+1) := by
  let : MulAction (stabilizer F a) (BasedWalk (graph F) (n+1) a) := pathAction F (n+1) a
  have hreach : ∀ r : BasedWalk (graph F) (n+1) a, r.Nonbacktracking →
      ∃ g : stabilizer F a, g • p = r := by
    intro r hr
    obtain ⟨g,hga,hg⟩ := locally_transitive F r.1.property p.1.property
    let g' : stabilizer F a := ⟨g,hga⟩
    let r' := g' • r
    have hr' : r'.Nonbacktracking := (nonbacktracking_smul_path F g' r).mpr hr
    have hfirst : r'.1 = p.1 := Subtype.ext ((first_smul F r g').trans hg)
    obtain ⟨t,ht,htr⟩ := edge_transitive_of_odd F degree hval p.1 T hT hTc hTp
      p hp rfl hodd r' hr' hfirst
    let t' : stabilizer F a := ⟨t,(hT ht).1⟩
    have htp : t' • p = r' := BasedWalk.vertices_injective (n+1) a
      ((vertices_smul_path F t' p).trans htr)
    refine ⟨g'⁻¹*t',?_⟩
    rw [mul_smul,htp]
    exact inv_smul_smul g' r
  intro r s hr hs
  obtain ⟨u,hu⟩ := hreach r hr
  obtain ⟨v,hv⟩ := hreach s hs
  have he : (v*u⁻¹) • r = s := by
    rw [mul_smul,←hu,inv_smul_smul,hv]
  exact ⟨(v*u⁻¹ : stabilizer F a), (v*u⁻¹).property,
    (vertices_smul_path F (v*u⁻¹) r).symm.trans (congrArg BasedWalk.vertices he)⟩

end Subgroup.CosetGeometry.RankTwo
