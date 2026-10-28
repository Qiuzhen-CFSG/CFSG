module
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Tactic.FinCases
/-!
# Recognition of a marked six-cycle from its six edges

Two distinct neighbors exhaust a neighbor set of cardinality two. Hence
six distinct vertices with the cyclic six edges give a graph isomorphism
whenever they exhaust the vertex set and every vertex has degree two.
The equivalence retains all six specified vertex labels.
-/

public section
namespace SimpleGraph.SixCycle
variable {X:Type*} (Γ:SimpleGraph X)
theorem neighbors_pair {x y z:X} (hc:Nat.card (Γ.neighborSet x)=2)
    (hy:Γ.Adj x y) (hz:Γ.Adj x z) (hne:y≠z) (w:X) :
    Γ.Adj x w ↔ w=y ∨ w=z := by
  constructor
  · intro hw
    obtain ⟨a,_,ha⟩ := (Nat.card_eq_two_iff' (⟨y,hy⟩:Γ.neighborSet x)).mp hc
    by_cases hwy:w=y
    · exact Or.inl hwy
    · exact Or.inr (congrArg Subtype.val
        ((ha ⟨w,hw⟩ (fun h=>hwy (congrArg Subtype.val h))).trans
          (ha ⟨z,hz⟩ (fun h=>hne (congrArg Subtype.val h).symm)).symm))
  · rintro (rfl|rfl) <;> assumption

theorem equiv_of_edges [Finite X] (hc:Nat.card X=6) (v:Fin 6→X)
    (hi:Function.Injective v) (hd:∀x,Nat.card (Γ.neighborSet x)=2)
    (he:∀i,Γ.Adj (v i) (v (i+1))) :
    ∃e:cycleGraph 6≃gΓ,∀i,e i=v i := by
  have hs:Function.Surjective v := (hi.bijective_of_nat_card_le (by simpa only [Nat.card_fin] using hc.le)).2
  let e:Fin 6≃X:=Equiv.ofBijective v ⟨hi,hs⟩
  refine ⟨{toEquiv:=e,map_rel_iff':=?_},fun _=>rfl⟩
  intro i j
  have hp:Γ.Adj (v i) (v (i-1)) := by
    simpa only [sub_add_cancel] using (he (i-1)).symm
  have hn:v (i-1)≠v (i+1) := by
    intro hh
    have hh':i-1=i+1:=hi hh
    have hsmall:∀i:Fin 6,i-1≠i+1 := by decide
    exact hsmall i hh'
  change Γ.Adj (v i) (v j) ↔ _
  rw [neighbors_pair Γ (hd _) hp (he i) hn]
  simp only [hi.eq_iff]
  rw [←mem_neighborSet,cycleGraph_neighborSet]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
end SimpleGraph.SixCycle
