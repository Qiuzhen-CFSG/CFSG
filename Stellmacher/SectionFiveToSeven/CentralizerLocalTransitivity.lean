module
public import Stellmacher.SectionFiveToSeven.Result7_2
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts


/-!
# Triviality from two adjacent local centralizer actions

In a Section Seven coset graph, suppose an element fixes both endpoints of
an edge and its centralizer in each endpoint stabilizer acts transitively
on the corresponding neighborhood. Then the element is the identity.
No assumption on the ambient group beyond the actual Section Seven context
is added, and the graph action convention is retained.

The union of the two full-centralizer vertex orbits contains the edge and
is closed under taking neighbors: conjugate back to the given endpoint,
use its local centralizer transitivity, then conjugate forward. Connectedness
puts every vertex in those two orbits. The element fixes both orbits because
it fixes the initial edge and commutes with their transporters. Faithfulness
from (7.2) therefore makes it trivial.

Source: Stellmacher (7.1)--(7.2), and their use in the final local-centralizer
argument before (10.1)(16), Journal of Algebra 190 (1997), printed p.64.
-/

namespace Stellmacher.SectionsFiveToSeven
open CosetGraphContext SevenSix
universe u
public theorem element_eq_one_of_adjacent_centralizer_transitivity
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2)
    (a b : Γ.Vertex) (hab : Γ.adjacent a b)
    (x : G) (hx : x ∈ stabilizer Γ a ⊓ stabilizer Γ b)
    (ha : IsActionTransitiveOn Γ
      (stabilizer Γ a ⊓ Subgroup.centralizer ({x}:Set G)) (neighborhood Γ a))
    (hb : IsActionTransitiveOn Γ
      (stabilizer Γ b ⊓ Subgroup.centralizer ({x}:Set G)) (neighborhood Γ b)) :
    x=1 := by
  let C := Subgroup.centralizer ({x}:Set G)
  let covered : Γ.Vertex → Prop := fun vertex =>
    (∃ g:C, Γ.act (g:G) a=vertex) ∨ (∃ g:C, Γ.act (g:G) b=vertex)
  have hstep (root partner : Γ.Vertex) (hedge : Γ.adjacent root partner)
      (htrans : IsActionTransitiveOn Γ (stabilizer Γ root ⊓ C) (neighborhood Γ root))
      (g:C) (neighbor:Γ.Vertex) (hadj : Γ.adjacent (Γ.act (g:G) root) neighbor) :
      ∃ k:C, Γ.act (k:G) partner=neighbor := by
    have hback := adjacent_act Γ (g:G)⁻¹ hadj
    rw [←Γ.act_mul,mul_inv_cancel,Γ.act_one] at hback
    obtain ⟨k,hmove⟩ := htrans
      ((mem_neighborhood_iff_adjacent Γ).mpr hedge)
      ((mem_neighborhood_iff_adjacent Γ).mpr hback)
    refine ⟨⟨(k:G)*(g:G),C.mul_mem k.property.2 g.property⟩,?_⟩
    change Γ.act ((k:G)*(g:G)) partner=neighbor
    rw [Γ.act_mul,hmove,←Γ.act_mul,inv_mul_cancel,Γ.act_one]
  have hclosed (vertex neighbor:Γ.Vertex) (hv : covered vertex)
      (hadj : Γ.adjacent vertex neighbor) : covered neighbor := by
    rcases hv with ⟨g,rfl⟩ | ⟨g,rfl⟩
    · exact Or.inr (hstep a b hab ha g neighbor hadj)
    · exact Or.inl (hstep b a (Γ.adjacent_symm hab) hb g neighbor hadj)
  have hall (vertex:Γ.Vertex) : covered vertex := by
    obtain ⟨n,f,hstart,hend,hpath⟩ := (lemma_seven_one h7 Γ).connected a vertex
    have hf : ∀ i : Fin (n+1), covered (f i) := by
      apply Fin.induction
      · rw [hstart]
        exact Or.inl ⟨1,Γ.act_one a⟩
      · intro i hi
        exact hclosed _ _ hi (hpath i)
    rw [←hend]
    exact hf _
  have hfix (root:Γ.Vertex) (hroot : Γ.act x root=root) (g:C) :
      Γ.act x (Γ.act (g:G) root)=Γ.act (g:G) root := by
    have hcomm : x*(g:G)=(g:G)*x :=
      Subgroup.mem_centralizer_iff.mp g.property x (by simp)
    rw [←Γ.act_mul,←hcomm,Γ.act_mul,hroot]
  have hxa : Γ.act x a=a := (Set.ext_iff.mp (Γ.stabilizer_def a) x).mp hx.1
  have hxb : Γ.act x b=b := (Set.ext_iff.mp (Γ.stabilizer_def b) x).mp hx.2
  have hkernel : x ∈ Γ.actionKernel := by
    rw [Γ.actionKernel_def]
    intro vertex
    rcases hall vertex with ⟨g,rfl⟩ | ⟨g,rfl⟩
    · exact hfix a hxa g
    · exact hfix b hxb g
  simpa only [lemma_seven_two h7 Γ,Subgroup.mem_bot] using hkernel
end Stellmacher.SectionsFiveToSeven
