module
public import Stellmacher.SectionNine.CubicTwoNeighborKernel
public import Stellmacher.SectionNine.CubicCoreIntersection

/-!
# A cubic edge and an escaping actor generate the vertex stabilizer

At a vertex with local SL₂(2) quotient, let n and m be distinct neighbors.
An actor in the vertex-m edge stabilizer but outside the vertex two-core,
together with the vertex-n edge stabilizer, generates the whole vertex
stabilizer. Only the genuine Section Seven graph hypotheses and local model
are used; there is no critical-path or module-order hypothesis.

If the actor belonged to the other edge, it would fix both neighbors and
hence lie in the cubic local kernel, contrary to the assumed core escape.
The other edge has index three. The relative-index tower then forces any
strict enlargement inside the vertex stabilizer to be the whole stabilizer.

This is the local generation input for Stellmacher (9.6), Journal of
Algebra190 (1997), printed p.53, when applying the (9.4) neighborhood
comparison. The consumer supplies the actual neighboring vertices and actor.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem cubic_edge_sup_zpowers_eq_stabilizer
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (vertex n m : Γ.Vertex)
    (hn : Γ.adjacent vertex n) (hm : Γ.adjacent vertex m) (hne : n ≠ m)
    (hmodel : QuotientIsModel (GAt Γ vertex) (QAt Γ vertex) SL2Two)
    (actor : G) (hactor : actor ∈ GAt Γ vertex ⊓ GAt Γ m)
    (hout : actor ∉ QAt Γ vertex) :
    (GAt Γ vertex ⊓ GAt Γ n) ⊔ Subgroup.zpowers actor = GAt Γ vertex := by
  let edge := GAt Γ vertex ⊓ GAt Γ n
  let J := edge ⊔ Subgroup.zpowers actor
  have hJG : J ≤ GAt Γ vertex := sup_le inf_le_left (Subgroup.zpowers_le.mpr hactor.1)
  have hnot : actor ∉ edge := by
    intro he
    apply hout
    exact cubic_mem_core_of_fix_two_neighbors Γ vertex n m
      (cubic_local_action_of_sl2Two_quotient Γ h7 vertex hmodel) hn hm hne
      ⟨actor,hactor.1⟩
      ((Set.ext_iff.mp (Γ.stabilizer_def n) actor).mp he.2)
      ((Set.ext_iff.mp (Γ.stabilizer_def m) actor).mp hactor.2)
  have hindex : edge.relIndex (GAt Γ vertex) = 3 := cubic_edge_index_three h7 Γ hn hmodel
  have htower := Subgroup.relIndex_mul_relIndex edge J (GAt Γ vertex) le_sup_left hJG
  rw [hindex] at htower
  have hdvd : edge.relIndex J ∣ 3 := ⟨_,htower.symm⟩
  rcases (Nat.prime_three.eq_one_or_self_of_dvd _ hdvd) with hone | hthree
  · exact (hnot ((Subgroup.relIndex_eq_one.mp hone)
      (show actor ∈ J from (show Subgroup.zpowers actor ≤ J from le_sup_right)
        (Subgroup.mem_zpowers actor)))).elim
  · rw [hthree] at htower
    have hone : J.relIndex (GAt Γ vertex) = 1 := by omega
    exact le_antisymm hJG (Subgroup.relIndex_eq_one.mp hone)

end Stellmacher.SectionNine
