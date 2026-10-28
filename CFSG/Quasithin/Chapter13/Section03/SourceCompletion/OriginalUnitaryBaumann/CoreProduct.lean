module
public import Theory.GroupTheory.TwoConjugateCoreProduct
public import Theory.Representation.G2BinaryPointGeneration
public import Theory.Representation.G2BinaryPointFlag

/-!
# The unitary core product from two moving root eights

The checked opposite root eights generate G₂(2). Lift their conjugator
through the literal action quotient. Their centralizer indices multiply
to at most 64, the order of the natural module, so the core splits as
V times its component centralizer. The moving conjugate centralizes this
whole fixed factor. No core product or splitting is assumed.

Source: Aschbacher--Smith 13.3.10(2), printed p.888. The original flag
application is OriginalUnitaryNoncentrality.CoreProduct.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G] [Finite G]
/-- The two root eights force the page-888 direct core product, with the
same conjugate actor centralizing the full fixed factor. -/
theorem unitary_core_product_of_moving_eight
    (Q V L A : Subgroup G) [Q.Normal]
    (q : G →* Atlas.G2.Model F) (hq : Function.Surjective q) (hker : q.ker = Q)
    (himage : A.map q = Atlas.G2.BinaryCore.elementary)
    (hVQ : V ≤ Q) (hc : V ≤ centralizer (Q : Set G))
    (hcomm : ⁅Q,L⁆ ≤ V) (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hcard : Nat.card V = 64) (hi : (centralizer (A : Set G)).relIndex Q ≤ 8) :
    Q = V ⊔ (Q ⊓ centralizer (L : Set G)) ∧
      Disjoint V (Q ⊓ centralizer (L : Set G)) ∧
      Q ⊓ centralizer (L : Set G) ≤ centralizer (A : Set G) := by
  obtain ⟨a,_,hgen⟩ := Atlas.G2.Natural.BinaryPointGeneration.exists_residual_conjugate_generating
  obtain ⟨g,hg⟩ := hq a
  have hm : (A.map (MulAut.conj g).toMonoidHom).map q =
      (A.map q).map (MulAut.conj a).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    ext t
    simp [MulAut.conj_apply,hg]
  have htop : Q ⊔ (A ⊔ A.map (MulAut.conj g).toMonoidHom) = ⊤ := by
    have hh : (A ⊔ A.map (MulAut.conj g).toMonoidHom).map q = ⊤ := by
      rw [Subgroup.map_sup,hm,himage,hgen]
    have hc := congrArg (comap q) hh
    rw [comap_map_eq,hker,comap_top] at hc
    exact sup_comm Q _ |>.trans hc
  exact core_product_of_two_conjugate_indices Q V L A hVQ hc hcomm g htop hfix 8 hi
    (by rw [hcard])
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
