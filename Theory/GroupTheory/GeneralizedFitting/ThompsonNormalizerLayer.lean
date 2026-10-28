module
public import Theory.GroupTheory.ElementaryThompsonFixedIndex
public import Theory.GroupTheory.GeneralizedFitting.ComponentInvolutionAction

/-!
# Thompson normalization of a component from a large central layer

Suppose the component normalizer has relative index at most two in S.
An elementary subgroup E of the component, centralizing that normalizer
inside S and disjoint from the component centralizer, forces J(S) into
the normalizer when |E| > 2. Otherwise an element of a maximum elementary
subgroup moves the component and fixes no nonidentity element of E.
Elementary replacement bounds this fixed index by two, a contradiction.

Source application: the Suzuki component orbit in Aschbacher--Smith
15.1.21(i), printed pp.1097--1098. Relative index and component normality
are not replaced by ambient normality.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A central elementary layer of order greater than two prevents Thompson
permutation of the component. -/
theorem IsComponent.maxJ_le_relative_normalizer_of_central_elementary
    (H L S E : Subgroup G) (hLH : L ≤ H) (hSH : S ≤ H)
    (hL : IsComponent H (L.subgroupOf H))
    (hi : (normalizer (L : Set G)).relIndex S ≤ 2)
    [IsElementaryAbelian 2 E] (hEL : E ≤ L) (hES : E ≤ S)
    (hEC : E ≤ centralizer (S ⊓ normalizer (L : Set G) : Set G))
    (hd : Disjoint E (centralizer (L : Set G))) (hc : 2 < Nat.card E) :
    elementaryAbelianMaxJ S ≤ normalizer (L : Set G) := by
  let Q := S ⊓ normalizer (L : Set G)
  have hEQ : E ≤ Q := le_inf hES (hEL.trans L.le_normalizer)
  apply sSup_le
  intro A hA
  by_contra hn
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hn
  have hca : centralizer ({a} : Set G) ⊓ E = ⊥ := by
    apply bot_unique
    intro x hx
    by_contra hx1
    have hxn : x ∉ centralizer (L : Set G) := fun hh =>
      hx1 (disjoint_iff_inf_le.mp hd ⟨hx.2,hh⟩)
    apply han
    have haH := hSH (hA.1 ha)
    have hxH := hLH (hEL hx.2)
    have hxn' : (⟨x,hxH⟩ : H) ∉ centralizer (L.subgroupOf H : Set H) := by
      intro hh
      apply hxn
      intro l hl
      exact congrArg Subtype.val (hh ⟨l,hLH hl⟩ hl)
    have hcomm : Commute (⟨a,haH⟩ : H) ⟨x,hxH⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.mp hx.1).symm
    have hn := hL.normalizes_of_noncentral_element ⊥ bot_le ⟨a,haH⟩ ⟨x,hxH⟩
      (hEL hx.2) hxn' (hcomm.map (QuotientGroup.mk' ⊥))
    rwa [← subgroupOf_normalizer_eq hLH] at hn
  have hb := maxElementary_fixedIndex_le_relIndex S Q A E inf_le_left hEQ hEC hA
  have hQ : Q.relIndex A ≤ 2 := by
    apply (relIndex_le_of_le_right hA.1 index_ne_zero_of_finite).trans
    simpa only [Q, inf_relIndex_left] using hi
  have hfix : (centralizer ({a} : Set G)).relIndex E ≤ (centralizer (A : Set G)).relIndex E :=
    relIndex_le_of_le_left (centralizer_le (by simpa using ha)) index_ne_zero_of_finite
  have hcard : (centralizer ({a} : Set G)).relIndex E = Nat.card E := by
    rw [← inf_relIndex_right, hca, relIndex_bot_left]
  have := hfix.trans (hb.1.trans (hb.2.trans hQ))
  omega

end Theory.GroupTheory
