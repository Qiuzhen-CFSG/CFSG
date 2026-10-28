module

public import Theory.GroupTheory.InvolutionTransfer
public import Theory.ElementaryAbelian.Basic

/-!
# Elementary-eight geometry above an index-two subgroup

This interface records the local data in the last exponent-four case of
MacWilliams's argument. An outside involution has elementary centralizer of
order eight and normalizer of order 32. Every elementary eight has either
this normalizer and centralizer size, an order-64 normalizer into which the
distinguished normalizer cannot embed, or an elementary order-16 normalizer.
The distinguished normalizer contains no elementary sixteen.

These are local hypotheses, not a classification assertion. Their intended
use is to exclude fusion of the outside involution into the index-two
subgroup. The transfer lemma below then gives the ambient contradiction.

Source: MacWilliams, Trans. AMS 150 (1970), Case 1.2, Lemma 3 and
(xxii)–(xxv), printed pp.382–385, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup

/-- The three elementary-eight normalizer cases needed for the index-two
extension in the exponent-four argument. No ambient fusion is assumed. -/
public structure ElementaryEightIndexTwoGeometry
    {P : Type*} [Group P] (R : Subgroup P) (t : P) : Prop where
  index_eq_two : R.index = 2
  order_eq_two : orderOf t = 2
  not_mem : t ∉ R
  centralizer_elementary : IsElementaryAbelian 2 (centralizer ({t} : Set P))
  centralizer_card : Nat.card (centralizer ({t} : Set P)) = 8
  normalizer_card :
    Nat.card (normalizer (centralizer ({t} : Set P) : Set P)) = 32
  normalizer_no_sixteen :
    ∀ A : Subgroup (normalizer (centralizer ({t} : Set P) : Set P)),
      IsElementaryAbelian 2 A → Nat.card A ≠ 16
  inside_centralizers : ∀ u : P, u ∈ R → orderOf u = 2 →
    u ∈ center P ∨
      (IsElementaryAbelian 2 (centralizer ({u} : Set P)) ∧
        Nat.card (centralizer ({u} : Set P)) = 16)
  outside_centralizers : ∀ u : P, u ∉ R → orderOf u = 2 →
    Nat.card (centralizer ({u} : Set P)) = 8
  normalizer_cases : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E = 8 →
    (centralizer (E : Set P) = E ∧ Nat.card (normalizer (E : Set P)) = 32) ∨
    (Nat.card (normalizer (E : Set P)) = 64 ∧
      ∀ f : normalizer (centralizer ({t} : Set P) : Set P) →*
          normalizer (E : Set P), ¬ Function.Injective f) ∨
    (IsElementaryAbelian 2 (normalizer (E : Set P)) ∧
      Nat.card (normalizer (E : Set P)) = 16)

namespace ElementaryEightIndexTwoGeometry

/-- The distinguished elementary centralizer is self-centralizing. -/
public theorem centralizer_self
    {P : Type*} [Group P] {R : Subgroup P} {t : P}
    (h : ElementaryEightIndexTwoGeometry R t) :
    centralizer (centralizer ({t} : Set P) : Set P) = centralizer ({t} : Set P) := by
  let E := centralizer ({t} : Set P)
  let : IsElementaryAbelian 2 E := h.centralizer_elementary
  apply le_antisymm
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (hx t (mem_centralizer_singleton_iff.mpr rfl)).symm
  · exact E.le_centralizer

/-- Once fusion into the core is excluded, Thompson transfer contradicts the
existence of this geometry in a group without normal subgroups of index two. -/
public theorem false_of_no_fusion
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    {R : Subgroup S} {t : S} (h : ElementaryEightIndexTwoGeometry R t)
    (hfusion : ∀ u : S, u ∈ R → orderOf u = 2 → ¬ IsConj (t : G) (u : G)) :
    False := by
  obtain ⟨u, htu, hu⟩ := S.exists_isConj_mem_of_index_two hno R h.index_eq_two
    t h.order_eq_two
  have huorder : orderOf u = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp htu
    rw [← Subgroup.orderOf_coe, ← hg]
    change orderOf ((MulAut.conj g) (t : G)) = 2
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, h.order_eq_two]
  exact hfusion u hu huorder htu

end ElementaryEightIndexTwoGeometry
