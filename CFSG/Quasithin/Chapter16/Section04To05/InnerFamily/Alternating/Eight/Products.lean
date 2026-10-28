module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Eight.MarkedSpace
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Intersections

/-!
# The A₈ subset-product exclusions

For each marked involution c = zˣ, place A in an overgroup Y of index two
over X = (L⟨z⟩)ˣ. Source (**) puts every other marked generator outside X.
Thus an even product avoiding c is in X; independence makes it distinct
from both 1 and c. Source (**) excludes this product and its product with c.
An even nonempty subset of five indices omits an index, and an odd subset
of size at least three is obtained by inserting an index into an even one.
This proves all exclusions of weights two, three, four and five.

The geometric placements remain explicit inputs. No product exclusion is
assumed. Source: Aschbacher–Smith, proof of 16.4.9(2), printed p.1192.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.AlternatingEight
open Subgroup
variable {G : Type*} [Group G] {L : Subgroup G} {z r : G}

/-- The actual conjugate-component placements required by the source proof. -/
structure Placements (F : MarkedEmbedding L z r) where
  conjugator : Fin 5 → G
  center : ∀ i, MulAut.conj (conjugator i) z = F.mark i
  overgroup : Fin 5 → Subgroup G
  contains : ∀ i, F.subgroup ≤ overgroup i
  component_le : ∀ i, (L ⊔ zpowers z).conjBy (conjugator i) ≤ overgroup i
  index : ∀ i, ((L ⊔ zpowers z).conjBy (conjugator i)).relIndex (overgroup i) = 2

variable [Finite G] {T : Sylow 2 G}

namespace MarkedEmbedding

private theorem word_mem_iff_even (F : MarkedEmbedding L z r)
    (h : StandardSetup T z L) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (hr : IsConj z r) (P : Placements F) (i : Fin 5)
    (s : Finset (Fin 5)) (hi : i ∉ s) :
    F.hom (word s) ∈ (L ⊔ zpowers z).conjBy (P.conjugator i) ↔ s.card % 2 = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hij : i ≠ j := fun he => hi (by simp [he])
    have his : i ∉ s := fun hh => hi (Finset.mem_insert_of_mem hh)
    have hjX : F.mark j ∉ (L ⊔ zpowers z).conjBy (P.conjugator i) := by
      intro hjX
      have he := h.conjugate_eq_of_mem_conjugate_component_zpowers hsmall hempty hdis
        (P.conjugator i) (F.mark_isConj hr j) hjX
      rw [P.center] at he
      exact hij (F.mark_injective he).symm
    let hm := ((L ⊔ zpowers z).conjBy (P.conjugator i)).subgroupOf (P.overgroup i)
    have he := hm.mul_mem_iff_of_index_two (P.index i)
      (a := ⟨F.mark j, P.contains i ⟨word {j}, rfl⟩⟩)
      (b := ⟨F.hom (word s), P.contains i ⟨word s, rfl⟩⟩)
    change (F.mark j * F.hom (word s) ∈ (L ⊔ zpowers z).conjBy (P.conjugator i)) ↔
      (F.mark j ∈ (L ⊔ zpowers z).conjBy (P.conjugator i) ↔
        F.hom (word s) ∈ (L ⊔ zpowers z).conjBy (P.conjugator i)) at he
    rw [word_insert hj, map_mul, Finset.card_insert_of_notMem hj]
    change (F.mark j * F.hom (word s) ∈ (L ⊔ zpowers z).conjBy (P.conjugator i)) ↔ (s.card + 1) % 2 = 0
    rw [he, iff_false_left hjX, ih his]
    omega

/-- An even nonempty product avoiding one mark, and its product with that
mark, are both excluded by (**). This supplies weights two through five. -/
theorem even_products_not_conjugate (F : MarkedEmbedding L z r)
    (h : StandardSetup T z L) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (hr : IsConj z r) (P : Placements F) (i : Fin 5)
    (s : Finset (Fin 5)) (hi : i ∉ s) (hs : s.Nonempty) (heven : s.card % 2 = 0) :
    ¬ IsConj z (F.hom (word s)) ∧ ¬ IsConj z (F.hom (word s) * F.mark i) := by
  have hu1 : F.hom (word s) ≠ 1 := by
    intro he
    have hh : s = ∅ := F.products_injective (by simpa using he)
    exact hs.ne_empty hh
  have hui : F.hom (word s) ≠ MulAut.conj (P.conjugator i) z := by
    rw [P.center]
    intro he
    have hh : s = {i} := F.products_injective he
    exact hi (hh ▸ Finset.mem_singleton_self i)
  simpa only [P.center] using h.paired_products_not_conjugate hsmall hempty hdis
    (P.conjugator i) ((F.word_mem_iff_even h hsmall hempty hdis hr P i s hi).mpr heven) hu1 hui

/-- The ambient class of z contains precisely the products of weight one. -/
theorem word_isConj_iff (F : MarkedEmbedding L z r)
    (h : StandardSetup T z L) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (hr : IsConj z r) (P : Placements F) (s : Finset (Fin 5)) :
    IsConj z (F.hom (word s)) ↔ s.card = 1 := by
  constructor
  · intro hc
    have hs0 : s.Nonempty := by
      by_contra hh
      have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
      have hz : z = 1 := by simpa [he] using hc
      have hz2 := h.involution
      simp [hz] at hz2
    by_contra hs1
    have hs2 : 2 ≤ s.card := by have := hs0.card_pos; omega
    by_cases heven : s.card % 2 = 0
    · have hex : ∃ i : Fin 5, i ∉ s := by
        by_contra! hall
        have he : s = Finset.univ := Finset.eq_univ_of_forall hall
        simp [he] at heven
      obtain ⟨i, hi⟩ := hex
      exact (F.even_products_not_conjugate h hsmall hempty hdis hr P i s hi hs0 heven).1 hc
    · obtain ⟨i, hi⟩ := hs0
      have herase := Finset.card_erase_of_mem hi
      have hne : (s.erase i).Nonempty := Finset.card_pos.mp (by omega)
      have he : (s.erase i).card % 2 = 0 := by omega
      have hn := (F.even_products_not_conjugate h hsmall hempty hdis hr P i (s.erase i)
        (Finset.notMem_erase i s) hne he).2
      apply hn
      have hw : F.hom (word s) = F.hom (word (s.erase i)) * F.mark i := by
        conv_lhs => rw [← Finset.insert_erase hi, word_insert (Finset.notMem_erase i s)]
        rw [mul_comm, map_mul]
        rfl
      rwa [← hw]
  · intro hs
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
    exact F.mark_isConj hr i

/-- Source zᴳ ∩ A = α, first with α as the five marked generators. -/
theorem class_intersection_eq_marks (F : MarkedEmbedding L z r)
    (h : StandardSetup T z L) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (hr : IsConj z r) (P : Placements F) :
    {a : G | IsConj z a} ∩ (F.subgroup : Set G) = Set.range F.mark := by
  ext a
  constructor
  · rintro ⟨hc, ha⟩
    obtain ⟨s, rfl⟩ := (F.mem_subgroup_iff a).mp ha
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp ((F.word_isConj_iff h hsmall hempty hdis hr P s).mp hc)
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨F.mark_isConj hr i, ⟨word {i}, rfl⟩⟩

/-- The marked set is precisely the source's {z} ∪ (rᴸ ∩ A). -/
theorem marks_eq_source_set (F : MarkedEmbedding L z r)
    (h : StandardSetup T z L) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (hr : IsConj z r) (P : Placements F) :
    Set.range F.mark = {z} ∪ ({a : G | ∃ l ∈ L, MulAut.conj l r = a} ∩ (F.subgroup : Set G)) := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i = 4
    · left
      simpa only [Set.mem_singleton_iff, mark, hi] using F.central
    · exact Or.inr ⟨F.conjugates i hi, ⟨word {i}, rfl⟩⟩
  · rintro (hz | ⟨⟨l, _, hl⟩, ha⟩)
    · exact ⟨4, F.central.trans (Set.mem_singleton_iff.mp hz).symm⟩
    · rw [← F.class_intersection_eq_marks h hsmall hempty hdis hr P]
      exact ⟨hr.trans (isConj_iff.mpr ⟨l, hl⟩), ha⟩

end MarkedEmbedding
end CFSG.Quasithin.Chapter16.Intersections.AlternatingEight
