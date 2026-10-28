module
public import Theory.GroupTheory.TwoInvolutionClassOrder
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Generation from two involution centralizers and Sylow fusion

Let `P` be a Sylow 2-subgroup of a finite group `G`, contained in `L`.
Suppose two nonconjugate involutions `z, v` in `P` have their full ambient
centralizers in `L`, and every involution in `P` is conjugate to `z` or `v`
by an element of `L`. Then `L = G`.

Sylow conjugacy inside `L` extends the supplied conjugators to all its
involutions. Ambient Sylow conjugacy gives the two classes in `G`, while
ambient nonconjugacy separates the internal classes. The full-centralizer
generation theorem from Thompson's mixed-pair count then applies.

Source motivation: Parrott (1972), p. 684, the application of Thompson's
order formula; the counting argument is in `TwoInvolutionClassOrder`.
-/

namespace Theory.GroupTheory.TwoInvolutionClassGeneration

variable {G : Type*} [Group G]

private theorem orderOf_isConj {a b : G} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq a).symm

/-- Full centralizers of two nonconjugate involutions generate an overgroup of
 a Sylow 2-subgroup when conjugators in that overgroup fuse every Sylow
 involution to one of the two representatives. The conjugation equations
 explicitly use elements of `L` and are oriented from the representatives. -/
public theorem eq_top_of_centralizers_le [Finite G] (P : Sylow 2 G) (L : Subgroup G)
    (hPL : (P : Subgroup G) ≤ L) (z v : G)
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (hzP : z ∈ P) (hvP : v ∈ P)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ L)
    (hCv : Subgroup.centralizer ({v} : Set G) ≤ L)
    (hfusion : ∀ u : G, u ∈ P → orderOf u = 2 →
      ∃ l : L, MulAut.conj (l : G) z = u ∨ MulAut.conj (l : G) v = u) :
    L = ⊤ := by
  let zL : L := ⟨z, hPL hzP⟩
  let vL : L := ⟨v, hPL hvP⟩
  have hclassesL (a : L) (ha : orderOf a = 2) : IsConj zL a ∨ IsConj vL a := by
    obtain ⟨u, hau⟩ := (P.subtype hPL).exists_isConj_of_orderOf_eq_prime_pow
      (n := 1) (by simpa only [pow_one] using ha)
    have huP : ((u : L) : G) ∈ P := u.property
    have hu2 : orderOf ((u : L) : G) = 2 :=
      (Subgroup.orderOf_coe (u : L)).trans ((orderOf_isConj hau).symm.trans ha)
    obtain ⟨l, hzu | hvu⟩ := hfusion u huP hu2
    · have hzuL : IsConj zL (u : L) :=
        isConj_iff.mpr ⟨l, Subtype.ext hzu⟩
      exact Or.inl (hzuL.trans hau.symm)
    · have hvuL : IsConj vL (u : L) :=
        isConj_iff.mpr ⟨l, Subtype.ext hvu⟩
      exact Or.inr (hvuL.trans hau.symm)
  have hclasses (a : G) (ha : orderOf a = 2) : IsConj z a ∨ IsConj v a := by
    obtain ⟨u, hau⟩ := P.exists_isConj_of_orderOf_eq_prime_pow
      (n := 1) (by simpa only [pow_one] using ha)
    let uL : L := ⟨u, hPL u.property⟩
    have hu2 : orderOf uL = 2 :=
      (Subgroup.orderOf_coe uL).symm.trans ((orderOf_isConj hau).symm.trans ha)
    rcases hclassesL uL hu2 with hzu | hvu
    · exact Or.inl ((L.subtype.map_isConj hzu).trans hau.symm)
    · exact Or.inr ((L.subtype.map_isConj hvu).trans hau.symm)
  apply TwoInvolutionClassOrder.eq_top_of_centralizers_le L z v hz hv hn hclasses
    (hPL hzP) (hPL hvP) hCz hCv
  · intro a
    refine ⟨fun h => L.subtype.map_isConj h, fun h => ?_⟩
    have ha : orderOf a = 2 :=
      (Subgroup.orderOf_coe a).symm.trans ((orderOf_isConj h).symm.trans hz)
    rcases hclassesL a ha with hza | hva
    · exact hza
    · exact (hn (h.trans (L.subtype.map_isConj hva).symm)).elim
  · intro a
    refine ⟨fun h => L.subtype.map_isConj h, fun h => ?_⟩
    have ha : orderOf a = 2 :=
      (Subgroup.orderOf_coe a).symm.trans ((orderOf_isConj h).symm.trans hv)
    rcases hclassesL a ha with hza | hva
    · exact (hn ((L.subtype.map_isConj hza).trans h.symm)).elim
    · exact hva

end Theory.GroupTheory.TwoInvolutionClassGeneration
