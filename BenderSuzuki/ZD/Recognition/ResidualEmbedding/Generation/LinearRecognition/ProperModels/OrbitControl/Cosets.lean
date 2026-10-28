module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.Foundations
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree.Swapping

/-!
# Distinguished orbit representatives in the two-point stabilizer

Conjugate `t y t` to `z` by a distinguished involution `s`. Product
disconnection puts `s t` in `M ∩ Mᵗ`, with odd order and inverted by `t`.
It carries `z` to `y` by right conjugation. This retains the representative
needed by Proposition 3.6(c), without assuming that the two-point stabilizer
itself has odd order.

Source: GLS, Volume 4, Chapter 2, Lemma 3.2 and Proposition 3.6(c).
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Distinguished orbit representatives lie in the actual inverted set of
`D` and have odd order, even when `D` has even order. -/
public theorem distinguished_exists_odd_inverted_conjugator
    (h : IsProductDisconnected Z M) {z t y : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hy : y ∈ Z) (hyM : y ∈ M) :
    ∃ k : G, k ∈ residualPairStabilizer M t ∧
      rightConjugateElem k t = k⁻¹ ∧ Odd (orderOf k) ∧
      rightConjugateElem z k = y := by
  have ti := (h.involutions t ht).inv_eq_self
  have tt : t * t = 1 := by simpa [pow_two] using (h.involutions t ht).sq_eq_one
  have hcomp s : MulAut.conj t (MulAut.conj s z) = MulAut.conj (t * s) z := by
    simp only [MulAut.conj_apply]; group
  obtain ⟨s, hs, he⟩ := sectionThree_distinguished_conjugator h hz hzM
    (h.invariant t y hy) (fun hm => htM ((h.conjugate_mem_iff y hy hyM t).mp hm))
  have he' : MulAut.conj t (MulAut.conj s z) = y := by
    rw [he]
    simp only [MulAut.conj_apply, ti]
    calc
      t * (t * (y : G) * t) * t = (t * t) * (y : G) * (t * t) := by group
      _ = y := by simp [tt]
  have hm : t * s ∈ M :=
    (h.conjugate_mem_iff z hz hzM _).mp (by rw [← hcomp, he']; exact hyM)
  have hsm : s * t ∈ M := by
    have hh := M.inv_mem hm
    simpa only [mul_inv_rev, ti, (h.involutions s hs).inv_eq_self] using hh
  let k : G := s * t
  have hinv : rightConjugateElem k t = k⁻¹ := by
    simp [k, rightConjugateElem, mul_inv_rev, ti,
      (h.involutions s hs).inv_eq_self, mul_assoc, tt]
  have hkconj : k ∈ rightConjugate M t := by
    have hh : k⁻¹ ∈ rightConjugate M t := by
      rw [← hinv]
      exact rightConjugateElem_mem_rightConjugate hsm
    simpa using (rightConjugate M t).inv_mem hh
  refine ⟨k, ⟨hsm, hkconj⟩, hinv,
    productDisconnected_odd_orderOf_mul h hs ht htM (Or.inr hsm), ?_⟩
  simpa [k, rightConjugateElem, MulAut.conj_apply, mul_inv_rev, ti,
    (h.involutions s hs).inv_eq_self, mul_assoc] using he'

end BenderSuzuki.ZD
