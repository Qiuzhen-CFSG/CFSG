module

public import Theory.GroupTheory.ConjugateEscape

/-!
# Further pushing up: the conjugate-escape step

This module begins the proof of Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined manuscript (1 March 2004), §C.6, pp. 164–169.
The lemma below isolates the normal-closure argument of C.6.3(1), using the
normalizer obstruction in C.6.2(3). The group-theoretic proof is in
`Theory.GroupTheory.ConjugateEscape`.

The commutator bound `[L,Q] ≤ U` is an explicit intermediate input here.
The full source theorem must additionally derive it from `L = O²(L)` and
`Q = O₂(LR)`, `U = [O₂(L),L]`. This lemma does not assert that derivation,
the rank conclusions of C.6.3, or either classification theorem C.6.1/C.6.4.
-/

namespace CFSG.Quasithin.ChapterC

open Subgroup

/-- The normalizer obstruction of C.6.2(3), together with the commutator
bound in the proof of C.6.3(1), produces an escaping conjugate. The output
uses the source's right conjugation `Uˣ = x⁻¹ U x`. -/
public theorem exists_conjugate_escape_of_commutator_le
    {G : Type*} [Group G] (L R T Λ U Q : Subgroup G)
    (hU : U ≠ ⊥) (hUR : U ≤ R) (hRT : R ≤ T)
    (hTR : T ≤ normalizer (R : Set G)) (hLQ : ⁅L, Q⁆ ≤ U)
    (hno : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R →
      (W.subgroupOf (L ⊔ T)).Normal →
      ¬ Λ ⊓ normalizer (R : Set G) ≤ Λ ⊓ normalizer (W : Set G)) :
    ∃ x ∈ (Λ ⊓ normalizer (R : Set G)) ⊔ T,
      ¬ U.map (MulAut.conj x⁻¹) ≤ Q := by
  let X := Λ ⊓ normalizer (R : Set G)
  obtain ⟨x, hx, hescape⟩ :=
    exists_conjugate_not_le_of_no_common_normal U R Q L (X ⊔ T)
      hU hUR (sup_le inf_le_right hTR) hLQ (by
        intro W hW hWR hLW hKW
        have hHW : L ⊔ T ≤ normalizer (W : Set G) :=
          sup_le hLW (le_sup_right.trans hKW)
        have hWH : W ≤ L ⊔ T := hWR.trans (hRT.trans le_sup_right)
        have hnormal : (W.subgroupOf (L ⊔ T)).Normal :=
          (normal_subgroupOf_iff_le_normalizer hWH).mpr hHW
        exact hno W hW hWR hnormal
          (le_inf inf_le_left (le_sup_left.trans hKW)))
  exact ⟨x⁻¹, (X ⊔ T).inv_mem hx, by simpa using hescape⟩

end CFSG.Quasithin.ChapterC
