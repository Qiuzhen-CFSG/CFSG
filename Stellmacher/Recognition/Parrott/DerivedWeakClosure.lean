module
public import Stellmacher.Recognition.Parrott.UniqueElementary
public import Stellmacher.Recognition.Parrott.DerivedNormalizer
public import Theory.GroupTheory.UniqueElementaryCentralizerFusion

/-!
# Derived weak closure under Parrott's core-involution negation

For a finite N₂ group with the original Parrott centralizer data, suppose
every involution in the actual mapped two-core lies in its derived image
E. Then an ambient conjugate of z that lies in E equals z.

The preceding uniqueness theorem makes E the unique elementary subgroup
of order32 in C_G(z). The first centralizer lemma supplies an ambient
Sylow two-subgroup inside C_G(z), and the N₂ normalizer theorem identifies
N_G(E) with that centralizer. The general unique-elementary fusion theorem
then proves weak closure by transporting a normalized join into this Sylow.

Source: David Parrott, *A characterization of the Tits' simple group*
(1972), Lemma 3, p.675. This assembly makes the source's uniqueness-to-fusion
step explicit. Its core-involution premise is the contradiction assumption
of that lemma; there is no assumed fusion or replacement local model.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- The core-involution negation forces z to be weakly closed in the actual derived image. -/
public theorem parrott_derived_weakClosure_of_core_involutions
    {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    (∀ t : G, t ∈ J.map H.subtype → orderOf t = 2 → t ∈ E) →
    ∀ t : G, t ∈ E → IsConj z t → t = z := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  change (∀ t : G, t ∈ J.map H.subtype → orderOf t = 2 → t ∈ E) →
    ∀ t : G, t ∈ E → IsConj z t → t = z
  intro hcore t ht hconj
  obtain ⟨_, _, _, _, _, hElem, hDcard, hSylow⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (K := commutator J) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans hDcard
  let T : Sylow 2 H := Classical.choice inferInstance
  obtain ⟨S, hS⟩ := hSylow T
  have hSH : (S : Subgroup G) ≤ H := by
    rw [hS]
    exact map_subtype_le _
  exact conjugate_eq_of_unique_elementary_centralizer z E
    (parrott_derived_normalizer_of_nTwo hN z h) S hSH
    (fun A hAH hA hAcard => parrott_unique_elementary_of_core_involutions z h hcore
      A hAH hA (hAcard.trans hEcard)) t ht hconj

end Stellmacher.Recognition
