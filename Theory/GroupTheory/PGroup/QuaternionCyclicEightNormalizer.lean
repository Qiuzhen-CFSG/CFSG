module

public import Theory.GroupTheory.IndexTwoNormalizerFiber
public import Theory.GroupTheory.PGroup.QuaternionCyclicFourAction
public import Theory.GroupTheory.PGroup.QuaternionCyclicConjugationCount

/-!+# Elementary-eight normalizers in a quaternion–cyclic core

Let an index-two subgroup be the central product of a quaternion group of
order eight and a cyclic center of order at least eight. If the ambient
2-group has a unique normal elementary four, then the normalizer of any
elementary eight crossing the core meets the core in a subgroup of order
sixteen.

The intersection of the elementary eight with the core is the unique normal
four. An outside involution centralizes this four and acts outerly on the
quaternion factor. The conjugation-fiber count gives sixteen, and the
index-two normalizer equivalence transfers that count to the normalizer.
No bound on all elementary subgroups, or exclusion of normal elementary
eights, is needed.

Source: Janko–Thompson (1970), §4, Case 2, printed p.393 (PDF page 9),
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace Subgroup

/-- The core intersection of the normalizer of a crossing elementary eight
has order sixteen in a quaternion–cyclic core with a unique normal four. -/
public theorem card_core_normalizer_eq_sixteen_of_quaternion_cyclic_core
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (R Q C W : Subgroup P) (hR : R.index = 2)
    (hQn : Q.Normal) (hCn : C.Normal) (hQ : Nonempty (Q ≃* QuaternionGroup 2))
    (hCc : IsCyclic C) (hC : 8 ≤ Nat.card C)
    (hQC : C ≤ centralizer (Q : Set P)) (hgen : Q ⊔ C = R)
    (hinter : Nat.card (Q ⊓ C : Subgroup P) = 2)
    (hcenter : C = (center R).map R.subtype)
    (hWn : W.Normal) (hWe : IsElementaryAbelian 2 W)
    (hW : Nat.card W = 4)
    (hunique : ∀ U : Subgroup P, U.Normal → IsElementaryAbelian 2 U →
      Nat.card U = 4 → U = W)
    (F : Subgroup P) (hFe : IsElementaryAbelian 2 F) (hF : Nat.card F = 8)
    (hout : ¬ F ≤ R) (_hcap : Nat.card (R.subgroupOf F) = 4) :
    Nat.card (R.subgroupOf (normalizer (F : Set P))) = 16 := by
  let := hQn
  let := hCn
  let := hCc
  let := hWn
  let := hWe
  let := hFe
  obtain ⟨hRF, houter⟩ := quaternion_cyclic_core_four_and_outer_action
    R Q C W hR hQ hgen hinter hcenter hW hunique F hF hout
  obtain ⟨t, htF, htR⟩ := SetLike.not_le_iff_exists.mp hout
  have hWR : W ≤ R := hRF ▸ inf_le_left
  have hWF : W ≤ F := hRF ▸ inf_le_right
  have ht : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) t htF
  have htW : t ∈ centralizer (W : Set P) := by
    intro w hw
    exact (F.le_centralizer htF) w (hWF hw)
  rw [card_core_normalizer_eq_card_conjugation_fiber R F W hR hRF t htF htR]
  exact card_conjugation_fiber_eq_sixteen_of_quaternion_cyclic_core
    hP R Q C W hR hQn hCn hQ hCc hC hQC hgen hinter hcenter
    hWn hWe hW hWR t ht htR htW (houter t htF htR)

end Subgroup
