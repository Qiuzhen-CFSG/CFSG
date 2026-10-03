module

public import Theory.GroupTheory.ConjugationFiberCard
public import Theory.GroupTheory.PGroup.QuaternionCyclicFourDisplacement
public import Theory.GroupTheory.PGroup.QuaternionCyclicOuterCentralizer

/-!
# The cardinality assembly for quaternion–cyclic conjugation fibers

The quaternion–cyclic calculation reduces to two intrinsic action facts:
the centralizer in the core has order four, and every element of the
elementary four occurs as a conjugation difference. The general fiber formula
then gives sixteen solutions.

An outer involution fixing the elementary four inverts a cyclic element of
order four. The quaternion and cyclic action calculations then establish both
facts, and the final theorem discharges every premise of the fiber formula.
No uniqueness or elementary-rank assumption is imposed.
Source: Janko–Thompson (1970), §4, Case 2, printed p.393.
-/

namespace Subgroup

/-- A four-element target and a four-element centralizer give sixteen
conjugation solutions, provided all four target elements occur. -/
public theorem card_conjugation_fiber_eq_sixteen_of_centralizer_card_four
    {P : Type*} [Group P] [Finite P] (R W : Subgroup P) (t : P)
    (hW : Nat.card W = 4)
    (hcentralizer : Nat.card (R ⊓ centralizer ({t} : Set P) : Subgroup P) = 4)
    (hhit : ∀ w : W, ∃ x : R, (x : P)⁻¹ * t * x * t⁻¹ = w) :
    Nat.card {x : R // (x : P)⁻¹ * t * x * t⁻¹ ∈ W} = 16 := by
  rw [card_conjugation_difference_preimage_of_surjective R W t hhit,
    hW, hcentralizer]

/-- An outer involution centralizing the elementary four in an index-two
quaternion–cyclic core has exactly sixteen conjugation differences in that four. -/
public theorem card_conjugation_fiber_eq_sixteen_of_quaternion_cyclic_core
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (R Q C W : Subgroup P) (hR : R.index = 2)
    (hQn : Q.Normal) (hCn : C.Normal) (hQ : Nonempty (Q ≃* QuaternionGroup 2))
    (hCc : IsCyclic C) (hC : 8 ≤ Nat.card C)
    (hQC : C ≤ centralizer (Q : Set P)) (hgen : Q ⊔ C = R)
    (hinter : Nat.card (Q ⊓ C : Subgroup P) = 2)
    (hcenter : C = (center R).map R.subtype)
    (hWn : W.Normal) (hWe : IsElementaryAbelian 2 W)
    (hW : Nat.card W = 4) (hWR : W ≤ R)
    (t : P) (ht : t ^ 2 = 1) (htR : t ∉ R) (htW : t ∈ centralizer (W : Set P))
    (houter : ¬ ∃ q₀ : Q, ∀ q : Q,
      t * (q : P) * t⁻¹ = (q₀ : P) * (q : P) * (q₀ : P)⁻¹) :
    Nat.card {x : R // (x : P)⁻¹ * t * x * t⁻¹ ∈ W} = 16 := by
  obtain ⟨⟨d, hd, htd⟩, hhit⟩ := quaternion_cyclic_four_displacement
    hP R Q C W hR hQn hCn hQ hCc hC hQC hgen hinter hcenter
    hWn hWe hW hWR t ht htR htW houter
  let := hQn
  let := hCn
  let := hCc
  have hcentralizer := card_inf_centralizer_quaternion_cyclic_of_inverts_four
    hP R Q C hQ hQC hgen hinter t ht houter d hd htd
  exact card_conjugation_fiber_eq_sixteen_of_centralizer_card_four R W t hW
    hcentralizer hhit

end Subgroup
