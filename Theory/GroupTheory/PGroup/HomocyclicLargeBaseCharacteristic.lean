module

public import Theory.GroupTheory.CharacteristicInvolutionProfile
public import Theory.GroupTheory.PGroup.NormalEightCentralizerCharacteristic
public import Theory.GroupTheory.PGroup.HomocyclicLargeBaseFourthRoots
public import Theory.GroupTheory.PGroup.HomocyclicLargeBaseFourTorsionKernel
public import Theory.GroupTheory.PGroup.HomocyclicLargeBaseNonfaithful

/-!
# An intrinsic criterion for the large homocyclic base obstruction

In the absence of normal elementary eights, a normal elementary four is
characteristic in its centralizer: it equals the first omega subgroup of the
center there. If the numbers of roots of a fixed power differ on its three
involutions, one of the fibers is a singleton, giving a characteristic
subgroup of order two in the centralizer.

For a large homocyclic base whose action is faithful on four-torsion modulo
the base, the fourth-root calculation supplies this nonconstant profile.
Without that faithfulness hypothesis, a dichotomy reduces the remaining
case to a normal index-two extension of the base with no new involutions.
Such extensions do occur; they cannot be excluded in general (see
`docs/homocyclic-four-torsion-counterexample.md`). In this case the
four-torsion kernel is characteristic in the centralizer and has nontrivial
cyclic derived subgroup, whose unique involution supplies the required
characteristic subgroup. The final theorem combines these two cases. Square
roots alone are insufficient: in the square of the semidihedral group of
order sixteen, all three central involutions have 36 square roots, whereas
their fourth-root counts are 48, 48, and 16.

Source context: Janko–Thompson, Math. Z. 113 (1970), 1.4, printed p.386 and
the final paragraph of p.395. Those passages cite the structural theorem;
the elementary invariant-profile criterion proved here does not assume it.
-/

open Subgroup

namespace Subgroup

/-- The given four is characteristic inside its centralizer because it is
the first omega subgroup of the center. -/
public theorem normal_four_characteristic_in_centralizer
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4) :
    (W.subgroupOf (centralizer (W : Set P))).Characteristic := by
  let C := centralizer (W : Set P)
  let O := omega₁ (center C) (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let Z := O.map (center C).subtype
  have hZ : Z.Characteristic := characteristic_of_characteristic_of_characteristic
  have hEq : W.subgroupOf C = Z := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le (le_centralizer W)]
    exact (omega_one_center_centralizer_eq_normal_four hno W hW).symm
  exact hEq.symm ▸ hZ

/-- Nonconstant power-root counts on the normal four provide the intrinsic
characteristic involution needed for a large-base exclusion. -/
public theorem centralizer_exists_characteristic_two_of_nonconstant_power_fibers
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (k : ℕ)
    (hne : ∃ x y : centralizer (W : Set P),
      (x : P) ∈ W ∧ x ≠ 1 ∧ (y : P) ∈ W ∧ y ≠ 1 ∧
      Nat.card {t : centralizer (W : Set P) // t ^ k = x} ≠
        Nat.card {t : centralizer (W : Set P) // t ^ k = y}) :
    ∃ K : Subgroup (centralizer (W : Set P)), K.Characteristic ∧ Nat.card K = 2 := by
  let C := centralizer (W : Set P)
  let V := W.subgroupOf C
  let : V.Characteristic := normal_four_characteristic_in_centralizer hno W hW
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf (le_centralizer W)
  have hV : Nat.card V = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe (le_centralizer W)).toEquiv).trans hW
  apply exists_characteristic_two_of_nonconstant_invariant_on_four V hV
    (fun z : C => Nat.card {t : C // t ^ k = z}) (power_fiber_card_aut k)
  obtain ⟨x, y, hx, hx1, hy, hy1, hxy⟩ := hne
  exact ⟨x, hx, hx1, y, hy, hy1, hxy⟩

/-- A large homocyclic base gives a characteristic involution in the centralizer
of its omega four when its action on four-torsion is faithful modulo the base. -/
public theorem centralizer_exists_characteristic_two_of_homocyclic_four_torsion_faithful
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D] (hWD : W ≤ D)
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (hfaith : ∀ g ∈ centralizer (W : Set P),
      (∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) g d = d) → g ∈ D) :
    ∃ K : Subgroup (centralizer (W : Set P)), K.Characteristic ∧ Nat.card K = 2 := by
  apply centralizer_exists_characteristic_two_of_nonconstant_power_fibers hno W hW 4
  exact centralizer_exists_ne_fourth_root_card_of_homocyclic_four_torsion_faithful
    W hW B hB hWB D hWD hDC hO n hn e hfaith

end Subgroup

namespace IsPGroup

/-- The remaining large-base case has a normal index-two extension of the base
which fixes four-torsion and contains no involutions outside the base.
The second alternative is genuine, not a contradiction. -/
public theorem characteristic_two_or_homocyclic_extension
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D] (hWD : W ≤ D)
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    (∃ K : Subgroup (centralizer (W : Set P)), K.Characteristic ∧ Nat.card K = 2) ∨
    ∃ X : Subgroup P, X.Normal ∧ D ≤ X ∧ D.relIndex X = 2 ∧
      (∀ x ∈ X, ∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) x d = d) ∧
      (∀ x ∈ X, x ^ 2 = 1 → x ∈ D) := by
  classical
  by_cases hf : ∀ g ∈ centralizer (W : Set P),
      (∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) g d = d) → g ∈ D
  · exact Or.inl (centralizer_exists_characteristic_two_of_homocyclic_four_torsion_faithful
      hno W hW B hB hWB D hWD hDC hO n hn e hf)
  · push Not at hf
    obtain ⟨g, _, hgfour, hg⟩ := hf
    exact Or.inr (exists_normal_index_two_extension_of_four_torsion_kernel
      hP hZ hno W hW D hDC hO n hn e g hg hgfour)

/-- A self-centralizing homocyclic base with cyclic factors of order at least
eight forces a characteristic involution in the centralizer of the normal four.
The uniqueness hypothesis on the normal four is retained in the contract,
although the faithful and nonfaithful arguments do not require it. -/
public theorem centralizer_exists_characteristic_two_of_large_homocyclic_base
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (_hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D] (hWD : W ≤ D)
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    ∃ K : Subgroup (centralizer (W : Set P)), K.Characteristic ∧ Nat.card K = 2 := by
  obtain hchar | ⟨X, _, _, hindex, hfour, _⟩ :=
    characteristic_two_or_homocyclic_extension hP hZ hno W hW B hB hWB D hWD hDC hO n hn e
  · exact hchar
  · exact centralizer_exists_characteristic_two_of_homocyclic_nonfaithful_extension
      hP hZ hno W hW D hWD hDC hO n hn e X hindex hfour

end IsPGroup
