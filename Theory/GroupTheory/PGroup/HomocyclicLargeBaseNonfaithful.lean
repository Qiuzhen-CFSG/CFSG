module

public import Theory.GroupTheory.PGroup.HomocyclicLargeBaseNonfaithfulReduction
public import Theory.GroupTheory.PGroup.HomocyclicFourTorsionKernelCharacteristic
public import Theory.GroupTheory.PGroup.CentralFourTorsionCyclicDerived

/-!
# Characteristic involutions from a nonfaithful homocyclic kernel

A proper extension inside the four-torsion kernel makes that kernel nonabelian.
The kernel is characteristic in the four-centralizer, and its derived
subgroup is cyclic. The unique involution of its derived subgroup therefore
generates a characteristic subgroup of order two in the whole four-centralizer.

The kernel's second omega is central and isomorphic to `C₄ × C₄`, so the
central-four-torsion theorem supplies cyclicity of its derived subgroup.
The intrinsic square-root argument in `HomocyclicFourTorsionKernelCharacteristic`
supplies characteristicity without requiring a characteristic base.

Source context: MacWilliams, Trans. AMS 150 (1970), printed pp.377–379,
assertions (xvii)–(xix). The imported results justify the needed invariance
and metacyclic structure for the present ambient hypotheses.
-/

open Subgroup
open scoped IsMulCommutative

namespace Subgroup

/-- The characteristic-kernel and cyclic-derived obligations suffice for final assembly. -/
public theorem characteristic_two_of_fourTorsionKernel_characteristic_cyclic_derived
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (W D : Subgroup P) [D.Normal] [IsMulCommutative D]
    [IsElementaryAbelian 2 W] (hWD : W ≤ D)
    (hDC : centralizer (D : Set P) ≤ D)
    (X : Subgroup P) (hi : D.relIndex X = 2)
    (hfour : ∀ x ∈ X, ∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) x d = d)
    (hchar : ((fourTorsionKernel D).subgroupOf (centralizer (W : Set P))).Characteristic)
    (hcyc : IsCyclic (_root_.commutator
      ((fourTorsionKernel D).subgroupOf (centralizer (W : Set P))))) :
    ∃ L : Subgroup (centralizer (W : Set P)), L.Characteristic ∧ Nat.card L = 2 := by
  let C := centralizer (W : Set P)
  let K := (fourTorsionKernel D).subgroupOf C
  let : K.Characteristic := hchar
  let : IsCyclic (_root_.commutator K) := hcyc
  apply exists_characteristic_two_of_nonabelian_characteristic_cyclic_derived
    (hP.to_subgroup C) K
  intro hab
  let : IsMulCommutative K := hab
  have he := subgroupOfEquivOfLe (fourTorsionKernel_le_centralizer W D hWD)
  have hk : IsMulCommutative (fourTorsionKernel D) := ⟨⟨fun x y => by
    obtain ⟨u, rfl⟩ := he.surjective x
    obtain ⟨v, rfl⟩ := he.surjective y
    rw [← map_mul, mul_comm, map_mul]⟩⟩
  exact nonabelian_fourTorsionKernel_of_extension D hDC X hi hfour hk

/-- A proper extension fixing four-torsion in a large homocyclic base gives a
characteristic involution in the centralizer of its omega four. The ambient
normal-eight obstruction suffices; no normal-eight obstruction in the centralizer,
characteristicity of the base, or restriction on involutions of the extension
is required as an additional hypothesis. -/
public theorem centralizer_exists_characteristic_two_of_homocyclic_nonfaithful_extension
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hWD : W ≤ D) (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (X : Subgroup P) (hindex : D.relIndex X = 2)
    (hfour : ∀ x ∈ X, ∀ d : D, d ^ 4 = 1 → MulAut.conjNormal (H := D) x d = d) :
    ∃ K : Subgroup (centralizer (W : Set P)), K.Characteristic ∧ Nat.card K = 2 := by
  apply characteristic_two_of_fourTorsionKernel_characteristic_cyclic_derived
    hP W D hWD hDC X hindex hfour
  · exact fourTorsionKernel_characteristic_in_centralizer hP hZ hno W hW
      D hWD hDC hO n hn e
  · exact isCyclic_commutator_subgroupOf_of_omega_two_le_center hP
      (fourTorsionKernel_le_centralizer W D hWD)
      (omega_two_fourTorsionKernel_central hP hZ hno W hW D hDC hO n hn e)
      (omegaTwoFourTorsionKernelEquiv hP hZ hno W hW D hDC hO n hn e)


end Subgroup
