module

public import CFSG.Quasithin.ChapterC.Defs
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.CharacteristicNormalizerGeneration

/-!
# Rank-one pushing-up: characteristic subgroup reduction

Remark C.1.19 constructs C₁(T) as Z(T) ∩ C₁(Baum(T)). The theorem below
proves the characteristicity, nontriviality and omega-center bound for this
construction from a characteristic subgroup B of T. It can therefore be used
with the Baumann subgroup as soon as the Glauberman–Niles witnesses on B are
constructed. The imported generation lemmas supply the elementary final steps
of C.1.21 and the normalizer containment used in C.1.29.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), C.1.17–C.1.29, pp.126–134. This module currently
establishes the characteristic-center reduction, not the Glauberman–Niles
existence theorem or the local C(G,T) theorem.
-/

public section

namespace CFSG.Quasithin.ChapterC

/-- The nontrivial characteristic-center construction of C.1.19. Here B will
be Baum(T), and D will be the first Glauberman–Niles subgroup of B. -/
theorem rankOne_characteristic_center_reduction
    {T : Type*} [Group T] [Finite T] (hT : IsPGroup 2 T)
    (B : Subgroup T) [B.Characteristic] (D : Subgroup B) [D.Characteristic]
    (hne : D ≠ ⊥)
    (hD : D ≤ (omega₁ (Subgroup.center B) (p := 2)).map (Subgroup.center B).subtype) :
    (Subgroup.center T ⊓ D.map B.subtype).Characteristic ∧
      Subgroup.center T ⊓ D.map B.subtype ≠ ⊥ ∧
      Subgroup.center T ⊓ D.map B.subtype ≤
        (omega₁ (Subgroup.center T) (p := 2)).map (Subgroup.center T).subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Subgroup.characteristic_center_reduction hT B D hne
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hD hx
  let : IsElementaryAbelian 2 (omega₁ (Subgroup.center B) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative (Subgroup.center B)
  exact congrArg (Subgroup.center B).subtype
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz)

end CFSG.Quasithin.ChapterC
