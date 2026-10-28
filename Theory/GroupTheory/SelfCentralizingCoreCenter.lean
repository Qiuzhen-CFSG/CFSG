module
public import Theory.PGroupCore
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centers of cores in overgroups of self-centralizing normal p-subgroups

If Q is self-centralizing and Q ≤ R, every element of Z(R) lies in Z(Q).
The subgroup statement keeps the actual inclusions into the ambient group.
If Q is also a normal p-subgroup and Q ≤ H, it lies in O_p(H), so the
same embedded inclusion bounds Z(O_p(H)) by Z(Q). No normality of H is
needed.

The concrete consumers are the J₄ max2 and max4 local subgroups in the
A₅ branch of Aschbacher–Smith 10.2.9; compare the characteristic-p
inheritance argument in A.1.6.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- Centers decrease inside the ambient group above a self-centralizing subgroup. -/
theorem center_map_le_center_map_of_centralizer_le
    (Q R : Subgroup G) (hQR : Q ≤ R)
    (hC : centralizer (Q : Set G) ≤ Q) :
    (center R).map R.subtype ≤ (center Q).map Q.subtype := by
  rintro x ⟨z, hz, rfl⟩
  have hc : (z : G) ∈ centralizer (Q : Set G) := by
    intro q hq
    exact congrArg R.subtype (mem_center_iff.mp hz ⟨q, hQR hq⟩)
  refine ⟨⟨z, hC hc⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro q
  exact Subtype.ext (hc q q.property)

/-- The embedded center inclusion gives the corresponding finite order bound. -/
theorem center_card_le_of_centralizer_le [Finite G]
    (Q R : Subgroup G) (hQR : Q ≤ R)
    (hC : centralizer (Q : Set G) ≤ Q) :
    Nat.card (center R) ≤ Nat.card (center Q) := by
  have h := card_le_of_le (center_map_le_center_map_of_centralizer_le Q R hQR hC)
  simpa only [card_map_of_injective R.subtype_injective,
    card_map_of_injective Q.subtype_injective] using h

/-- The actual core-center image lies in the center image of a self-centralizing
normal p-subgroup contained in H. -/
theorem center_pCore_map_le_center_map_of_normal_pSubgroup
    (p : ℕ) (Q H : Subgroup G) [Q.Normal]
    (hQp : IsPGroup p Q) (hQH : Q ≤ H)
    (hC : centralizer (Q : Set G) ≤ Q) :
    (center (pCore p H)).map (H.subtype.comp (pCore p H).subtype) ≤
      (center Q).map Q.subtype := by
  have hcore : Q.subgroupOf H ≤ pCore p H :=
    le_sSup ⟨inferInstance, hQp.comap_subtype⟩
  rintro x ⟨z, hz, rfl⟩
  have hc : ((z : H) : G) ∈ centralizer (Q : Set G) := by
    intro q hq
    let qH : H := ⟨q, hQH hq⟩
    let qR : pCore p H := ⟨qH, hcore hq⟩
    exact congrArg (fun t : pCore p H => ((t : H) : G)) (mem_center_iff.mp hz qR)
  refine ⟨⟨((z : H) : G), hC hc⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro q
  exact Subtype.ext (hc q q.property)

/-- Core-center order bound without assuming normality of the overgroup H. -/
theorem center_pCore_card_le_of_normal_pSubgroup [Finite G]
    (p : ℕ) (Q H : Subgroup G) [Q.Normal]
    (hQp : IsPGroup p Q) (hQH : Q ≤ H)
    (hC : centralizer (Q : Set G) ≤ Q) :
    Nat.card (center (pCore p H)) ≤ Nat.card (center Q) := by
  have h := card_le_of_le
    (center_pCore_map_le_center_map_of_normal_pSubgroup p Q H hQp hQH hC)
  have hf : Function.Injective (H.subtype.comp (pCore p H).subtype) :=
    H.subtype_injective.comp (pCore p H).subtype_injective
  simpa only [card_map_of_injective hf,
    card_map_of_injective Q.subtype_injective] using h

/-- The center bound passes to any overgroup of a self-centralizing p-core. -/
theorem center_pCore_card_le_of_pCore_le [Finite G]
    (p : ℕ) (H : Subgroup G) (hQH : pCore p G ≤ H)
    (hC : centralizer (pCore p G : Set G) ≤ pCore p G) :
    Nat.card (center (pCore p H)) ≤ Nat.card (center (pCore p G)) :=
  center_pCore_card_le_of_normal_pSubgroup p (pCore p G) H pCore_isPGroup hQH hC

end Subgroup
