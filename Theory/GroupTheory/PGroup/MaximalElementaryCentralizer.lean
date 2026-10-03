module

public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.PGroup.Omega

/-!
# First omega of the centralizer of a largest elementary subgroup

If an elementary abelian p-subgroup has largest possible order, every element
of exponent p in its centralizer belongs to it. Adjoining such an element
gives an elementary subgroup, so the order bound forces equality. Consequently
the first omega subgroup of the centralizer, mapped to the ambient group,
is exactly the given elementary subgroup.

The order-sixteen specialization is the use of the four-generator bound in
Janko–Thompson, Math. Z. 113 (1970), Lemma 5.1, p.394. This module proves the
implication from an elementary order bound; it does not assume that the
absence of normal elementary eights is itself an elementary rank bound.
-/

namespace Subgroup

/-- A largest elementary abelian subgroup contains every element of exponent
p that centralizes it. -/
public theorem mem_of_pow_eq_one_of_elementary_card_le
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (E : Subgroup P) [IsElementaryAbelian p E]
    (hmax : ∀ A : Subgroup P, IsElementaryAbelian p A → Nat.card A ≤ Nat.card E)
    {x : P} (hx : x ^ p = 1) (hxC : x ∈ centralizer (E : Set P)) : x ∈ E := by
  let : IsElementaryAbelian p (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx
  let : IsElementaryAbelian p (E ⊔ zpowers x : Subgroup P) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hxC)
  have heq : E = E ⊔ zpowers x :=
    eq_of_le_of_card_ge le_sup_left (hmax _ inferInstance)
  rw [heq]
  exact (le_sup_right : zpowers x ≤ E ⊔ zpowers x) (mem_zpowers x)

/-- First omega of the centralizer of a largest elementary subgroup is the
subgroup itself, after mapping to the ambient group. -/
public theorem omega_one_centralizer_map_eq_of_elementary_card_le
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (E : Subgroup P) [IsElementaryAbelian p E]
    (hmax : ∀ A : Subgroup P, IsElementaryAbelian p A → Nat.card A ≤ Nat.card E) :
    (omega₁ (centralizer (E : Set P)) (p := p)).map
      (centralizer (E : Set P)).subtype = E := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    intro x hx
    apply mem_of_pow_eq_one_of_elementary_card_le E hmax _ x.property
    exact congrArg Subtype.val (show x ^ p = 1 by simpa using hx)
  · have hEC : E ≤ centralizer (E : Set P) :=
      le_centralizer_iff_isMulCommutative.mpr inferInstance
    intro x hx
    refine ⟨⟨x, hEC hx⟩, subset_closure ?_, rfl⟩
    change (⟨x, hEC hx⟩ : centralizer (E : Set P)) ^ (p ^ 1) = 1
    apply Subtype.ext
    simpa using elemPow_eq_one_of_isElementaryAbelian (p := p) x hx

end Subgroup
