module

public import Theory.GroupTheory.PGroup.RankTwoFour
public import Theory.GroupTheory.NormalFourCentralizer

/-!
# Normal four-groups with a unique central involution

Under an elementary rank bound of two, every elementary four-group contains
the first omega subgroup of the center. Distinct elementary four-groups cannot
centralize one another. When the center has just one involution, a normal
four-group has centralizer of index exactly two.

These elementary observations supply the local setup and the final rank
contradiction in Janko–Thompson, Math. Z. 113 (1970), §§3–6. They do not assert
the ambient fusion or weak-closure results used there.
-/

namespace Subgroup

/-- Under the rank bound, a four-group central in a normal overgroup is normal.
Conjugation preserves that overgroup and the equation `x² = 1`; every such
element in the overgroup belongs to the four-group. -/
public theorem normal_four_of_normal_centralizing_overgroup
    {P : Type*} [Group P] [Finite P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E C : Subgroup P) [IsElementaryAbelian 2 E] [C.Normal]
    (hE : Nat.card E = 4) (hEC : E ≤ C)
    (hCE : C ≤ centralizer (E : Set P)) : E.Normal := by
  refine ⟨fun x hx g => ?_⟩
  apply mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank E hE
  · have h := congrArg (MulAut.conj g)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) x hx)
    simpa only [map_pow, map_one, MulAut.conj_apply] using h
  · exact hCE ((inferInstance : C.Normal).conj_mem x (hEC hx) g)

/-- Central involutions belong to every elementary four under the rank bound. -/
public theorem omega_one_center_le_four_of_elementary_card_lt_eight
    {P : Type*} [Group P] [Finite P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    (omega₁ (center P) (p := 2)).map (center P).subtype ≤ E := by
  apply map_le_iff_le_comap.mpr
  apply (closure_le (E.comap (center P).subtype)).mpr
  intro x hx
  apply mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank E hE
  · exact congrArg Subtype.val (show x ^ 2 = 1 by simpa using hx)
  · exact center_le_centralizer _ x.property

/-- An elementary four cannot be central when central first omega has order two. -/
public theorem four_not_le_center_of_card_omega_one_center_eq_two
    {P : Type*} [Group P] [Finite P]
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    ¬ E ≤ center P := by
  intro hcentral
  have hle : E ≤ (omega₁ (center P) (p := 2)).map (center P).subtype := by
    intro x hx
    refine mem_map.mpr ⟨⟨x, hcentral hx⟩, ?_, rfl⟩
    apply subset_closure
    change (⟨x, hcentral hx⟩ : center P) ^ (2 ^ 1) = 1
    apply Subtype.ext
    simpa using elemPow_eq_one_of_isElementaryAbelian (A := E) x hx
  have hcard := card_le_of_le hle
  rw [card_map_of_injective (center P).subtype_injective, hZ, hE] at hcard
  omega

/-- With one central involution, a normal four has centralizer of index two. -/
public theorem centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) : (centralizer (E : Set P)).index = 2 := by
  have hle := centralizer_index_le_two_of_normal_four hP E hE
  have hzero := (centralizer (E : Set P)).index_ne_zero_of_finite
  have hone : (centralizer (E : Set P)).index ≠ 1 := by
    intro h
    exact four_not_le_center_of_card_omega_one_center_eq_two hZ E hE
      (centralizer_eq_top_iff_subset.mp (index_eq_one.mp h))
  omega

/-- Two commuting elementary fours coincide under the elementary rank bound. -/
public theorem four_eq_of_le_centralizer_of_elementary_card_lt_eight
    {P : Type*} [Group P] [Finite P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E F : Subgroup P) [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4)
    (hFE : F ≤ centralizer (E : Set P)) : F = E := by
  apply eq_of_le_of_card_ge ?_ (by omega)
  intro x hx
  exact mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank E hE
    (elemPow_eq_one_of_isElementaryAbelian (A := F) x hx) (hFE hx)

/-- A unique normal elementary four-group is characteristic. -/
public theorem characteristic_of_unique_normal_four {P : Type*} [Group P] [Finite P]
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E) : E.Characteristic := by
  apply characteristic_iff_map_eq.mpr
  intro f
  apply hunique
  · exact f.normal_map_iff.mpr inferInstance
  · exact IsElementaryAbelian.map f.toMonoidHom
  · rwa [card_map_of_injective f.injective]

end Subgroup
