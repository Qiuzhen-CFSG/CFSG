module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Stellmacher.Recognition.NormalFourNonnormalLargeFactor
public import Stellmacher.Recognition.NormalFourNonnormalWidthOne
public import Theory.GroupTheory.PGroup.RankTwoSymplecticBounds
public import Theory.GroupTheory.SmallCoreSylowIndex

/-!
# Bounds for the two-core in the nonnormal four-group branch

The quotient throughout is the actual `N_G(Ω₁(Z(S)))/O₂′`. Its two-core
has order at least sixteen by Hall's theorem and the exclusion of pure Hall
factors. Its Sylow two-subgroup is not normal: the unique normal four is
characteristic in that Sylow, and hence would have normal quotient image.
Thus the relative index of the two-core in the quotient Sylow is at least two.

Once the core has order less than thirty-two, the odd-automorphism bound and
Hall's theorem give Sylow relative index exactly two. The ambient large-factor
exclusion discharges the intrinsic width-one premise, and the cyclic and
noncyclic tail exclusions bound the whole core strictly below thirty-two.
Together these give core order sixteen and Sylow relative index two.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed pp.389–393,
through the calculation `|T| = 32`.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- An abelian core would centralize the four, making it normal by the rank
bound. -/
public theorem omegaQuotient_pCore_noncommutative (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hnormal : ¬ (fourImage S E).Normal) :
    ¬ IsMulCommutative (pCore 2 (OmegaQuotient S)) := by
  intro hcomm
  let : IsMulCommutative (pCore 2 (OmegaQuotient S)) := hcomm
  let : IsElementaryAbelian 2 (fourImage S E) := fourImage_elementary S E
  have hle := fourImage_le_pCore hN hrank S hZ E hE
  apply hnormal
  apply normal_four_of_normal_centralizing_overgroup
    (fun A hA => @omegaQuotient_rank _ _ _ hrank S A hA)
    (fourImage S E) (pCore 2 (OmegaQuotient S)) (fourImage_card S E hE) hle
  intro x hx y hy
  exact congrArg Subtype.val
    ((isMulCommutative_iff.mp hcomm) (⟨y, hle hy⟩ : pCore 2 (OmegaQuotient S)) ⟨x, hx⟩)

/-- The quotient Sylow cannot be normal when its unique normal four has
nonnormal ambient image. -/
public theorem omegaQuotientSylow_not_normal
    (S : Sylow 2 G) (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    ¬ (omegaQuotientSylow S : Subgroup (OmegaQuotient S)).Normal := by
  intro hT
  let T : Subgroup (OmegaQuotient S) := omegaQuotientSylow S
  let : T.Normal := hT
  let e : S ≃* T := omegaQuotientSylowEquiv S
  have hchar : E.Characteristic := characteristic_of_unique_normal_four E hE hunique
  let F := E.map e.toMonoidHom
  have hFchar : F.Characteristic := by
    apply characteristic_iff_map_le.mpr
    intro a
    rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(e.trans a |>.trans e.symm) y,
      characteristic_iff_le_comap.mp hchar _ hy, ?_⟩
    exact e.apply_symm_apply _
  let : F.Characteristic := hFchar
  have hmap : F.map T.subtype = fourImage S E := by
    change (E.map e.toMonoidHom).map T.subtype = fourImage S E
    rw [map_map, fourImage_eq_map]
    congr 1
    ext x
    exact omegaQuotientSylowEquiv_apply S x
  exact hnormal (hmap ▸ (inferInstance : (F.map T.subtype).Normal))

/-- The whole core has order at least sixteen, not just a nontrivial
extraspecial factor. -/
public theorem omegaQuotient_pCore_card_lower (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    16 ≤ Nat.card (pCore 2 (OmegaQuotient S)) := by
  apply IsBinarySymplecticType.sixteen_le_card_of_not_hall pCore_isPGroup
    (elementary_card_lt_eight_of_subgroup ?_ (pCore 2 (OmegaQuotient S)))
    (omegaQuotient_pCore_symplectic hrank S E hunique hnormal)
    (omegaQuotient_pCore_not_hall hN hrank S hZ E hE hnormal)
  intro A hA
  let : IsElementaryAbelian 2 A := hA
  exact omegaQuotient_rank hrank S A

/-- The quotient core is a proper subgroup of the quotient Sylow. -/
public theorem omegaQuotient_pCore_relIndex_lower
    (S : Sylow 2 G) (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    2 ≤ (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) := by
  have hle : pCore 2 (OmegaQuotient S) ≤ omegaQuotientSylow S :=
    pCore_isPGroup.le_sylow_of_normal _
  have hzero : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) ≠ 0 :=
    index_ne_zero_of_finite
  have hone : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) ≠ 1 := by
    intro h
    have heq := le_antisymm hle (relIndex_eq_one.mp h)
    exact omegaQuotientSylow_not_normal S E hE hunique hnormal
      (heq ▸ (inferInstance : (pCore 2 (OmegaQuotient S)).Normal))
  omega

/-- Assemble the exact bounds once the ambient exclusions give both upper
bounds. The lower bounds require no ambient simplicity or fusion premise. -/
public theorem omegaQuotient_pCore_order_index_of_upper_bounds (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hcard : Nat.card (pCore 2 (OmegaQuotient S)) ≤ 16)
    (hindex : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) ≤ 2) :
    Nat.card (pCore 2 (OmegaQuotient S)) = 16 ∧
      (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2 := by
  exact ⟨Nat.le_antisymm hcard
      (omegaQuotient_pCore_card_lower hN hrank S hZ E hE hunique hnormal),
    Nat.le_antisymm hindex
      (omegaQuotient_pCore_relIndex_lower S E hE hunique hnormal)⟩

/-- The core-size exclusion is the only remaining ambient input: a core of
order less than thirty-two has order sixteen and Sylow relative index two. -/
public theorem omegaQuotient_pCore_order_index_of_card_lt_thirty_two (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hbound : Nat.card (pCore 2 (OmegaQuotient S)) < 32) :
    Nat.card (pCore 2 (OmegaQuotient S)) = 16 ∧
      (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2 := by
  have hsmall : Nat.card (pCore 2 (OmegaQuotient S)) ≤ 16 := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := OmegaQuotient S)).exists_card_eq
    have hnle : n ≤ 4 := by
      by_contra h
      have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show 5 ≤ n by omega)
      rw [← hn] at hp
      norm_num at hp
      omega
    rw [hn]
    exact Nat.pow_le_pow_right (by decide) hnle
  have hindex := (omegaQuotientSylow S).relIndex_pCore_eq_two_of_small_nonabelian
    (omegaQuotient_solvable hN S hZ)
    (omegaQuotient_centralizer_pCore_le hN S hZ)
    (omegaQuotient_pCore_noncommutative hN hrank S hZ E hE hnormal) hbound
    (omegaQuotientSylow_not_normal S E hE hunique hnormal)
  exact omegaQuotient_pCore_order_index_of_upper_bounds
    hN hrank S hZ E hE hunique hnormal hsmall hindex.le

/-- The ambient large-factor exclusion rules out every width-two Hall
decomposition, so the width-one tail bounds apply to the whole quotient core. -/
public theorem omegaQuotient_pCore_card_lt_thirty_two
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    Nat.card (pCore 2 (OmegaQuotient S)) < 32 := by
  apply omegaQuotient_pCore_card_lt_thirty_two_of_width_exclusion
    hns hN hrank S hnonab hZ E hE hunique hnormal
  intro A D _hAn _hDn hA _hD hc hgen hAc
  let : IsExtraspecial 2 A := hA
  exact omegaQuotient_large_factor_false hns hN hrank S hZ E hE hunique A D hAc hc hgen

/-- The core order/index portion of Janko–Thompson Lemma 4.1 in the
nonnormal four-image branch, for the literal quotient `N_G(Ω₁(Z(S)))/O₂′`. -/
public theorem omegaQuotient_pCore_order_index
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    Nat.card (pCore 2 (OmegaQuotient S)) = 16 ∧
      (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2 := by
  exact omegaQuotient_pCore_order_index_of_card_lt_thirty_two
    hN hrank S hZ E hE hunique hnormal
    (omegaQuotient_pCore_card_lt_thirty_two hns hN hrank S hnonab hZ E hE hunique hnormal)

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
