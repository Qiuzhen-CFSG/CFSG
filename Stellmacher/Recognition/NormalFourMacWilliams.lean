module

public import Stellmacher.Recognition.NormalFourCentralFusion
public import Stellmacher.Recognition.NormalFourMacWilliamsBounds
public import Theory.GroupTheory.PGroup.TransitiveInvolutions

/-!
# The central-four MacWilliams structure

Central-four fusion makes the three involutions central and automorphism-
transitive. The intrinsic bounds in `NormalFourMacWilliamsBounds` give order
64 and exponent four. The special-group calculation then identifies the
center, commutator and Frattini subgroups and shows that the center is
elementary abelian of order four. This proves the central-four conclusion
directly, without an ambient classification into Sylow alternatives.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 5.1, p.393.
-/

namespace Stellmacher.Recognition.NormalFourMacWilliams

open Subgroup

/-- Exponent four and the central-four fusion data force all the subgroup
equalities and the elementary center of order four. -/
public theorem structural_equalities_of_exponent
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hnonab : ¬ IsMulCommutative S)
    (hfour : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hexp : ∀ x : S, x ^ 4 = 1) :
    center S = commutator S ∧ center S = frattini S ∧
      IsElementaryAbelian 2 (center S) ∧ Nat.card (center S) = 4 := by
  have hcentral (x : S) (hx : x ^ 2 = 1) : x ∈ center S :=
    mem_center_of_square_eq_one_of_omega_center_card_four
      (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) hfour hx
  have htrans (x y : S) (hx : orderOf x = 2) (hy : orderOf y = 2) :
      ∃ a : MulAut S, a x = y := by
    obtain ⟨n, hn, he⟩ := NormalFourCentralOmegaFour.involutions_normalizer_conjugate
      hns S hrank hfour x y hx hy
    refine ⟨normalizerMonoidHom (S : Subgroup G) ⟨n⁻¹, inv_mem hn⟩, ?_⟩
    apply Subtype.ext
    change n⁻¹ * (x : G) * (n⁻¹)⁻¹ = y
    simpa only [inv_inv] using he
  obtain ⟨hd, hf, he, ho⟩ :=
    S.isPGroup'.special_of_exponent_four_of_transitive_involutions
      hnonab hcentral htrans hexp
  refine ⟨hd, hf, he, ?_⟩
  rw [ho, omega_one_eq_map_center_of_card_four
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) hfour,
    card_map_of_injective (center S).subtype_injective]
  exact hfour

/-- The concrete MacWilliams conclusion, after supplying its remaining order
and exponent data. This adapter uses neither N₂ nor an extra normalizer
hypothesis. -/
public theorem structural_equalities_of_card_and_exponent
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hnonab : ¬ IsMulCommutative S)
    (hfour : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hcard : Nat.card S = 64) (hexp : ∀ x : S, x ^ 4 = 1) :
    Nat.card S = 64 ∧ center S = commutator S ∧ center S = frattini S ∧
      IsElementaryAbelian 2 (center S) ∧ Nat.card (center S) = 4 :=
  ⟨hcard, structural_equalities_of_exponent hns S hrank hnonab hfour hexp⟩

/-- The central-four MacWilliams conclusion. The N₂ condition and the extra
normalizer inequality are unnecessary for this specialization. -/
public theorem structural_equalities
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hnonab : ¬ IsMulCommutative S)
    (hfour : Nat.card (omega₁ (center S) (p := 2)) = 4) :
    Nat.card S = 64 ∧ center S = commutator S ∧ center S = frattini S ∧
      IsElementaryAbelian 2 (center S) ∧ Nat.card (center S) = 4 := by
  obtain ⟨hcard, hexp⟩ := card_and_exponent hns S hrank hnonab hfour
  exact structural_equalities_of_card_and_exponent hns S hrank hnonab hfour hcard hexp

end Stellmacher.Recognition.NormalFourMacWilliams
