module

public import Stellmacher.Recognition.NormalFourCentralFusion
public import Theory.GroupTheory.PGroup.TransitiveInvolutions
public import Theory.GroupTheory.PGroup.ThreeInvolutionExponent
public import Theory.GroupTheory.PGroup.ThreeInvolutionOrder

/-!
# Order and exponent bounds in the central-four MacWilliams step

The Sylow subgroup has precisely three involutions, all central, and its
automorphisms act transitively on them. The count follows from the elementary
rank bound; the automorphisms come from the normalizer fusion theorem.

The intrinsic three-involution theorems then give exponent four and order 64
when the Sylow subgroup is nonabelian. Their proofs use the critical subgroup
and class-two arguments for the exponent, followed by the anisotropic square
map on the central quotient for the order. Thus the numerical conclusions
follow without assuming an ambient classification theorem, the N₂ condition,
or an additional normalizer inequality.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3 and Lemma 5.1,
printed pp.386 and 393.
-/

namespace Stellmacher.Recognition.NormalFourMacWilliams

open Subgroup

/-- The intrinsic classification inputs follow from central-four fusion.
Neither the N₂ condition nor an additional normalizer inequality is needed. -/
public theorem three_involution_data
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hfour : Nat.card (omega₁ (center S) (p := 2)) = 4) :
    (∀ x : S, x ^ 2 = 1 → x ∈ center S) ∧
      Nat.card {x : S // orderOf x = 2} = 3 ∧
      ∀ x y : S, orderOf x = 2 → orderOf y = 2 →
        ∃ a : MulAut S, a x = y := by
  have hr := elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)
  refine ⟨fun _ hx => mem_center_of_square_eq_one_of_omega_center_card_four hr hfour hx,
    card_involutions_of_omega_center_card_four hr hfour, ?_⟩
  intro x y hx hy
  obtain ⟨n, hn, he⟩ := NormalFourCentralOmegaFour.involutions_normalizer_conjugate
    hns S hrank hfour x y hx hy
  refine ⟨normalizerMonoidHom (S : Subgroup G) ⟨n⁻¹, inv_mem hn⟩, ?_⟩
  apply Subtype.ext
  change n⁻¹ * (x : G) * (n⁻¹)⁻¹ = y
  simpa only [inv_inv] using he

/-- The central-four fusion hypotheses force a nonabelian Sylow two-subgroup
to have order 64 and exponent dividing four. Neither N₂ nor an additional
normalizer inequality is needed. -/
public theorem card_and_exponent
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hnonab : ¬ IsMulCommutative S)
    (hfour : Nat.card (omega₁ (center S) (p := 2)) = 4) :
    Nat.card S = 64 ∧ ∀ x : S, x ^ 4 = 1 := by
  obtain ⟨hcentral, hthree, htrans⟩ := three_involution_data hns S hrank hfour
  have hexp := S.isPGroup'.exponent_four_of_transitive_three_involutions
    hnonab hcentral hthree htrans
  exact ⟨S.isPGroup'.card_eq_sixty_four_of_exponent_four_of_transitive_three_involutions
    hnonab hcentral hthree htrans hexp, hexp⟩

end Stellmacher.Recognition.NormalFourMacWilliams
