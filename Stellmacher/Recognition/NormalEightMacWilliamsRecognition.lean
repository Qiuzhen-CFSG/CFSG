module

public import Theory.SpecificGroups.MacWilliams.SylowPresentations
public import Theory.SpecificGroups.MacWilliams.UnitaryRecognition
public import Theory.GroupTheory.PGroup.CentralInvolutionSylowRank
public import Stellmacher.Recognition.NormalFourMacWilliams
public import Stellmacher.Recognition.NormalEightMacWilliamsCentrality
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Recognition of the central-four MacWilliams alternative

The central omega order excludes the nonabelian small dihedral exceptions;
noncommutativity excludes the elementary four-group exception. Centrality of
Sylow involutions and Sylow conjugacy derive the ambient elementary rank
bound. The existing fusion and three-involution theorems then give order 64,
exponent four, and the special-group structure.

The critical-subgroup centrality theorem supplies the centrality input.
Intrinsic recognition then lifts the central quotient square map to the exact
zero-based unitary presentation, whose commutator convention is
`x⁻¹ * y⁻¹ * x * y`. In this central-four case the unitary alternative always
holds, giving the requested MacWilliams presentation dichotomy.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, printed p.386,
quoting MacWilliams, Trans. AMS 150 (1970), DOI
10.1090/S0002-9947-1970-0276324-3.
-/

namespace Stellmacher.Recognition.NormalEightMacWilliamsRecognition

open Subgroup

/-- The actual central-four and noncommutativity hypotheses exclude every
finite dihedral exception of order at most eight. `DihedralGroup n` has
order `2 * n` for positive `n`. -/
public theorem not_small_dihedral
    {P : Type*} [Group P] [Finite P]
    (hnonab : ¬ IsMulCommutative P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (n : ℕ) (hn : 0 < n) (hsmall : n ≤ 4) :
    ¬ Nonempty (P ≃* DihedralGroup n) := by
  rintro ⟨e⟩
  have hle := (omega₁ (center P) (p := 2)).card_le_card_group
  have hcard := Nat.card_congr (centerCongr e).toEquiv
  rw [hZ, hcard] at hle
  interval_cases n
  · have hc : Nat.card (center (DihedralGroup 1)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    omega
  · apply hnonab
    refine ⟨⟨fun x y => e.injective ?_⟩⟩
    simpa only [map_mul] using
      (show ∀ a b : DihedralGroup 2, a * b = b * a from by decide) (e x) (e y)
  · have hc : Nat.card (center (DihedralGroup 3)) = 1 := by
      rw [Nat.card_eq_fintype_card]
      decide
    omega
  · have hc : Nat.card (center (DihedralGroup 4)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    omega

private theorem elementary_rank_of_centrality
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hc : ∀ x : S, orderOf x = 2 → x ∈ center S) :
    ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8 := by
  intro A hA
  let : IsElementaryAbelian 2 A := hA
  exact lt_of_le_of_lt (S.elementary_card_le_four_of_central_involutions hZ hc A)
    (by decide)

/-- Once centrality is established, the three involutions are transitive
under Sylow automorphisms. The rank bound used by the fusion API is derived. -/
public theorem three_involution_data_of_centrality
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hc : ∀ x : S, orderOf x = 2 → x ∈ center S) :
    (∀ x : S, x ^ 2 = 1 → x ∈ center S) ∧
      Nat.card {x : S // orderOf x = 2} = 3 ∧
      ∀ x y : S, orderOf x = 2 → orderOf y = 2 →
        ∃ a : MulAut S, a x = y :=
  NormalFourMacWilliams.three_involution_data hns S
    (elementary_rank_of_centrality S hZ hc) hZ

/-- Centrality supplies the numerical and special-group inputs for intrinsic
unitary presentation recognition, without assuming an elementary rank bound. -/
public theorem structural_data_of_centrality
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hc : ∀ x : S, orderOf x = 2 → x ∈ center S) :
    Nat.card S = 64 ∧ (∀ x : S, x ^ 4 = 1) ∧
      center S = commutator S ∧ center S = frattini S ∧
      IsElementaryAbelian 2 (center S) ∧ Nat.card (center S) = 4 := by
  have hr := elementary_rank_of_centrality S hZ hc
  obtain ⟨hcard, hexp⟩ := NormalFourMacWilliams.card_and_exponent hns S hr hnonab hZ
  exact ⟨hcard, hexp,
    NormalFourMacWilliams.structural_equalities_of_exponent hns S hr hnonab hZ hexp⟩

/-- The central-four MacWilliams hypotheses identify the Sylow subgroup with
the explicit unitary presentation. No elementary-rank bound is assumed. -/
public theorem nonempty_unitary_equiv
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G)) :
    Nonempty (S ≃* MacWilliamsSylow.UnitarySylow) := by
  have hc := NormalEightMacWilliamsCentrality.involution_mem_center
    hns S hnonab hZ hno hnorm
  obtain ⟨hcentral, hthree, htrans⟩ := three_involution_data_of_centrality hns S hZ hc
  obtain ⟨hcard, hexp, hder, hPhi, hZelem, hZcard⟩ :=
    structural_data_of_centrality hns S hnonab hZ hc
  exact MacWilliamsSylow.nonempty_unitary_equiv_of_intrinsic_data
    S.isPGroup' hnonab hcentral hthree htrans hcard hexp hder hPhi hZelem hZcard

/-- MacWilliams presentation recognition with the normal elementary four
subgroup supplied by the consumer. The central omega already supplies such a
subgroup, so the stronger unitary recognition does not need this extra input. -/
public theorem sylow_presentation_dichotomy
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (_hW : Nat.card W = 4)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G)) :
    Nonempty (S ≃* MacWilliamsSylow.HallJankoSylow) ∨
      Nonempty (S ≃* MacWilliamsSylow.UnitarySylow) :=
  Or.inr (nonempty_unitary_equiv hns S hnonab hZ hno hnorm)

end Stellmacher.Recognition.NormalEightMacWilliamsRecognition
