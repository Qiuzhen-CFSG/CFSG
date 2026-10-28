module

public import Stellmacher.Recognition.SemidihedralThreeCyclicGeometry
public import Stellmacher.Recognition.SemidihedralThreeCyclicThreePart
public import Stellmacher.Recognition.SemidihedralThreeCharacterOrderBounds

/-!
# Cyclic-block conclusions from supplied principal characters

The actual principal characters and the Schur bounds give self-centralizing
Sylow subgroups of orders eleven and thirteen with odd automizers. Burnside
transfer excludes a trivial automizer, so their orders are five and three.
Sylow's congruence then gives the residues of the group order divided by the
corresponding prime. In Case II, the cyclic thirteen-block and Brauer--Tuan
intersection theorem also bound the three-part by 27.

The assembly retains the elementary-four subgroup and its actual odd-core
parameters. The character package and all three Schur bounds are explicit
inputs; their construction remains with the unconditional consumer. The last
corollary reuses the established numerical reductions in ThreeCharacterArithmetic.

Source: Alperin--Brauer--Gorenstein, III.8 Lemma 4 and Proposition 5,
article pp.116--117. The transfer adapters are adapted from the saved
SemidihedralCyclic/DraftSetup.lean development.
-/

namespace Stellmacher.Recognition
open ABG
namespace SemidihedralThreePrincipalCharacters
variable {G : Type*} [Group G] [Finite G] {x : G} {T : Subgroup G}
  (c : SemidihedralThreePrincipalCharacters G x T)

/-- Oddness determines the Case I automizer; transfer excludes order one. -/
public theorem case_one_automizer_eq_five [IsSimpleGroup G]
    (hf : c.degree 0 = 11) (hbound : Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11)
    (P : Sylow 11 G) (ho : Odd (automizerIndex (P : Subgroup G))) :
    automizerIndex (P : Subgroup G) = 5 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hP := c.case_one_sylow_card hf hbound P
  have hG : Nat.card G ≠ 11 := by
    have hg : 7920 ∣ Nat.card G := by rw [c.case_one_order hf]; exact dvd_mul_right _ _
    intro he
    rw [he] at hg
    norm_num at hg
  exact P.centralizer_relIndex_normalizer_eq_five_of_odd hP hG ho

/-- Oddness determines the Case II automizer; transfer excludes order one. -/
public theorem case_two_automizer_eq_three [IsSimpleGroup G]
    (hf : c.degree 1 = 13) (hbound : Nat.card G ∣ 16 * 3^8 * 5^3 * 7^2 * 11 * 13)
    (P : Sylow 13 G) (ho : Odd (automizerIndex (P : Subgroup G))) :
    automizerIndex (P : Subgroup G) = 3 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hP := c.case_two_sylow_card hf hbound P
  have hG : Nat.card G ≠ 13 := by
    have hg : 5616 ∣ Nat.card G := by rw [c.case_two_order hf]; exact dvd_mul_right _ _
    intro he
    rw [he] at hg
    norm_num at hg
  exact P.centralizer_relIndex_normalizer_eq_three_of_odd hP hG ho

/-- Case I: the self-centralizing Sylow-eleven normalizer has order 55,
so Sylow's congruence gives the residue five. -/
public theorem case_one_cyclic_congruence [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (hx : orderOf x = 2) (hT : IsElementaryAbelian 2 T)
    (hTcard : Nat.card T = 4) (hxT : x ∈ T)
    (hA : (threePrincipalCoreCentralizer x T).index ≠ 1)
    (hlocal : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 720)
    (hf : c.degree 0 = 11)
    (hbound : Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11) :
    (Nat.card G / 11) % 11 = 5 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let P : Sylow 11 G := Classical.choice inferInstance
  obtain ⟨hC, ho⟩ := c.case_one_sylow_geometry S hS hN hx hT hTcard hxT
    hA hlocal hf hbound P
  have hm := c.case_one_automizer_eq_five hf hbound P ho
  have hn := P.normalizer_card_of_self_centralizing (c.case_one_sylow_card hf hbound P) hC
  change Nat.card (Subgroup.normalizer (P : Set G)) =
    11 * automizerIndex (P : Subgroup G) at hn
  rw [hm] at hn
  exact P.card_div_prime_modEq_of_normalizer_card hn

/-- Case II: the normalizer order 39 gives the residue three, and the
cyclic thirteen-block bounds the three-part by 27. -/
public theorem case_two_cyclic_conclusions [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (hx : orderOf x = 2) (hT : IsElementaryAbelian 2 T)
    (hTcard : Nat.card T = 4) (hxT : x ∈ T)
    (hA : (threePrincipalCoreCentralizer x T).index ≠ 1)
    (hlocal : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 720)
    (hf : c.degree 1 = 13)
    (hbound : Nat.card G ∣ 16 * 3^8 * 5^3 * 7^2 * 11 * 13) :
    ¬ 81 ∣ Nat.card G ∧ (Nat.card G / 13) % 13 = 3 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  let P : Sylow 13 G := Classical.choice inferInstance
  have hP := c.case_two_sylow_card hf hbound P
  obtain ⟨hC, ho⟩ := c.case_two_sylow_geometry S hS hN hx hT hTcard hxT
    hA hlocal hf hbound P
  have hm := c.case_two_automizer_eq_three hf hbound P ho
  refine ⟨c.not_eightyOne_dvd_card hf P hP hC hm, ?_⟩
  have hn := P.normalizer_card_of_self_centralizing hP hC
  change Nat.card (Subgroup.normalizer (P : Set G)) =
    13 * automizerIndex (P : Subgroup G) at hn
  rw [hm] at hn
  exact P.card_div_prime_modEq_of_normalizer_card hn

end SemidihedralThreePrincipalCharacters

/-- The complete cyclic-block order alternatives from supplied principal
characters and Schur bounds, with the original elementary-four hypotheses. -/
public theorem semidihedral_three_cyclic_from_principalData
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T)
    (c : SemidihedralThreePrincipalCharacters G x T)
    (hA : (threePrincipalCoreCentralizer x T).index ≠ 1)
    (hlocal : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 720)
    (hbound₁ : c.degree 0 = 11 → Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11)
    (hbound₂ : c.degree 1 = 13 → Nat.card G ∣ 16 * 3^8 * 5^3 * 7^2 * 11 * 13) :
    let A := threePrincipalCoreCentralizer x T
    (Nat.card G = 7920 * (Nat.card A * A.index^3) ∧
      Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11 ∧ (Nat.card G / 11) % 11 = 5) ∨
    (Nat.card G = 5616 * (Nat.card A * A.index^3) ∧
      ¬ 81 ∣ Nat.card G ∧ (Nat.card G / 13) % 13 = 3) := by
  rcases c.alternatives with h | h
  · exact Or.inl ⟨h.2.2.2.2.2, hbound₁ h.1,
      c.case_one_cyclic_congruence S hS hN hx inferInstance hT hxT hA hlocal h.1
        (hbound₁ h.1)⟩
  · exact Or.inr ⟨h.2.2.2.2.2,
      c.case_two_cyclic_conclusions S hS hN hx inferInstance hT hxT hA hlocal h.2.1
        (hbound₂ h.2.1)⟩

/-- The established numerical reductions applied to the actual core parameters. -/
public theorem semidihedral_three_character_bounds_from_principalData
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T)
    (c : SemidihedralThreePrincipalCharacters G x T)
    (hA : (threePrincipalCoreCentralizer x T).index ≠ 1)
    (hlocal : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 720)
    (hbound₁ : c.degree 0 = 11 → Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11)
    (hbound₂ : c.degree 1 = 13 → Nat.card G ∣ 16 * 3^8 * 5^3 * 7^2 * 11 * 13) :
    let A := threePrincipalCoreCentralizer x T
    let a := Nat.card A
    let b := A.index
    a * b ∣ 15 ∧
      ((a * b^3 ∣ 3^4 * 5 ∧ a * b^3 % 11 = 1) ∨
        (Nat.Coprime (a * b) 3 ∧ a * b^3 % 13 = 1)) := by
  exact semidihedral_three_character_bounds_of_order_data S hS hN x hx T
    (fun _ => ⟨hlocal, semidihedral_three_cyclic_from_principalData
      S hS hN x hx T hT hxT c hA hlocal hbound₁ hbound₂⟩) hA

end Stellmacher.Recognition
