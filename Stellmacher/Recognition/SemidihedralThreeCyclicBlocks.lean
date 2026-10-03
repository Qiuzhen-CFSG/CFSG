module

public import Stellmacher.Recognition.SemidihedralThreeSchurBounds
public import Stellmacher.Recognition.SemidihedralThreeCyclicFromPrincipalData

/-!
# Cyclic-block conclusions for the semidihedral characteristic-three case

The principal-character catalogue and the local and global Schur bounds
discharge all inputs to the cyclic-block argument. Its self-centralizing
Sylow subgroups have orders eleven and thirteen and automizer orders five
and three, respectively. Sylow's congruence gives the two order residues;
the cyclic thirteen-block and Brauer--Tuan argument exclude a three-part
divisible by 81 in Case II.

The assembled alternatives retain the actual odd-core centralizer and its
index. The case-specific corollaries select the alternative by its group-order
formula, without requiring a supplied character witness. The final numerical
character bounds are left to the consuming assembly.

Source: Alperin--Brauer--Gorenstein, III.8 Lemma 4 and Proposition 5,
article pp.116--117; Brauer--Tuan, On simple groups of finite order I (1945),
Lemmas 2--3, as used in the cyclic-block prerequisite.
-/

namespace Stellmacher.Recognition

private theorem order_alternatives_disjoint {g m : ℕ} (hg : 0 < g)
    (h₁ : g = 7920 * m) (h₂ : g = 5616 * m) : False := by
  omega

/-- The cyclic-block conclusions and local Schur bound, constructed from the
original simple semidihedral N₂ hypotheses and the actual core parameters. -/
public theorem semidihedral_three_cyclic_blocks
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T) :
    let N := Subgroup.centralizer ({x} : Set G)
    let K := (pPrimeCore 2 N).map N.subtype
    let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
    let a := Nat.card A
    let b := A.index
    b ≠ 1 → Nat.card N ∣ 720 ∧
      ((Nat.card G = 7920 * (a * b^3) ∧
          Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11 ∧ (Nat.card G / 11) % 11 = 5) ∨
       (Nat.card G = 5616 * (a * b^3) ∧
          ¬ 81 ∣ Nat.card G ∧ (Nat.card G / 13) % 13 = 3)) := by
  obtain ⟨c⟩ := exists_semidihedralThreePrincipalCharacters S hS hN x hx T hT hxT
  dsimp only
  intro hb
  obtain ⟨hlocal, hbound₁, hbound₂⟩ := semidihedral_three_schur_bounds_from_principalData
    S hS hN x hx T hT hxT c.toThreePrincipalData hb
  exact ⟨hlocal, semidihedral_three_cyclic_from_principalData
    S hS hN x hx T hT hxT c hb hlocal hbound₁ hbound₂⟩

/-- Case I of ABG III.8 Proposition 5: the Sylow-eleven normalizer gives
the residue five for the group order divided by eleven. -/
public theorem semidihedral_three_case_one_cyclic_congruence
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T) :
    let A := threePrincipalCoreCentralizer x T
    A.index ≠ 1 →
      Nat.card G = 7920 * (Nat.card A * A.index^3) → (Nat.card G / 11) % 11 = 5 := by
  dsimp only
  intro hb horder
  obtain ⟨_, hcases⟩ := semidihedral_three_cyclic_blocks S hS hN x hx T hT hxT hb
  rcases hcases with h | h
  · exact h.2.2
  · exact (order_alternatives_disjoint Nat.card_pos horder h.1).elim

/-- Case II of ABG III.8 Proposition 5: Brauer--Tuan bounds the three-part
by 27, and the Sylow-thirteen normalizer gives the residue three. -/
public theorem semidihedral_three_case_two_cyclic_conclusions
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T) :
    let A := threePrincipalCoreCentralizer x T
    A.index ≠ 1 →
      Nat.card G = 5616 * (Nat.card A * A.index^3) →
        ¬ 81 ∣ Nat.card G ∧ (Nat.card G / 13) % 13 = 3 := by
  dsimp only
  intro hb horder
  obtain ⟨_, hcases⟩ := semidihedral_three_cyclic_blocks S hS hN x hx T hT hxT hb
  rcases hcases with h | h
  · exact (order_alternatives_disjoint Nat.card_pos h.1 horder).elim
  · exact h.2

end Stellmacher.Recognition
