module
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.PGroup.NormalPrimeImage
public import Theory.GroupTheory.PGroup.ClassTwoFixedFrattiniRank
public import Theory.GroupTheory.PGroup.SupercriticalExistence.ClassTwoOmega
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# Normal extraspecial factors under an odd rank-two bound

Two normal extraspecial subgroups of order p³ and exponent p cannot have
intersection of order at most p when their join has p-rank at most two.
Their centers and small intersection are central in the generated p-group,
so the join has class at most two and exponent p. The rank-two order bound
forces the join to have order at most p³ and both factors to equal it.

Source: Aschbacher--Smith, proof of 9.4.1, printed p.736, the common
Frattini-line case of the Xi fusion argument.
-/

public section
namespace Subgroup
open Subgroup Theory.GroupTheory
open scoped commutatorElement

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]

private theorem extraspecial_center_central
    (hP : IsPGroup p P) (A : Subgroup P) [A.Normal] [IsExtraspecial p A] :
    (center A).map A.subtype ≤ center P := by
  let Z := (center A).map A.subtype
  have hn : (⊤ : Subgroup P) ≤ normalizer (Z : Set P) := by
    have hh := normalizer_le_normalizer_characteristic_image A (center A)
    simpa only [normalizer_eq_top] using hh
  let _ : Z.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  exact hP.normal_le_center_of_card_dvd_prime Z (by
    rw [card_map_of_injective A.subtype_injective, IsExtraspecial.center_order_p p A])

theorem normal_extraspecial_pair_eq_of_rank_two
    (hP : IsPGroup p P) (hp : p ≠ 2)
    (A B : Subgroup P) [A.Normal] [B.Normal]
    [IsExtraspecial p A] [IsExtraspecial p B]
    (hAcard : Nat.card A = p ^ 3) (hBcard : Nat.card B = p ^ 3)
    (hAexp : Monoid.exponent A = p) (hBexp : Monoid.exponent B = p)
    (hgen : A ⊔ B = ⊤) (hI : Nat.card (A ⊓ B : Subgroup P) ≤ p)
    (hr : primeRank p P ≤ 2) : A = B := by
  have hAc := extraspecial_center_central hP A
  have hBc := extraspecial_center_central hP B
  have hIdvd : Nat.card (A ⊓ B : Subgroup P) ∣ p := by
    obtain ⟨n, hn⟩ := (hP.to_subgroup (A ⊓ B)).exists_card_eq
    have hn1 : n ≤ 1 := by
      apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
      simpa only [pow_one] using hn ▸ hI
    rw [hn]
    simpa using (pow_dvd_pow p hn1)
  have hIc : A ⊓ B ≤ center P := hP.normal_le_center_of_card_dvd_prime _ hIdvd
  have hAA : ⁅A,A⁆ ≤ center P := by
    rw [← map_subtype_commutator, IsExtraspecial.commutator_eq_center (p := p)]
    exact hAc
  have hBB : ⁅B,B⁆ ≤ center P := by
    rw [← map_subtype_commutator, IsExtraspecial.commutator_eq_center (p := p)]
    exact hBc
  have hAB : ⁅A,B⁆ ≤ center P :=
    (le_inf (commutator_le_left A B) (commutator_le_right A B)).trans hIc
  have hBA : ⁅B,A⁆ ≤ center P := by simpa only [commutator_comm B A] using hAB
  have hZA : ⁅(⊤ : Subgroup P),A⁆ ≤ center P := by
    rw [← hgen]
    exact commutator_sup_le_of_relative_normal ⊤ A B A (center P)
      le_normalizer_of_normal le_top le_top hAA hBA
  have hZB : ⁅(⊤ : Subgroup P),B⁆ ≤ center P := by
    rw [← hgen]
    exact commutator_sup_le_of_relative_normal ⊤ A B B (center P)
      le_normalizer_of_normal le_top le_top hAB hBB
  have hclass : _root_.commutator P ≤ center P := by
    change ⁅(⊤ : Subgroup P),⊤⁆ ≤ center P
    rw [← hgen]
    exact commutator_sup_le_of_relative_normal ⊤ A B (A ⊔ B) (center P)
      le_normalizer_of_normal le_top le_top
      (by simpa only [hgen, commutator_comm A ⊤] using hZA)
      (by simpa only [hgen, commutator_comm B ⊤] using hZB)
  have hpow : ∀ x : P, x ^ p = 1 := by
    intro x
    have hx : x ∈ A ⊔ B := hgen ▸ mem_top x
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_right.mp hx
    apply mul_pow_eq_one_of_class_two hp hclass
    · have hh := Monoid.pow_exponent_eq_one (⟨a,ha⟩ : A)
      rw [hAexp] at hh
      exact congrArg Subtype.val hh
    · have hh := Monoid.pow_exponent_eq_one (⟨b,hb⟩ : B)
      rw [hBexp] at hh
      exact congrArg Subtype.val hh
  have hnc : ¬ IsMulCommutative P := by
    intro hab
    let _ := hab
    have hcenter : center A = ⊤ := center_eq_top_iff.mpr inferInstance
    exact QuotientGroup.nontrivial_iff.mp
      (IsExtraspecial.quotient_nontrivial p A) hcenter
  have htwo : primeRank p P = 2 := by
    by_contra htwo
    have hone : primeRank p P ≤ 1 := by omega
    let _ : IsCyclic P := hP.isCyclic_of_odd_of_elementary_card_le
      ((Fact.out : p.Prime).odd_of_ne_two hp) (fun E hE => by
        let _ := hE
        exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hone E)
    exact hnc inferInstance
  have hnt : Nontrivial P := by
    rcases subsingleton_or_nontrivial P with h | h
    · let _ := h
      exact (hnc inferInstance).elim
    · exact h
  let _ := hnt
  have hexp : Monoid.exponent P = p :=
    (Monoid.exponent_eq_prime_iff (Fact.out : p.Prime)).mpr
      (fun x hx => orderOf_eq_prime (hpow x) hx)
  have hcard : Nat.card P ≤ p ^ 3 :=
    hP.card_le_prime_cube_of_exponent_prime_rank_two hp hexp htwo hclass
  have hAtop : A = ⊤ := eq_of_le_of_card_ge le_top
    (by simpa only [card_top, hAcard] using hcard)
  have hBtop : B = ⊤ := eq_of_le_of_card_ge le_top
    (by simpa only [card_top, hBcard] using hcard)
  exact hAtop.trans hBtop.symm

theorem normal_extraspecial_pair_eq_of_join_rank_two
    {G : Type*} [Group G] [Finite G] (hp : p ≠ 2)
    (A B : Subgroup G) [A.Normal] [B.Normal]
    [IsExtraspecial p A] [IsExtraspecial p B]
    (hAcard : Nat.card A = p ^ 3) (hBcard : Nat.card B = p ^ 3)
    (hAexp : Monoid.exponent A = p) (hBexp : Monoid.exponent B = p)
    (hI : Nat.card (A ⊓ B : Subgroup G) ≤ p)
    (hr : primeRank p (A ⊔ B : Subgroup G) ≤ 2) : A = B := by
  let J := A ⊔ B
  let A' := A.subgroupOf J
  let B' := B.subgroupOf J
  let eA : A' ≃* A := subgroupOfEquivOfLe le_sup_left
  let eB : B' ≃* B := subgroupOfEquivOfLe le_sup_right
  let : IsExtraspecial p A' := IsExtraspecial.of_mulEquiv eA.symm inferInstance
  let : IsExtraspecial p B' := IsExtraspecial.of_mulEquiv eB.symm inferInstance
  have hi : Nat.card (A' ⊓ B' : Subgroup J) ≤ p := by
    change Nat.card ((A ⊓ B : Subgroup G).subgroupOf J) ≤ p
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show A ⊓ B ≤ J from inf_le_left.trans le_sup_left)).toEquiv]
    exact hI
  have hpJ : IsPGroup p J :=
    (IsPGroup.of_card hAcard).to_sup_of_normal_right (IsPGroup.of_card hBcard)
  have he := normal_extraspecial_pair_eq_of_rank_two hpJ hp A' B'
    ((Nat.card_congr eA.toEquiv).trans hAcard) ((Nat.card_congr eB.toEquiv).trans hBcard)
    ((Monoid.exponent_eq_of_mulEquiv eA).trans hAexp)
    ((Monoid.exponent_eq_of_mulEquiv eB).trans hBexp)
    (codisjoint_subgroupOf_sup A B).eq_top hi hr
  have hh := congrArg (Subgroup.map J.subtype) he
  change (A.subgroupOf J).map J.subtype = (B.subgroupOf J).map J.subtype at hh
  simpa only [map_subgroupOf_eq_of_le (show A ≤ J from le_sup_left),
    map_subgroupOf_eq_of_le (show B ≤ J from le_sup_right)] using hh

end Subgroup
