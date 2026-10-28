module

public import Stellmacher.SectionOne.SmallMProof.QuotientAction

/-!
# Extracting the SL2 alternative and its odd-core generation

Fixed index on an invariant submodule cannot exceed full fixed index. Thus m=1 eliminates the small, exceptional and omega-product constructors of the recorded conclusion, leaving the exact SL2 data. Coprime-core factorization identifies its odd core as a three-group.

The standing Section 1 hypotheses and subgroup/cardinality conditions are
explicit. This is the recursive proof used for the restricted conclusion
`m(S) ≤ 1`; the unrestricted source-facing theorem is not used.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.17–19,
and its offender application in (1.7).
-/

open scoped BigOperators Pointwise commutatorElement

namespace Stellmacher.SectionOne.SmallMProof

universe u

open RankOneThreeGroupAssembly

private theorem fixedQuotientCard_eq_cast_relIndex
    {G V : Type u} [Group G] [Group V] [Finite V]
    [MulDistribMulAction G V] (A : Subgroup G) (X : Subgroup V) :
    fixedQuotientCard (G := G) (V := V) A X =
      (((X ⊓ FixedPoints.subgroup A V).relIndex X : ℕ) : ℚ) := by
  let C := FixedPoints.subgroup A V
  have hcardSub : Nat.card ((X ⊓ C).subgroupOf X) = Nat.card ↑(X ⊓ C) :=
    natCard_subgroupOf_eq (X ⊓ C) X inf_le_left
  have hmul := Subgroup.index_mul_card (H := (X ⊓ C).subgroupOf X)
  rw [hcardSub] at hmul
  have hden : (Nat.card ↑(X ⊓ C) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↑(X ⊓ C))).ne'
  unfold fixedQuotientCard
  change (Nat.card X : ℚ) / (Nat.card ↑(X ⊓ C) : ℚ) = _
  apply (div_eq_iff hden).2
  rw [← Nat.cast_mul]
  exact_mod_cast hmul.symm

private theorem fixedQuotientCard_le_full_fixedQuotient
    {G V : Type u} [Group G] [Group V] [Finite V]
    [MulDistribMulAction G V] (A : Subgroup G) (X : Subgroup V) :
    fixedQuotientCard (G := G) (V := V) A X ≤
      (Nat.card V : ℚ) / Nat.card (FixedPoints.subgroup A V) := by
  let C := FixedPoints.subgroup A V
  rw [fixedQuotientCard_eq_cast_relIndex]
  have hrel : (X ⊓ C).relIndex X ≤ C.index := by
    rw [Subgroup.inf_relIndex_left, ← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top Subgroup.index_ne_zero_of_finite
  have hmul := Subgroup.index_mul_card (H := C)
  have hden : (Nat.card C : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := C)).ne'
  have hratio : (Nat.card V : ℚ) / Nat.card C = (C.index : ℚ) := by
    apply (div_eq_iff hden).2
    rw [← Nat.cast_mul]
    exact_mod_cast hmul.symm
  rw [hratio]
  exact_mod_cast hrel

private theorem full_fixedQuotient_eq_card_of_m_eq_one
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (A : Subgroup G)
    (hm : m (G := G) (V := V) A = 1) :
    (Nat.card V : ℚ) / Nat.card (FixedPoints.subgroup A V) = Nat.card A := by
  have hfix : (Nat.card (FixedPoints.subgroup A V) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := FixedPoints.subgroup A V)).ne'
  have hA : (Nat.card A : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := A)).ne'
  unfold m at hm
  apply (div_eq_iff hfix).2
  have hprod : (Nat.card (FixedPoints.subgroup A V) : ℚ) * Nat.card A ≠ 0 :=
    mul_ne_zero hfix hA
  have hnum := (div_eq_one_iff_eq hprod).1 hm
  exact hnum.trans (mul_comm _ _)

public theorem oddCore_isPGroup_three_of_sl2Product
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (S : Subgroup G)
    (hprod : ∃ F : Finset (Subgroup G),
      (∀ E : Subgroup G, E ∈ F →
        IsSL2Two (↑E) ∧
          oneOmega (G := G) (V := V)
            ((commutator (↑E)).map E.subtype)) ∧
      IsInternalDirectProduct (oddCore G ⊔ S) F) :
    IsPGroup 3 (oddCore G) ∧
      ∃ F : Finset (Subgroup G),
        (∀ E : Subgroup G, E ∈ F →
          IsSL2Two (↑E) ∧
            oneOmega (G := G) (V := V)
              ((commutator (↑E)).map E.subtype)) ∧
        IsInternalDirectProduct (oddCore G ⊔ S) F ∧
        (oddCore G).subgroupOf (oddCore G ⊔ S) =
          ⨆ E : {E : Subgroup G // E ∈ F},
            ⁅(E : Subgroup G).subgroupOf (oddCore G ⊔ S),
              (E : Subgroup G).subgroupOf (oddCore G ⊔ S)⁆ := by
  classical
  obtain ⟨F, hEF, hprod⟩ := hprod
  let H : Subgroup G := pPrimeCore 2 G ⊔ S
  have hEleH (E : Subgroup G) (hE_mem : E ∈ F) : E ≤ H := by
    change E ≤ pPrimeCore 2 G ⊔ S
    have hgen := hprod.1
    change pPrimeCore 2 G ⊔ S =
      ⨆ E' : {E' : Subgroup G // E' ∈ F}, (E' : Subgroup G) at hgen
    rw [hgen]
    exact le_iSup (fun E' : {E' : Subgroup G // E' ∈ F} => (E' : Subgroup G))
      ⟨E, hE_mem⟩
  let EH (E : Subgroup G) : Subgroup H := E.subgroupOf H
  let DE (E : Subgroup G) : Subgroup H := ⁅EH E, EH E⁆
  have hEHnormal (E : Subgroup G) (hE_mem : E ∈ F) : (EH E).Normal := by
    have hnormal := hprod.2.1 E hE_mem
    have hH : oddCore G ⊔ S = H := rfl
    rw [hH] at hnormal
    exact hnormal
  have hDEmap (E : Subgroup G) (hE_mem : E ∈ F) :
      (DE E).map H.subtype = (commutator E).map E.subtype := by
    calc
      (DE E).map H.subtype = ⁅E, E⁆ := by
        exact commutator_subgroupOf_map_eq H E E
          (hEleH E hE_mem) (hEleH E hE_mem)
      _ = (commutator E).map E.subtype :=
        (Subgroup.map_subtype_commutator E).symm
  have hDEcard (E : Subgroup G) (hE_mem : E ∈ F) : Nat.card (DE E) = 3 := by
    have hcardAmbient : Nat.card ((commutator E).map E.subtype) = 3 :=
      (hEF E hE_mem).2.2.1
    rw [← hDEmap E hE_mem] at hcardAmbient
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective (DE E) H.subtype H.subtype_injective).toEquiv).trans
      hcardAmbient
  have hDEp (E : Subgroup G) (hE_mem : E ∈ F) : IsPGroup 3 (DE E) :=
    IsPGroup.of_card (p := 3) (n := 1) (by simpa using hDEcard E hE_mem)
  have hEHcard (E : Subgroup G) (hE_mem : E ∈ F) : Nat.card (EH E) = 6 := by
    rw [natCard_subgroupOf_eq E H (hEleH E hE_mem)]
    exact isSL2Two_card (hEF E hE_mem).1
  have hDEleEH (E : Subgroup G) : DE E ≤ EH E :=
    Subgroup.commutator_le_self (EH E)
  have hDErelIndex (E : Subgroup G) (hE_mem : E ∈ F) :
      (DE E).relIndex (EH E) = 2 := by
    change ((DE E).subgroupOf (EH E)).index = 2
    have hmul := ((DE E).subgroupOf (EH E)).index_mul_card
    rw [natCard_subgroupOf_eq (DE E) (EH E) (hDEleEH E),
      hDEcard E hE_mem, hEHcard E hE_mem] at hmul
    omega
  have hDEeq (E : Subgroup G) :
      DE E = (commutator (EH E)).map (EH E).subtype :=
    (Subgroup.map_subtype_commutator (EH E)).symm
  have hderived_le : ∀ E : Subgroup G, E ∈ F →
      ⁅E, E⁆ ≤ pPrimeCore 2 G := by
    intro E hE_mem
    simpa only [oddCore, Subgroup.map_subtype_commutator] using
      (hEF E hE_mem).2.1
  have hderived_q : ∀ E : Subgroup G, E ∈ F →
      let H := pPrimeCore 2 G ⊔ S
      IsPGroup 3 ((commutator (E.subgroupOf H)).map
        (E.subgroupOf H).subtype) := by
    intro E hE_mem
    change IsPGroup 3 ((commutator (EH E)).map (EH E).subtype)
    rw [← hDEeq E]
    exact hDEp E hE_mem
  have hindex : ∀ E : Subgroup G, E ∈ F →
      let H := pPrimeCore 2 G ⊔ S
      ∃ n : ℕ, ((commutator (E.subgroupOf H)).map
        (E.subgroupOf H).subtype).relIndex (E.subgroupOf H) = 2 ^ n := by
    intro E hE_mem
    refine ⟨1, ?_⟩
    change ((commutator (EH E)).map (EH E).subtype).relIndex (EH E) = 2 ^ 1
    rw [← hDEeq E, pow_one]
    exact hDErelIndex E hE_mem
  have hgen : pPrimeCore 2 G ⊔ S =
      ⨆ E : {E : Subgroup G // E ∈ F}, (E : Subgroup G) := by
    simpa only [oddCore] using hprod.1
  have hnorm : ∀ E : Subgroup G, E ∈ F →
      (E.subgroupOf (pPrimeCore 2 G ⊔ S)).Normal :=
    fun E hE_mem => by simpa only [H] using hEHnormal E hE_mem
  refine ⟨pPrimeCore_isPGroup_of_generated_factors (p := 2) (q := 3)
    S F hgen hnorm hderived_le hderived_q hindex, ⟨F, hEF, hprod, ?_⟩⟩
  change (pPrimeCore 2 G).subgroupOf (pPrimeCore 2 G ⊔ S) =
    ⨆ E : {E : Subgroup G // E ∈ F},
      ⁅(E : Subgroup G).subgroupOf (pPrimeCore 2 G ⊔ S),
        (E : Subgroup G).subgroupOf (pPrimeCore 2 G ⊔ S)⁆
  exact pPrimeCore_subgroupOf_eq_iSup_commutator_of_generated_factors
    S F hgen hnorm hderived_le hindex

public theorem sl2Data_of_conclusion_of_m_eq_one
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (S : Subgroup G)
    (hm : m (G := G) (V := V) S = 1)
    (hc : LemmaOneSixConclusion (G := G) (V := V) S) :
    RankOneLocalSL2Data (G := G) (V := V) S := by
  have hfull : (Nat.card V : ℚ) /
      Nat.card (FixedPoints.subgroup S V) = Nat.card S :=
    full_fixedQuotient_eq_card_of_m_eq_one S hm
  cases hc with
  | small _ hgt =>
      rw [hm] at hgt
      norm_num at hgt
  | doubleSL2 hmTwo _ _ _ =>
      rw [hm] at hmTwo
      norm_num at hmTwo
  | omegaProduct hprod hquad hfixed =>
      have hle := fixedQuotientCard_le_full_fixedQuotient S
        (commutatorAction (oddCore G) V)
      rw [hfixed, hfull] at hle
      have hpos : (0 : ℚ) < Nat.card S := by
        exact_mod_cast Nat.card_pos ( α := S)
      norm_num at hle
  | sl2Product hprod hquad hfixed =>
      exact ⟨hprod, hquad, hfixed⟩

end Stellmacher.SectionOne.SmallMProof
