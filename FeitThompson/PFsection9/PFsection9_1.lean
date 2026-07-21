module

import FeitThompson.BGsection3.Remaining
import FeitThompson.Wielandt
public import FeitThompson.PFsection9.Basic

noncomputable section

open scoped BigOperators

namespace Section9

universe v
universe w
universe u

public theorem subgroupCentralizerIn_sup_le_left_sec9
    {G : Type u} [Group G]
    (H U E : Subgroup G) :
    subgroupCentralizerIn H (U ⊔ E) ≤ subgroupCentralizerIn H U := by
  intro x hx
  have hx' : x ∈ H ∧ x ∈ Subgroup.centralizer ((U ⊔ E : Subgroup G) : Set G) := by
    simpa [subgroupCentralizerIn] using hx
  have hxU : x ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hx' ⊢
    intro u hu
    exact hx'.2 u ((show U ≤ U ⊔ E from le_sup_left) hu)
  simpa [subgroupCentralizerIn] using And.intro hx'.1 hxU

public theorem subgroupCentralizerIn_sup_le_right_sec9
    {G : Type u} [Group G]
    (H U E : Subgroup G) :
    subgroupCentralizerIn H (U ⊔ E) ≤ subgroupCentralizerIn H E := by
  intro x hx
  have hx' : x ∈ H ∧ x ∈ Subgroup.centralizer ((U ⊔ E : Subgroup G) : Set G) := by
    simpa [subgroupCentralizerIn] using hx
  have hxE : x ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hx' ⊢
    intro e he
    exact hx'.2 e ((show E ≤ U ⊔ E from le_sup_right) he)
  simpa [subgroupCentralizerIn] using And.intro hx'.1 hxE

public theorem subgroupCentralizerIn_eq_left_of_card_eq_sec9
    {G : Type u} [Group G] [Finite G]
    (H S : Subgroup G) :
    Nat.card (subgroupCentralizerIn H S) = Nat.card H →
      subgroupCentralizerIn H S = H := by
  intro hcard
  let Csub : Subgroup H := (subgroupCentralizerIn H S).subgroupOf H
  have hCsub_card : Nat.card Csub = Nat.card H := by
    simpa [Csub] using
      (natCard_subgroupOf_eq (subgroupCentralizerIn H S) H inf_le_left).trans hcard
  have hCsub_top : Csub = ⊤ :=
    (Subgroup.card_eq_iff_eq_top (H := Csub)).1 hCsub_card
  apply le_antisymm
  · exact inf_le_left
  · intro x hxH
    have hxCsub : (⟨x, hxH⟩ : H) ∈ Csub := by
      simp [hCsub_top]
    simpa [Csub, Subgroup.mem_subgroupOf] using hxCsub

private theorem frobeniusActionData_nat_card_eq_mul_sec9
    {G : Type u} [Group G] [Finite G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      Nat.card UE = Nat.card U * Nat.card E := by
  classical
  intro h91
  rcases h91 with ⟨hcomp, hfrob, _hUE_norm_H, _hH_solv, _hcop⟩
  have hUnorm : (U.subgroupOf UE).Normal := by
    have hUnormSup : (U.subgroupOf (U ⊔ E)).Normal :=
      IsFrobeniusGroupWithKernelComplement.normal hfrob
    have hUEeq : UE = U ⊔ E := hcomp.2.2.1
    subst UE
    simpa using hUnormSup
  have hdisjSub : Disjoint (U.subgroupOf UE) (E.subgroupOf UE) := by
    have hdisj := hcomp.2.2.2
    rw [disjoint_iff] at hdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ U ⊓ E := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf] using hx.1,
          by simpa [Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hsupTop : U.subgroupOf UE ⊔ E.subgroupOf UE = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := U) (A' := E) (B := UE) hcomp.1 hcomp.2.1]
    rw [← hcomp.2.2.1]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  have hcompSub : (U.subgroupOf UE).IsComplement' (E.subgroupOf UE) := by
    letI : (U.subgroupOf UE).Normal := hUnorm
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (U.subgroupOf UE) (E.subgroupOf UE) hdisjSub hsupTop
  have hmul := hcompSub.card_mul
  simpa [natCard_subgroupOf_eq U UE hcomp.1,
    natCard_subgroupOf_eq E UE hcomp.2.1] using hmul.symm

private theorem subgroupCentralizerIn_conjBy_nat_card_eq_of_mem_normalizer_sec9
    {G : Type u} [Group G] [Finite G]
    (H E : Subgroup G) {g : G}
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) :
    Nat.card (subgroupCentralizerIn H (E.conjBy g)) =
      Nat.card (subgroupCentralizerIn H E) := by
  rw [section11_subgroupCentralizerIn_conjBy_eq_self_of_mem_normalizer hgH]
  exact section11_card_conjBy (subgroupCentralizerIn H E) g

private noncomputable def theorem_9_1_conjugate_complement_product_sec9
    {G : Type u} [Group G] [Finite G]
    (U E H : Subgroup G) : ℕ :=
  letI : Fintype U := Fintype.ofFinite U
  ∏ u : U,
    Nat.card (subgroupCentralizerIn H (E.conjBy (u : G))) ^
      Nat.card (E.conjBy (u : G))

private theorem frobeniusActionData_conjugate_complement_product_eq_power_sec9
    {G : Type u} [Group G] [Finite G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      theorem_9_1_conjugate_complement_product_sec9 U E H =
        Nat.card (subgroupCentralizerIn H E) ^ (Nat.card E * Nat.card U) := by
  intro h91
  letI : Fintype U := Fintype.ofFinite U
  dsimp [theorem_9_1_conjugate_complement_product_sec9]
  rcases h91 with ⟨hcomp, _hfrob, hUE_norm_H, _hH_solv, _hcop⟩
  have hterm : ∀ u : U,
      Nat.card (subgroupCentralizerIn H (E.conjBy (u : G))) ^
          Nat.card (E.conjBy (u : G)) =
        Nat.card (subgroupCentralizerIn H E) ^ Nat.card E := by
    intro u
    have hu_norm : (u : G) ∈ Subgroup.normalizer (H : Set G) :=
      hUE_norm_H (hcomp.1 u.property)
    have hcent :=
      subgroupCentralizerIn_conjBy_nat_card_eq_of_mem_normalizer_sec9 H E hu_norm
    have hEcard : Nat.card (E.conjBy (u : G)) = Nat.card E :=
      section11_card_conjBy E (u : G)
    rw [hcent, hEcard]
  calc
    (∏ u : U,
        Nat.card (subgroupCentralizerIn H (E.conjBy (u : G))) ^
          Nat.card (E.conjBy (u : G)))
        = ∏ _u : U, Nat.card (subgroupCentralizerIn H E) ^ Nat.card E := by
          exact Finset.prod_congr rfl (fun u _hu => hterm u)
    _ = (Nat.card (subgroupCentralizerIn H E) ^ Nat.card E) ^ Nat.card U := by
      rw [Finset.prod_const]
      simp [Nat.card_eq_fintype_card]
    _ = Nat.card (subgroupCentralizerIn H E) ^ (Nat.card E * Nat.card U) := by
      rw [pow_mul]

private theorem fixedPointSubgroup_card_eq_subgroupCentralizerIn_sec9
    {G : Type u} [Group G] [Finite G]
    (H R : Subgroup G)
    (hRnormH : R ≤ Subgroup.normalizer (H : Set G)) :
    letI : Subgroup.Normalizes R H := ⟨hRnormH⟩
    Nat.card (fixedPointSubgroup (↥R) H) =
      Nat.card (subgroupCentralizerIn H R) := by
  letI : Subgroup.Normalizes R H := ⟨hRnormH⟩
  have hfix : fixedPointSubgroup (↥R) H =
      (subgroupCentralizerIn H R).subgroupOf H := by
    simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn H R hRnormH
  calc
    Nat.card (fixedPointSubgroup (↥R) H) =
        Nat.card ((subgroupCentralizerIn H R).subgroupOf H) := by
          rw [hfix]
    _ = Nat.card (subgroupCentralizerIn H R) := by
          exact natCard_subgroupOf_eq (subgroupCentralizerIn H R) H inf_le_left

private theorem fixedPointSubgroup_subgroupOf_actor_eq_sec9
    {A M : Type u} [Group A] [Group M] [MulDistribMulAction A M]
    {S B : Subgroup A} (hB_le : B ≤ S) :
    letI : MulDistribMulAction (↥S) M := MulDistribMulAction.compHom M S.subtype
    fixedPointSubgroup (↥(B.subgroupOf S)) M = fixedPointSubgroup (↥B) M := by
  letI : MulDistribMulAction (↥S) M := MulDistribMulAction.compHom M S.subtype
  ext x
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hx b
    have hb :
        (⟨⟨(b : A), hB_le b.2⟩, by
          show ((⟨(b : A), hB_le b.2⟩ : S) : A) ∈ B
          exact b.2⟩ : B.subgroupOf S) • x = x :=
      hx ⟨⟨(b : A), hB_le b.2⟩, by
        show ((⟨(b : A), hB_le b.2⟩ : S) : A) ∈ B
        exact b.2⟩
    simpa using hb
  · intro hx b
    have hb : ((⟨(b : S), by
      show ((b : S) : A) ∈ B
      exact b.2⟩ : B) : A) • x = x := by
      exact hx ⟨(b : S), by
        show ((b : S) : A) ∈ B
        exact b.2⟩
    simpa using hb

private theorem isInvariant_of_le_actor_sec9
    {G : Type u} [Group G]
    (A B H : Subgroup G) [Subgroup.Normalizes A H] [Subgroup.Normalizes B H]
    {N : Subgroup H}
    (hBA : B ≤ A)
    (hNinv : IsInvariant (↥A) H N) :
    IsInvariant (↥B) H N := by
  refine ⟨?_⟩
  intro b x
  have hA :=
    IsInvariant.invariant (A := ↥A) (G := H) (H := N)
      (⟨(b : G), hBA b.2⟩ : A) x
  constructor
  · intro hx
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hA.1 hx
  · intro hx
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hA.2 hx

private theorem fixedPointSubgroup_subgroupOf_conj_actor_eq_sec9
    {G : Type u} [Group G]
    (A B H : Subgroup G) [Subgroup.Normalizes A H] [Subgroup.Normalizes B H]
    (hBA : B ≤ A) :
    letI : MulDistribMulAction (↥(B.subgroupOf A)) H :=
      MulDistribMulAction.compHom H (B.subgroupOf A).subtype
    fixedPointSubgroup (↥(B.subgroupOf A)) H = fixedPointSubgroup (↥B) H := by
  letI : MulDistribMulAction (↥(B.subgroupOf A)) H :=
    MulDistribMulAction.compHom H (B.subgroupOf A).subtype
  ext x
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hx b
    have hb :
        (⟨⟨(b : G), hBA b.2⟩, by
          show ((⟨(b : G), hBA b.2⟩ : A) : G) ∈ B
          exact b.2⟩ : B.subgroupOf A) • x = x :=
      hx ⟨⟨(b : G), hBA b.2⟩, by
        show ((⟨(b : G), hBA b.2⟩ : A) : G) ∈ B
        exact b.2⟩
    apply Subtype.ext
    simpa [MulAction.compHom_smul_def,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
      congrArg Subtype.val hb
  · intro hx b
    have hb : ((⟨(b : A), by
      show ((b : A) : G) ∈ B
      exact b.2⟩ : B) • x : H) = x := by
      exact hx ⟨(b : A), by
        show ((b : A) : G) ∈ B
        exact b.2⟩
    apply Subtype.ext
    simpa [MulAction.compHom_smul_def,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
      congrArg Subtype.val hb

private theorem theorem_9_1_fixedPointSubgroup_top_eq_sec9
    {A M : Type u} [Group A] [Group M] [MulDistribMulAction A M] :
    letI : MulDistribMulAction (↥(⊤ : Subgroup A)) M :=
      MulDistribMulAction.compHom M (⊤ : Subgroup A).subtype
    fixedPointSubgroup (↥(⊤ : Subgroup A)) M = fixedPointSubgroup A M := by
  letI : MulDistribMulAction (↥(⊤ : Subgroup A)) M :=
    MulDistribMulAction.compHom M (⊤ : Subgroup A).subtype
  ext x
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hx a
    have ha : (⟨a, by simp⟩ : (⊤ : Subgroup A)) • x = x := hx ⟨a, by simp⟩
    simpa using ha
  · intro hx a
    have ha : (a : A) • x = x := hx (a : A)
    simpa using ha

private theorem theorem_9_1_fixedPoint_card_eq_mul_quotient_action_sec9
    {A M : Type u} [Group A] [Finite A] [Group M] [Finite M]
    [MulDistribMulAction A M]
    {N : Subgroup M} [N.Normal]
    (hNinv : IsInvariant A M N)
    (hsolvM : IsSolvable M)
    (hcopA : Nat.Coprime (Nat.card A) (Nat.card M)) :
    letI : IsInvariant A M N := hNinv
    letI : MulDistribMulAction A (M ⧸ N) :=
      quotientMulDistribMulAction (A := A) (G := M) N hNinv
    Nat.card (fixedPointSubgroup A M) =
      Nat.card (fixedPointSubgroup A N) *
        Nat.card (fixedPointSubgroup A (M ⧸ N)) := by
  letI : IsInvariant A M N := hNinv
  letI : MulDistribMulAction A (M ⧸ N) :=
    quotientMulDistribMulAction (A := A) (G := M) N hNinv
  have hcopTop : Nat.Coprime (Nat.card (⊤ : Subgroup A)) (Nat.card M) := by
    simpa using hcopA
  have hfactor :=
    fixedPointSubgroup_card_eq_mul_quotient_of_solvable_coprime
      (G := A) (M := M) (R := (⊤ : Subgroup A)) (N := N)
      hNinv hsolvM hcopTop
  simpa [theorem_9_1_fixedPointSubgroup_top_eq_sec9] using hfactor

private theorem theorem_9_1_fixedPoint_card_eq_mul_quotient_sec9
    {G : Type u} [Group G] [Finite G]
    (A H : Subgroup G) [Subgroup.Normalizes A H]
    {N : Subgroup H} [N.Normal]
    (hNinv : IsInvariant A H N)
    (hsolvH : IsSolvable H)
    (hcopA : Nat.Coprime (Nat.card A) (Nat.card H)) :
    letI : IsInvariant A H N := hNinv
    letI : MulDistribMulAction A (H ⧸ N) :=
      quotientMulDistribMulAction (A := A) (G := H) N hNinv
    Nat.card (fixedPointSubgroup (↥A) H) =
      Nat.card (fixedPointSubgroup (↥A) N) *
        Nat.card (fixedPointSubgroup (↥A) (H ⧸ N)) := by
  letI : IsInvariant A H N := hNinv
  letI : MulDistribMulAction A (H ⧸ N) :=
    quotientMulDistribMulAction (A := A) (G := H) N hNinv
  have hcopTop : Nat.Coprime (Nat.card (⊤ : Subgroup A)) (Nat.card H) := by
    simpa using hcopA
  have hfactor :=
    fixedPointSubgroup_card_eq_mul_quotient_of_solvable_coprime
      (G := A) (M := H) (R := (⊤ : Subgroup A)) (N := N)
      hNinv hsolvH hcopTop
  simpa [theorem_9_1_fixedPointSubgroup_top_eq_sec9] using hfactor

private noncomputable def theorem_9_1_fixedPoint_conjugate_complement_product_sec9
    {G : Type u} [Group G] [Finite G]
    (U E H : Subgroup G)
    (hEnormH : ∀ u : U, E.conjBy (u : G) ≤ Subgroup.normalizer (H : Set G)) : ℕ :=
  letI : Fintype U := Fintype.ofFinite U
  ∏ u : U,
    letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
    Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) H) ^
      Nat.card (E.conjBy (u : G))

private theorem theorem_9_1_fixedPoint_conjugate_complement_product_eq_centralizer_product_sec9
    {G : Type u} [Group G] [Finite G]
    (U E H : Subgroup G)
    (hEnormH : ∀ u : U, E.conjBy (u : G) ≤ Subgroup.normalizer (H : Set G)) :
    theorem_9_1_fixedPoint_conjugate_complement_product_sec9 U E H hEnormH =
      theorem_9_1_conjugate_complement_product_sec9 U E H := by
  letI : Fintype U := Fintype.ofFinite U
  dsimp [theorem_9_1_fixedPoint_conjugate_complement_product_sec9,
    theorem_9_1_conjugate_complement_product_sec9]
  apply Finset.prod_congr rfl
  intro u _hu
  have hcard :=
    fixedPointSubgroup_card_eq_subgroupCentralizerIn_sec9 H
      (E.conjBy (u : G)) (hEnormH u)
  rw [hcard]

private theorem theorem_9_1_fixedPoint_product_lift_card_factors_sec9
    {ι : Type*} [Fintype ι]
    (aN aQ bN bQ dN dQ m n : ℕ)
    (cN cQ e : ι → ℕ)
    (hN : aN ^ m * bN ^ n = (∏ i, cN i ^ e i) * dN ^ n)
    (hQ : aQ ^ m * bQ ^ n = (∏ i, cQ i ^ e i) * dQ ^ n) :
    (aN * aQ) ^ m * (bN * bQ) ^ n =
      (∏ i, (cN i * cQ i) ^ e i) * (dN * dQ) ^ n := by
  classical
  calc
    (aN * aQ) ^ m * (bN * bQ) ^ n =
        (aN ^ m * bN ^ n) * (aQ ^ m * bQ ^ n) := by
          rw [Nat.mul_pow, Nat.mul_pow]
          ac_rfl
    _ = ((∏ i, cN i ^ e i) * dN ^ n) *
        ((∏ i, cQ i ^ e i) * dQ ^ n) := by
          rw [hN, hQ]
    _ = ((∏ i, cN i ^ e i) * (∏ i, cQ i ^ e i)) *
        (dN ^ n * dQ ^ n) := by
          ac_rfl
    _ = (∏ i, cN i ^ e i * cQ i ^ e i) * (dN * dQ) ^ n := by
          rw [← Finset.prod_mul_distrib, ← Nat.mul_pow]
    _ = (∏ i, (cN i * cQ i) ^ e i) * (dN * dQ) ^ n := by
          congr 1
          apply Finset.prod_congr rfl
          intro i _hi
          rw [Nat.mul_pow]

private theorem theorem_9_1_fixedPoint_conjugate_product_factor_sec9
    {G : Type u} [Group G] [Finite G]
    (U E H : Subgroup G)
    (hEnormH : ∀ u : U, E.conjBy (u : G) ≤ Subgroup.normalizer (H : Set G))
    (cN cQ : U → ℕ)
    (hfactor : ∀ u : U,
      letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
      Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) H) = cN u * cQ u) :
    letI : Fintype U := Fintype.ofFinite U
    theorem_9_1_fixedPoint_conjugate_complement_product_sec9 U E H hEnormH =
      (∏ u : U, cN u ^ Nat.card (E.conjBy (u : G))) *
        (∏ u : U, cQ u ^ Nat.card (E.conjBy (u : G))) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  dsimp [theorem_9_1_fixedPoint_conjugate_complement_product_sec9]
  calc
    (∏ u : U,
        (letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
         Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) H)) ^
          Nat.card (E.conjBy (u : G))) =
      ∏ u : U, (cN u * cQ u) ^ Nat.card (E.conjBy (u : G)) := by
        apply Finset.prod_congr rfl
        intro u _hu
        rw [hfactor u]
    _ = ∏ u : U,
        cN u ^ Nat.card (E.conjBy (u : G)) *
          cQ u ^ Nat.card (E.conjBy (u : G)) := by
        apply Finset.prod_congr rfl
        intro u _hu
        rw [Nat.mul_pow]
    _ = (∏ u : U, cN u ^ Nat.card (E.conjBy (u : G))) *
        (∏ u : U, cQ u ^ Nat.card (E.conjBy (u : G))) := by
        rw [Finset.prod_mul_distrib]

private theorem theorem_9_1_fixedPoint_conjugate_product_factor_combined_sec9
    {G : Type u} [Group G] [Finite G]
    (U E H : Subgroup G)
    (hEnormH : ∀ u : U, E.conjBy (u : G) ≤ Subgroup.normalizer (H : Set G))
    (cN cQ : U → ℕ)
    (hfactor : ∀ u : U,
      letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
      Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) H) = cN u * cQ u) :
    letI : Fintype U := Fintype.ofFinite U
    theorem_9_1_fixedPoint_conjugate_complement_product_sec9 U E H hEnormH =
      ∏ u : U, (cN u * cQ u) ^ Nat.card (E.conjBy (u : G)) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  dsimp [theorem_9_1_fixedPoint_conjugate_complement_product_sec9]
  apply Finset.prod_congr rfl
  intro u _hu
  rw [hfactor u]

private noncomputable def theorem_9_1_fixedPoint_conjugate_action_product_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (U E : Subgroup G)
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M) : ℕ :=
  letI : Fintype U := Fintype.ofFinite U
  ∏ u : U,
    letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) ^
      Nat.card (E.conjBy (u : G))

private theorem theorem_9_1_fixedPoint_conjugate_action_product_factor_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (U E : Subgroup G)
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (cN cQ : U → ℕ)
    (hfactor : ∀ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) = cN u * cQ u) :
    letI : Fintype U := Fintype.ofFinite U
    theorem_9_1_fixedPoint_conjugate_action_product_sec9 U E hEact =
      ∏ u : U, (cN u * cQ u) ^ Nat.card (E.conjBy (u : G)) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  dsimp [theorem_9_1_fixedPoint_conjugate_action_product_sec9]
  apply Finset.prod_congr rfl
  intro u _hu
  rw [hfactor u]

private theorem theorem_9_1_wielandt_fixedPoint_action_product_identity_lift_from_card_factors_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (aN aQ bN bQ dN dQ : ℕ)
    (cN cQ : U → ℕ)
    (hUEfactor :
      Nat.card (fixedPointSubgroup (↥UE) M) = aN * aQ)
    (hMfactor : Nat.card M = bN * bQ)
    (hUfactor :
      Nat.card (fixedPointSubgroup (↥U) M) = dN * dQ)
    (hEfactor : ∀ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) = cN u * cQ u)
    (hN :
      letI : Fintype U := Fintype.ofFinite U
      aN ^ Nat.card UE * bN ^ Nat.card U =
        (∏ u : U, cN u ^ Nat.card (E.conjBy (u : G))) * dN ^ Nat.card U)
    (hQ :
      letI : Fintype U := Fintype.ofFinite U
      aQ ^ Nat.card UE * bQ ^ Nat.card U =
        (∏ u : U, cQ u ^ Nat.card (E.conjBy (u : G))) * dQ ^ Nat.card U) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      theorem_9_1_fixedPoint_conjugate_action_product_sec9 U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  have hlift :=
    theorem_9_1_fixedPoint_product_lift_card_factors_sec9
      (aN := aN) (aQ := aQ) (bN := bN) (bQ := bQ)
      (dN := dN) (dQ := dQ) (m := Nat.card UE) (n := Nat.card U)
      (cN := cN) (cQ := cQ)
      (e := fun u : U => Nat.card (E.conjBy (u : G))) hN hQ
  have hprod :=
    theorem_9_1_fixedPoint_conjugate_action_product_factor_sec9
      U E hEact cN cQ hEfactor
  rw [hUEfactor, hMfactor, hUfactor, hprod]
  exact hlift

private theorem theorem_9_1_fixedPoint_conjugate_complement_product_eq_action_product_sec9
    {G : Type u} [Group G] [Finite G]
    (U E H : Subgroup G)
    (hEnormH : ∀ u : U, E.conjBy (u : G) ≤ Subgroup.normalizer (H : Set G)) :
    let hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) H := fun u => by
      letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
      infer_instance
    theorem_9_1_fixedPoint_conjugate_complement_product_sec9 U E H hEnormH =
      theorem_9_1_fixedPoint_conjugate_action_product_sec9 U E hEact := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  dsimp [theorem_9_1_fixedPoint_conjugate_complement_product_sec9,
    theorem_9_1_fixedPoint_conjugate_action_product_sec9]

private theorem theorem_9_1_wielandt_fixedPoint_product_identity_lift_from_card_factors_sec9
    {G : Type u} [Group G] [Finite G]
    (UE U E H : Subgroup G)
    (hUE_norm_H : UE ≤ Subgroup.normalizer (H : Set G))
    (hU_norm_H : U ≤ Subgroup.normalizer (H : Set G))
    (hEnormH : ∀ u : U, E.conjBy (u : G) ≤ Subgroup.normalizer (H : Set G))
    (aN aQ bN bQ dN dQ : ℕ)
    (cN cQ : U → ℕ)
    (hUEfactor :
      letI : Subgroup.Normalizes UE H := ⟨hUE_norm_H⟩
      Nat.card (fixedPointSubgroup (↥UE) H) = aN * aQ)
    (hHfactor : Nat.card H = bN * bQ)
    (hUfactor :
      letI : Subgroup.Normalizes U H := ⟨hU_norm_H⟩
      Nat.card (fixedPointSubgroup (↥U) H) = dN * dQ)
    (hEfactor : ∀ u : U,
      letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
      Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) H) = cN u * cQ u)
    (hN :
      letI : Fintype U := Fintype.ofFinite U
      aN ^ Nat.card UE * bN ^ Nat.card U =
        (∏ u : U, cN u ^ Nat.card (E.conjBy (u : G))) * dN ^ Nat.card U)
    (hQ :
      letI : Fintype U := Fintype.ofFinite U
      aQ ^ Nat.card UE * bQ ^ Nat.card U =
        (∏ u : U, cQ u ^ Nat.card (E.conjBy (u : G))) * dQ ^ Nat.card U) :
    letI : Subgroup.Normalizes UE H := ⟨hUE_norm_H⟩
    letI : Subgroup.Normalizes U H := ⟨hU_norm_H⟩
    Nat.card (fixedPointSubgroup (↥UE) H) ^ Nat.card UE *
        Nat.card H ^ Nat.card U =
      theorem_9_1_fixedPoint_conjugate_complement_product_sec9 U E H hEnormH *
        Nat.card (fixedPointSubgroup (↥U) H) ^ Nat.card U := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  letI : Subgroup.Normalizes UE H := ⟨hUE_norm_H⟩
  letI : Subgroup.Normalizes U H := ⟨hU_norm_H⟩
  have hlift :=
    theorem_9_1_fixedPoint_product_lift_card_factors_sec9
      (aN := aN) (aQ := aQ) (bN := bN) (bQ := bQ)
      (dN := dN) (dQ := dQ) (m := Nat.card UE) (n := Nat.card U)
      (cN := cN) (cQ := cQ)
      (e := fun u : U => Nat.card (E.conjBy (u : G))) hN hQ
  have hprod :=
    theorem_9_1_fixedPoint_conjugate_product_factor_combined_sec9
      U E H hEnormH cN cQ hEfactor
  rw [hUEfactor, hHfactor, hUfactor, hprod]
  exact hlift

private theorem theorem_9_1_conj_complement_le_frobenius_actor_sec9
    {G : Type u} [Group G] [Finite G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      ∀ u : U, E.conjBy (u : G) ≤ UE := by
  intro h91 u x hx
  rcases h91 with ⟨hcomp, _hfrob, _hUE_norm_H, _hH_solv, _hcop⟩
  rw [Subgroup.conjBy, Subgroup.mem_map] at hx
  rcases hx with ⟨e, heE, hxe⟩
  rw [← hxe]
  exact UE.mul_mem (UE.mul_mem (hcomp.1 u.property) (hcomp.2.1 heE))
    (UE.inv_mem (hcomp.1 u.property))

private theorem section12ComplementIn_conj_complement_le_sec9
    {G : Type u} [Group G]
    (UE U E : Subgroup G) :
    section12ComplementIn UE U E →
      ∀ u : U, E.conjBy (u : G) ≤ UE := by
  intro hcomp u x hx
  rw [Subgroup.conjBy, Subgroup.mem_map] at hx
  rcases hx with ⟨e, heE, hxe⟩
  rw [← hxe]
  exact UE.mul_mem (UE.mul_mem (hcomp.1 u.property) (hcomp.2.1 heE))
    (UE.inv_mem (hcomp.1 u.property))

private theorem isInvariant_of_compatible_le_actor_sec9
    {G M : Type u} [Group G] [Group M]
    (A B : Subgroup G)
    [MulDistribMulAction A M] [MulDistribMulAction B M]
    (hBA : B ≤ A)
    (hcompat : ∀ (b : B) (m : M), b • m = (⟨(b : G), hBA b.2⟩ : A) • m)
    {N : Subgroup M}
    (hAinv : IsInvariant A M N) :
    IsInvariant B M N := by
  refine ⟨?_⟩
  intro b m
  have hA :=
    IsInvariant.invariant (A := A) (G := M) (H := N)
      (⟨(b : G), hBA b.2⟩ : A) m
  constructor
  · intro hm
    simpa [hcompat b m] using hA.1 hm
  · intro hm
    exact hA.2 (by simpa [hcompat b m] using hm)

private theorem fixedPointSubgroup_invariant_of_normal_sec9
    {A M : Type u} [Group A] [Group M] [MulDistribMulAction A M]
    (B : Subgroup A) [B.Normal] :
    IsInvariant A M (fixedPointSubgroup (↥B) M) := by
  refine ⟨?_⟩
  intro g x
  constructor
  · intro hx
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hx ⊢
    intro b
    have hxfix :
        ((⟨g⁻¹ * (b : A) * g, by
          simpa using (inferInstance : B.Normal).conj_mem (b : A) b.2 g⁻¹⟩ : B) : A) • x = x :=
      hx ⟨g⁻¹ * (b : A) * g, by
        simpa using (inferInstance : B.Normal).conj_mem (b : A) b.2 g⁻¹⟩
    calc
      (b : A) • (g • x) = g • (((g⁻¹ * (b : A) * g) : A) • x) := by
        simp [mul_smul, mul_assoc]
      _ = g • x := by rw [hxfix]
  · intro hx
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hx ⊢
    intro b
    have hxfix :
        ((⟨g * (b : A) * g⁻¹, by
          exact (inferInstance : B.Normal).conj_mem (b : A) b.2 g⟩ : B) : A) • (g • x) =
            g • x :=
      hx ⟨g * (b : A) * g⁻¹, by
        exact (inferInstance : B.Normal).conj_mem (b : A) b.2 g⟩
    calc
      (b : A) • x = g⁻¹ • (((g * (b : A) * g⁻¹) : A) • (g • x)) := by
        simp [mul_smul, mul_assoc]
      _ = g⁻¹ • (g • x) := by rw [hxfix]
      _ = x := by simp

private theorem fixedPointSubgroup_compatible_eq_sec9
    {G M : Type u} [Group G] [Group M]
    (A B : Subgroup G)
    [MulDistribMulAction A M] [MulDistribMulAction B M]
    (hBA : B ≤ A)
    (hcompat : ∀ (b : B) (m : M), b • m = (⟨(b : G), hBA b.2⟩ : A) • m) :
    fixedPointSubgroup (↥B) M =
      letI : MulDistribMulAction (↥B) M :=
        MulDistribMulAction.compHom M (Subgroup.inclusion hBA)
      fixedPointSubgroup (↥B) M := by
  ext m
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hm b
    have hb := hm b
    simpa [MulAction.compHom_smul_def, hcompat b m] using hb
  · intro hm b
    have hb := hm b
    simpa [MulAction.compHom_smul_def, hcompat b m] using hb

private theorem fixedPointSubgroup_eq_subgroupOf_of_compatible_sec9
    {G M : Type u} [Group G] [Group M]
    (A B : Subgroup G)
    [MulDistribMulAction A M] [MulDistribMulAction B M]
    (hBA : B ≤ A)
    (hcompat : ∀ (b : B) (m : M), b • m = (⟨(b : G), hBA b.2⟩ : A) • m) :
    fixedPointSubgroup (↥B) M =
      letI : MulDistribMulAction (↥(B.subgroupOf A)) M :=
        MulDistribMulAction.compHom M (B.subgroupOf A).subtype
      fixedPointSubgroup (↥(B.subgroupOf A)) M := by
  ext m
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hm b
    let bB : B := ⟨(b : G), b.2⟩
    have hb := hm bB
    have hb_eq : (⟨(b : A), by
        show ((b : A) : G) ∈ B
        exact b.2⟩ : B.subgroupOf A) = b := by
      ext
      rfl
    rw [← hb_eq]
    simpa [bB, MulAction.compHom_smul_def, hcompat bB m] using hb
  · intro hm b
    have hb :
        (⟨⟨(b : G), hBA b.2⟩, by
          show ((⟨(b : G), hBA b.2⟩ : A) : G) ∈ B
          exact b.2⟩ : B.subgroupOf A) • m = m :=
      hm ⟨⟨(b : G), hBA b.2⟩, by
        show ((⟨(b : G), hBA b.2⟩ : A) : G) ∈ B
        exact b.2⟩
    simpa [MulAction.compHom_smul_def, hcompat b m] using hb

private theorem theorem_9_1_fixedPoint_card_eq_mul_quotient_of_le_actor_sec9
    {G : Type u} [Group G] [Finite G]
    (A B H : Subgroup G) [Subgroup.Normalizes A H] [Subgroup.Normalizes B H]
    {N : Subgroup H} [N.Normal]
    (hBA : B ≤ A)
    (hAinv : IsInvariant A H N)
    (hsolvH : IsSolvable H)
    (hcopA : Nat.Coprime (Nat.card A) (Nat.card H)) :
    letI : IsInvariant B H N := isInvariant_of_le_actor_sec9 A B H hBA hAinv
    letI : MulDistribMulAction (↥B) (H ⧸ N) :=
      quotientMulDistribMulAction (A := B) (G := H) N
        (isInvariant_of_le_actor_sec9 A B H hBA hAinv)
    Nat.card (fixedPointSubgroup (↥B) H) =
      Nat.card (fixedPointSubgroup (↥B) N) *
        Nat.card (fixedPointSubgroup (↥B) (H ⧸ N)) := by
  let hBinv : IsInvariant B H N := isInvariant_of_le_actor_sec9 A B H hBA hAinv
  letI : IsInvariant B H N := hBinv
  letI : MulDistribMulAction (↥B) (H ⧸ N) :=
    quotientMulDistribMulAction (A := B) (G := H) N hBinv
  have hcopB : Nat.Coprime (Nat.card B) (Nat.card H) := by
    exact Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_le hBA) hcopA
  simpa [hBinv] using
    theorem_9_1_fixedPoint_card_eq_mul_quotient_sec9
      B H (N := N) hBinv hsolvH hcopB

private theorem theorem_9_1_wielandt_fixedPoint_product_identity_lift_from_invariant_normal_sec9
    {G : Type u} [Group G] [Finite G]
    (UE U E H : Subgroup G)
    (h91 : frobeniusActionData UE U E H)
    (hUE_norm_H : UE ≤ Subgroup.normalizer (H : Set G))
    (hU_norm_H : U ≤ Subgroup.normalizer (H : Set G))
    (hEnormH : ∀ u : U, E.conjBy (u : G) ≤ Subgroup.normalizer (H : Set G))
    (hU_le_UE : U ≤ UE)
    (hE_le_UE : ∀ u : U, E.conjBy (u : G) ≤ UE)
    {N : Subgroup H} [N.Normal]
    (hUEinv :
      letI : Subgroup.Normalizes UE H := ⟨hUE_norm_H⟩
      IsInvariant UE H N)
    (hN :
      letI : Subgroup.Normalizes UE H := ⟨hUE_norm_H⟩
      letI : Subgroup.Normalizes U H := ⟨hU_norm_H⟩
      letI : IsInvariant UE H N := hUEinv
      let hUinv : IsInvariant U H N := isInvariant_of_le_actor_sec9 UE U H hU_le_UE hUEinv
      letI : IsInvariant U H N := hUinv
      letI : Fintype U := Fintype.ofFinite U
      Nat.card (fixedPointSubgroup (↥UE) N) ^ Nat.card UE * Nat.card N ^ Nat.card U =
        (∏ u : U,
          letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
          let hEuinv : IsInvariant (E.conjBy (u : G)) H N :=
            isInvariant_of_le_actor_sec9 UE (E.conjBy (u : G)) H (hE_le_UE u) hUEinv
          letI : IsInvariant (E.conjBy (u : G)) H N := hEuinv
          Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) N) ^
            Nat.card (E.conjBy (u : G))) *
          Nat.card (fixedPointSubgroup (↥U) N) ^ Nat.card U)
    (hQ :
      letI : Subgroup.Normalizes UE H := ⟨hUE_norm_H⟩
      letI : Subgroup.Normalizes U H := ⟨hU_norm_H⟩
      letI : IsInvariant UE H N := hUEinv
      letI : MulDistribMulAction UE (H ⧸ N) :=
        quotientMulDistribMulAction (A := UE) (G := H) N hUEinv
      let hUinv : IsInvariant U H N := isInvariant_of_le_actor_sec9 UE U H hU_le_UE hUEinv
      letI : IsInvariant U H N := hUinv
      letI : MulDistribMulAction U (H ⧸ N) :=
        quotientMulDistribMulAction (A := U) (G := H) N hUinv
      letI : Fintype U := Fintype.ofFinite U
      Nat.card (fixedPointSubgroup (↥UE) (H ⧸ N)) ^ Nat.card UE *
          Nat.card (H ⧸ N) ^ Nat.card U =
        (∏ u : U,
          letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
          let hEuinv : IsInvariant (E.conjBy (u : G)) H N :=
            isInvariant_of_le_actor_sec9 UE (E.conjBy (u : G)) H (hE_le_UE u) hUEinv
          letI : IsInvariant (E.conjBy (u : G)) H N := hEuinv
          letI : MulDistribMulAction (E.conjBy (u : G)) (H ⧸ N) :=
            quotientMulDistribMulAction (A := E.conjBy (u : G)) (G := H) N hEuinv
          Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) (H ⧸ N)) ^
            Nat.card (E.conjBy (u : G))) *
          Nat.card (fixedPointSubgroup (↥U) (H ⧸ N)) ^ Nat.card U) :
    letI : Subgroup.Normalizes UE H := ⟨hUE_norm_H⟩
    letI : Subgroup.Normalizes U H := ⟨hU_norm_H⟩
    Nat.card (fixedPointSubgroup (↥UE) H) ^ Nat.card UE *
        Nat.card H ^ Nat.card U =
      theorem_9_1_fixedPoint_conjugate_complement_product_sec9 U E H hEnormH *
        Nat.card (fixedPointSubgroup (↥U) H) ^ Nat.card U := by
  classical
  rcases h91 with ⟨_hcomp, _hfrob, _hUE_norm_H', hsolvH, hcopHUE⟩
  letI : Subgroup.Normalizes UE H := ⟨hUE_norm_H⟩
  letI : Subgroup.Normalizes U H := ⟨hU_norm_H⟩
  letI : IsInvariant UE H N := hUEinv
  letI : MulDistribMulAction UE (H ⧸ N) :=
    quotientMulDistribMulAction (A := UE) (G := H) N hUEinv
  let hUinv : IsInvariant U H N := isInvariant_of_le_actor_sec9 UE U H hU_le_UE hUEinv
  letI : IsInvariant U H N := hUinv
  letI : MulDistribMulAction U (H ⧸ N) :=
    quotientMulDistribMulAction (A := U) (G := H) N hUinv
  have hUEfactor :
      Nat.card (fixedPointSubgroup (↥UE) H) =
        Nat.card (fixedPointSubgroup (↥UE) N) *
          Nat.card (fixedPointSubgroup (↥UE) (H ⧸ N)) :=
    theorem_9_1_fixedPoint_card_eq_mul_quotient_sec9
      UE H (N := N) hUEinv hsolvH hcopHUE.symm
  have hHfactor : Nat.card H = Nat.card N * Nat.card (H ⧸ N) := by
    simpa [Nat.mul_comm] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := H) (s := N))
  have hUfactor :
      Nat.card (fixedPointSubgroup (↥U) H) =
        Nat.card (fixedPointSubgroup (↥U) N) *
          Nat.card (fixedPointSubgroup (↥U) (H ⧸ N)) :=
    theorem_9_1_fixedPoint_card_eq_mul_quotient_of_le_actor_sec9
      UE U H (N := N) hU_le_UE hUEinv hsolvH hcopHUE.symm
  have hEfactor : ∀ u : U,
      letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
      let hEuinv : IsInvariant (E.conjBy (u : G)) H N :=
        isInvariant_of_le_actor_sec9 UE (E.conjBy (u : G)) H (hE_le_UE u) hUEinv
      letI : IsInvariant (E.conjBy (u : G)) H N := hEuinv
      letI : MulDistribMulAction (E.conjBy (u : G)) (H ⧸ N) :=
        quotientMulDistribMulAction (A := E.conjBy (u : G)) (G := H) N hEuinv
      Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) H) =
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) N) *
          Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) (H ⧸ N)) := by
    intro u
    letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
    let hEuinv : IsInvariant (E.conjBy (u : G)) H N :=
      isInvariant_of_le_actor_sec9 UE (E.conjBy (u : G)) H (hE_le_UE u) hUEinv
    letI : IsInvariant (E.conjBy (u : G)) H N := hEuinv
    letI : MulDistribMulAction (E.conjBy (u : G)) (H ⧸ N) :=
      quotientMulDistribMulAction (A := E.conjBy (u : G)) (G := H) N hEuinv
    exact
      theorem_9_1_fixedPoint_card_eq_mul_quotient_of_le_actor_sec9
        UE (E.conjBy (u : G)) H (N := N) (hE_le_UE u) hUEinv hsolvH hcopHUE.symm
  exact
    theorem_9_1_wielandt_fixedPoint_product_identity_lift_from_card_factors_sec9
      UE U E H hUE_norm_H hU_norm_H hEnormH
      (aN := Nat.card (fixedPointSubgroup (↥UE) N))
      (aQ := Nat.card (fixedPointSubgroup (↥UE) (H ⧸ N)))
      (bN := Nat.card N)
      (bQ := Nat.card (H ⧸ N))
      (dN := Nat.card (fixedPointSubgroup (↥U) N))
      (dQ := Nat.card (fixedPointSubgroup (↥U) (H ⧸ N)))
      (cN := fun u : U =>
        letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
        let hEuinv : IsInvariant (E.conjBy (u : G)) H N :=
          isInvariant_of_le_actor_sec9 UE (E.conjBy (u : G)) H (hE_le_UE u) hUEinv
        letI : IsInvariant (E.conjBy (u : G)) H N := hEuinv
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) N))
      (cQ := fun u : U =>
        letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
        let hEuinv : IsInvariant (E.conjBy (u : G)) H N :=
          isInvariant_of_le_actor_sec9 UE (E.conjBy (u : G)) H (hE_le_UE u) hUEinv
        letI : IsInvariant (E.conjBy (u : G)) H N := hEuinv
        letI : MulDistribMulAction (E.conjBy (u : G)) (H ⧸ N) :=
          quotientMulDistribMulAction (A := E.conjBy (u : G)) (G := H) N hEuinv
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) (H ⧸ N)))
      hUEfactor hHfactor hUfactor hEfactor hN hQ

private theorem theorem_9_1_wielandt_fixedPoint_product_identity_action_lift_from_invariant_normal_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hsolvM : IsSolvable M)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
          UE) • m)
    {N : Subgroup M} [N.Normal]
    (hUEinv : IsInvariant UE M N)
    (hN :
      let hUinv : IsInvariant U M N :=
        isInvariant_of_compatible_le_actor_sec9 UE U hcomp.1 hUcompat hUEinv
      letI : IsInvariant U M N := hUinv
      let hEuinv : ∀ u : U, IsInvariant (E.conjBy (u : G)) M N := fun u =>
        letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        isInvariant_of_compatible_le_actor_sec9 UE (E.conjBy (u : G))
          (section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u)
          (hEcompat u) hUEinv
      let hEactN : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) N := fun u => by
        letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        letI : IsInvariant (E.conjBy (u : G)) M N := hEuinv u
        infer_instance
      letI : Fintype U := Fintype.ofFinite U
      Nat.card (fixedPointSubgroup (↥UE) N) ^ Nat.card UE *
          Nat.card N ^ Nat.card U =
        theorem_9_1_fixedPoint_conjugate_action_product_sec9 U E hEactN *
          Nat.card (fixedPointSubgroup (↥U) N) ^ Nat.card U)
    (hQ :
      letI : IsInvariant UE M N := hUEinv
      letI : MulDistribMulAction UE (M ⧸ N) :=
        quotientMulDistribMulAction (A := UE) (G := M) N hUEinv
      let hUinv : IsInvariant U M N :=
        isInvariant_of_compatible_le_actor_sec9 UE U hcomp.1 hUcompat hUEinv
      letI : IsInvariant U M N := hUinv
      letI : MulDistribMulAction U (M ⧸ N) :=
        quotientMulDistribMulAction (A := U) (G := M) N hUinv
      let hEuinv : ∀ u : U, IsInvariant (E.conjBy (u : G)) M N := fun u =>
        letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        isInvariant_of_compatible_le_actor_sec9 UE (E.conjBy (u : G))
          (section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u)
          (hEcompat u) hUEinv
      let hEactQ : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) (M ⧸ N) := fun u => by
        letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        letI : IsInvariant (E.conjBy (u : G)) M N := hEuinv u
        exact quotientMulDistribMulAction (A := E.conjBy (u : G)) (G := M) N (hEuinv u)
      letI : Fintype U := Fintype.ofFinite U
      Nat.card (fixedPointSubgroup (↥UE) (M ⧸ N)) ^ Nat.card UE *
          Nat.card (M ⧸ N) ^ Nat.card U =
        theorem_9_1_fixedPoint_conjugate_action_product_sec9 U E hEactQ *
          Nat.card (fixedPointSubgroup (↥U) (M ⧸ N)) ^ Nat.card U) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      theorem_9_1_fixedPoint_conjugate_action_product_sec9 U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  letI : IsInvariant UE M N := hUEinv
  letI : MulDistribMulAction UE (M ⧸ N) :=
    quotientMulDistribMulAction (A := UE) (G := M) N hUEinv
  let hUinv : IsInvariant U M N :=
    isInvariant_of_compatible_le_actor_sec9 UE U hcomp.1 hUcompat hUEinv
  letI : IsInvariant U M N := hUinv
  letI : MulDistribMulAction U (M ⧸ N) :=
    quotientMulDistribMulAction (A := U) (G := M) N hUinv
  let hEuinv : ∀ u : U, IsInvariant (E.conjBy (u : G)) M N := fun u =>
    letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    isInvariant_of_compatible_le_actor_sec9 UE (E.conjBy (u : G))
      (section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u)
      (hEcompat u) hUEinv
  let hEactN : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) N := fun u => by
    letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    letI : IsInvariant (E.conjBy (u : G)) M N := hEuinv u
    infer_instance
  let hEactQ : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) (M ⧸ N) := fun u => by
    letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    letI : IsInvariant (E.conjBy (u : G)) M N := hEuinv u
    exact quotientMulDistribMulAction (A := E.conjBy (u : G)) (G := M) N (hEuinv u)
  have hUEfactor :
      Nat.card (fixedPointSubgroup (↥UE) M) =
        Nat.card (fixedPointSubgroup (↥UE) N) *
          Nat.card (fixedPointSubgroup (↥UE) (M ⧸ N)) :=
    theorem_9_1_fixedPoint_card_eq_mul_quotient_action_sec9
      (A := UE) (M := M) (N := N) hUEinv hsolvM hcop.symm
  have hMfactor : Nat.card M = Nat.card N * Nat.card (M ⧸ N) := by
    simpa [Nat.mul_comm] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := M) (s := N))
  have hcopU : Nat.Coprime (Nat.card U) (Nat.card M) := by
    exact Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_le hcomp.1) hcop.symm
  have hUfactor :
      Nat.card (fixedPointSubgroup (↥U) M) =
        Nat.card (fixedPointSubgroup (↥U) N) *
          Nat.card (fixedPointSubgroup (↥U) (M ⧸ N)) :=
    theorem_9_1_fixedPoint_card_eq_mul_quotient_action_sec9
      (A := U) (M := M) (N := N) hUinv hsolvM hcopU
  have hEfactor : ∀ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) =
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) N) *
          Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) (M ⧸ N)) := by
    intro u
    letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    letI : IsInvariant (E.conjBy (u : G)) M N := hEuinv u
    letI : MulDistribMulAction (E.conjBy (u : G)) (M ⧸ N) := hEactQ u
    have hcopEu : Nat.Coprime (Nat.card (E.conjBy (u : G))) (Nat.card M) := by
      exact Nat.Coprime.of_dvd_left
        (Subgroup.card_dvd_of_le
          (section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u))
        hcop.symm
    exact
      theorem_9_1_fixedPoint_card_eq_mul_quotient_action_sec9
        (A := E.conjBy (u : G)) (M := M) (N := N) (hEuinv u) hsolvM hcopEu
  have hNprod :
      Nat.card (fixedPointSubgroup (↥UE) N) ^ Nat.card UE * Nat.card N ^ Nat.card U =
        (∏ u : U,
          Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) N) ^
            Nat.card (E.conjBy (u : G))) *
          Nat.card (fixedPointSubgroup (↥U) N) ^ Nat.card U := by
    simpa [theorem_9_1_fixedPoint_conjugate_action_product_sec9, hEactN] using hN
  have hQprod :
      Nat.card (fixedPointSubgroup (↥UE) (M ⧸ N)) ^ Nat.card UE *
          Nat.card (M ⧸ N) ^ Nat.card U =
        (∏ u : U,
          Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) (M ⧸ N)) ^
            Nat.card (E.conjBy (u : G))) *
          Nat.card (fixedPointSubgroup (↥U) (M ⧸ N)) ^ Nat.card U := by
    simpa [theorem_9_1_fixedPoint_conjugate_action_product_sec9, hEactQ] using hQ
  exact
    theorem_9_1_wielandt_fixedPoint_action_product_identity_lift_from_card_factors_sec9
      UE U E hEact
      (aN := Nat.card (fixedPointSubgroup (↥UE) N))
      (aQ := Nat.card (fixedPointSubgroup (↥UE) (M ⧸ N)))
      (bN := Nat.card N)
      (bQ := Nat.card (M ⧸ N))
      (dN := Nat.card (fixedPointSubgroup (↥U) N))
      (dQ := Nat.card (fixedPointSubgroup (↥U) (M ⧸ N)))
      (cN := fun u : U =>
        letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        letI : IsInvariant (E.conjBy (u : G)) M N := hEuinv u
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) N))
      (cQ := fun u : U =>
        letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        letI : IsInvariant (E.conjBy (u : G)) M N := hEuinv u
        letI : MulDistribMulAction (E.conjBy (u : G)) (M ⧸ N) := hEactQ u
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) (M ⧸ N)))
      hUEfactor hMfactor hUfactor hEfactor hNprod hQprod

private theorem theorem_9_1_chiefFactor_elementaryAbelian_of_nontrivial_sec9
    {A M : Type u} [Group A] [Group M] [Finite M] [MulDistribMulAction A M]
    [Nontrivial M]
    (hsolvM : IsSolvable M)
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant A M N → N ≠ ⊥ → N = ⊤) :
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p M := by
  classical
  have hcommM : IsMulCommutative M := by
    have hcomm_lt : commutator M < (⊤ : Subgroup M) := by
      letI : IsSolvable M := hsolvM
      exact IsSolvable.commutator_lt_top_of_nontrivial (G := M)
    have htop_inv : IsInvariant A M (⊤ : Subgroup M) := by
      refine ⟨?_⟩
      intro a g
      simp
    letI : IsInvariant A M (⊤ : Subgroup M) := htop_inv
    have hcomm_inv : IsInvariant A M (commutator M) := by
      simpa [_root_.commutator_def] using
        (isInvariant_commutator (A := A) (G := M)
          (H := (⊤ : Subgroup M)) (K := (⊤ : Subgroup M)))
    have hcomm_eq_bot : commutator M = ⊥ := by
      by_contra hne
      have htop : commutator M = (⊤ : Subgroup M) :=
        hminv (commutator M) inferInstance hcomm_inv hne
      exact (ne_of_lt hcomm_lt) htop
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun a b ↦ ?_
    have htop_le_cent :
        (⊤ : Subgroup M) ≤ Subgroup.centralizer ((⊤ : Subgroup M) : Set M) := by
      have htop_comm_bot : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = ⊥ := by
        simpa [_root_.commutator_def] using hcomm_eq_bot
      exact
        (Subgroup.commutator_eq_bot_iff_le_centralizer
          (H₁ := (⊤ : Subgroup M)) (H₂ := (⊤ : Subgroup M))).1 htop_comm_bot
    have ha_cent : a ∈ Subgroup.centralizer ((⊤ : Subgroup M) : Set M) :=
      htop_le_cent trivial
    exact ((Subgroup.mem_centralizer_iff.mp ha_cent) b trivial).symm
  letI : IsMulCommutative M := hcommM
  have hnilM : Group.IsNilpotent M := by
    refine ⟨1, ?_⟩
    have hcenter : Subgroup.center M = ⊤ := by
      ext x
      constructor
      · intro _hx
        simp
      · intro _hx
        rw [Subgroup.mem_center_iff]
        intro y
        simpa using (IsMulCommutative.is_comm (M := M)).comm y x
    simpa [upperCentralSeries_one] using hcenter
  have hM_card_gt_one : 1 < Nat.card M :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨p, hp_prime, hp_dvd_cardM⟩ :=
    Nat.exists_prime_and_dvd (n := Nat.card M) (Nat.ne_of_gt hM_card_gt_one)
  letI : Fact p.Prime := ⟨hp_prime⟩
  let P : Sylow p M := default
  have hP_ne_bot : (P : Subgroup M) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := M) (p := p) P hp_dvd_cardM
  have hP_normal : (P : Subgroup M).Normal :=
    Group.IsNilpotent.sylow_normal hnilM p P
  letI : (P : Subgroup M).Characteristic := Sylow.characteristic_of_normal P hP_normal
  have hP_inv : IsInvariant A M (P : Subgroup M) :=
    isInvariant_of_characteristic (A := A) (G := M) (P : Subgroup M)
  have hP_top : (P : Subgroup M) = ⊤ :=
    hminv (P : Subgroup M) hP_normal hP_inv hP_ne_bot
  have htop_p : IsPGroup p (⊤ : Subgroup M) :=
    P.isPGroup'.of_equiv (MulEquiv.subgroupCongr hP_top)
  have hMpgroup : IsPGroup p M := htop_p.of_equiv Subgroup.topEquiv
  letI : Fact (IsPGroup p M) := ⟨hMpgroup⟩
  let Ω : Subgroup M := omega₁ (G := M) (p := p)
  letI : Ω.Characteristic := by
    simpa [Ω] using omega₁_characteristic (G := M) (p := p)
  have hΩ_inv : IsInvariant A M Ω :=
    isInvariant_of_characteristic (A := A) (G := M) Ω
  have hΩ_ne_bot : Ω ≠ ⊥ := by
    letI : Fintype M := Fintype.ofFinite M
    obtain ⟨x, hx_order⟩ := _root_.exists_prime_orderOf_dvd_card (G := M) p <| by
      simpa [Nat.card_eq_fintype_card] using hp_dvd_cardM
    have hx_ne_one : x ≠ (1 : M) := by
      intro hx
      have : 1 = p := by simpa [hx] using hx_order
      exact hp_prime.ne_one this.symm
    have hx_pow : x ^ p = 1 := by
      simpa [hx_order] using pow_orderOf_eq_one x
    have hx_mem : x ∈ Ω := by
      change x ∈ Subgroup.closure {y : M | y ^ (p ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [Ω, omega₁, omega, pow_one] using hx_pow
    intro hΩ_bot
    have hx_bot : x ∈ (⊥ : Subgroup M) := by
      simpa [hΩ_bot] using hx_mem
    exact hx_ne_one (by simpa using hx_bot)
  have hΩ_top : Ω = ⊤ := hminv Ω inferInstance hΩ_inv hΩ_ne_bot
  have hpow : ∀ x : M, x ^ p = 1 := by
    intro x
    have hxΩ : x ∈ Ω := by simp [hΩ_top]
    have hx' : x ∈ Subgroup.closure {y : M | y ^ (p ^ 1) = 1} := by
      simpa [Ω, omega₁, omega] using hxΩ
    refine
      Subgroup.closure_induction (k := {y : M | y ^ (p ^ 1) = 1})
        (p := fun z _hz => z ^ p = 1) (x := x) ?_ ?_ ?_ ?_ hx'
    · intro y hy
      simpa [pow_one] using hy
    · simp
    · intro a b _ha _hb ha hb
      calc
        (a * b) ^ p = a ^ p * b ^ p := by simpa using mul_pow a b p
        _ = 1 := by simp [ha, hb]
    · intro a _ha ha
      simp [ha]
  refine ⟨p, hp_prime, ?_⟩
  exact
    { toIsMulCommutative := hcommM
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hpow }

private theorem theorem_9_1_chiefFactor_elementaryAbelian_or_subsingleton_sec9
    {A M : Type u} [Group A] [Group M] [Finite M] [MulDistribMulAction A M]
    (hsolvM : IsSolvable M)
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant A M N → N ≠ ⊥ → N = ⊤) :
    Subsingleton M ∨ Nontrivial M ∧ ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p M := by
  by_cases hsub : Subsingleton M
  · exact Or.inl hsub
  · letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hsub
    exact Or.inr ⟨inferInstance,
      theorem_9_1_chiefFactor_elementaryAbelian_of_nontrivial_sec9
        (A := A) (M := M) hsolvM hminv⟩

private noncomputable def theorem_9_1_fixedPointSubgroup_fixedSubspaceEquiv_sec9
    {A M : Type u} [Group A] [Group M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [MulDistribMulAction A M]
    (H : Subgroup A) :
    ↥((Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)).fixedSubspace H) ≃
      Additive ↥(fixedPointSubgroup (↥H) M) := by
  refine
    { toFun := fun x =>
        Additive.ofMul ⟨Additive.toMul x.1, by
          rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
          intro h
          exact Additive.ofMul.injective (by
            simpa using x.2 h)⟩
      invFun := fun y =>
        ⟨Additive.ofMul ((Additive.toMul y : ↥(fixedPointSubgroup (↥H) M)) : M), by
          intro h
          have hy := (Additive.toMul y).2 h
          simpa using congrArg Additive.ofMul hy⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro y
        ext
        rfl }

private theorem theorem_9_1_fixedPointSubgroup_card_eq_prime_pow_finrank_sec9
    {A M : Type u} [Group A] [Group M] [Finite M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [MulDistribMulAction A M] :
    Nat.card (fixedPointSubgroup A M) =
      p ^ Module.finrank (ZMod p)
        ↥((Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)).fixedSubspace
          (⊤ : Subgroup A)) := by
  classical
  let ρ := Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)
  have h_equiv : ↥(ρ.fixedSubspace (⊤ : Subgroup A)) ≃
      Additive ↥(fixedPointSubgroup (↥(⊤ : Subgroup A)) M) :=
    theorem_9_1_fixedPointSubgroup_fixedSubspaceEquiv_sec9
      (A := A) (M := M) (p := p) (⊤ : Subgroup A)
  have h_top : fixedPointSubgroup (↥(⊤ : Subgroup A)) M = fixedPointSubgroup A M := by
    ext x
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    constructor
    · intro hx a
      exact hx ⟨a, by simp⟩
    · intro hx a
      simpa using hx (a : A)
  have h_add_card : Nat.card (Additive ↥(fixedPointSubgroup (↥(⊤ : Subgroup A)) M)) =
      Nat.card (fixedPointSubgroup A M) := by
    calc
      Nat.card (Additive ↥(fixedPointSubgroup (↥(⊤ : Subgroup A)) M)) =
          Nat.card ↥(fixedPointSubgroup (↥(⊤ : Subgroup A)) M) := by
            exact Nat.card_congr
              { toFun := Additive.toMul
                invFun := Additive.ofMul
                left_inv := by intro x; rfl
                right_inv := by intro x; rfl }
      _ = Nat.card (fixedPointSubgroup A M) := by rw [h_top]
  have h_sub_card : Nat.card ↥(ρ.fixedSubspace (⊤ : Subgroup A)) =
      Nat.card (fixedPointSubgroup A M) := by
    calc
      Nat.card ↥(ρ.fixedSubspace (⊤ : Subgroup A)) =
          Nat.card (Additive ↥(fixedPointSubgroup (↥(⊤ : Subgroup A)) M)) :=
            Nat.card_congr h_equiv
      _ = Nat.card (fixedPointSubgroup A M) := h_add_card
  have hnat := Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := ↥(ρ.fixedSubspace (⊤ : Subgroup A)))
  simpa [ρ, Nat.card_eq_fintype_card, ZMod.card, h_sub_card] using hnat

private theorem fixedSubspace_finrank_eq_of_fixedPointSubgroup_card_eq_sec9
    {A M : Type u} [Group A] [Group M] [Finite M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [MulDistribMulAction A M]
    (n : ℕ)
    (hcard : Nat.card (fixedPointSubgroup A M) = p ^ n) :
    Module.finrank (ZMod p)
        ↥((Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)).fixedSubspace
          (⊤ : Subgroup A)) = n := by
  apply Nat.pow_right_injective (Fact.out : Nat.Prime p).one_lt
  have hfixed :=
    theorem_9_1_fixedPointSubgroup_card_eq_prime_pow_finrank_sec9
      (A := A) (M := M) (p := p)
  exact hfixed.symm.trans hcard

private theorem fixedSubspace_finrank_eq_zero_of_fixedPointSubgroup_eq_bot_sec9
    {A M : Type u} [Group A] [Group M] [Finite M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [MulDistribMulAction A M]
    (hfix : fixedPointSubgroup A M = ⊥) :
    Module.finrank (ZMod p)
        ↥((Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)).fixedSubspace
          (⊤ : Subgroup A)) = 0 := by
  apply fixedSubspace_finrank_eq_of_fixedPointSubgroup_card_eq_sec9
  simp [hfix]

private theorem fixedSubspace_finrank_eq_full_of_fixedPointSubgroup_eq_top_sec9
    {A M : Type u} [Group A] [Group M] [Finite M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [MulDistribMulAction A M]
    (hfix : fixedPointSubgroup A M = ⊤) :
    Module.finrank (ZMod p)
        ↥((Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)).fixedSubspace
          (⊤ : Subgroup A)) =
      Module.finrank (ZMod p) (Additive M) := by
  apply fixedSubspace_finrank_eq_of_fixedPointSubgroup_card_eq_sec9
  have hnat := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive M)
  have hMcard :
      Nat.card M = p ^ Module.finrank (ZMod p) (Additive M) := by
    simpa [Nat.card_eq_fintype_card, ZMod.card] using hnat
  rw [hfix]
  simpa [hMcard]

private theorem fixedSubspace_finrank_eq_of_fixedPointSubgroup_nat_card_eq_sec9
    {A B M : Type u} [Group A] [Group B] [Group M] [Finite M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    [MulDistribMulAction A M] [MulDistribMulAction B M]
    (hcard : Nat.card (fixedPointSubgroup A M) =
      Nat.card (fixedPointSubgroup B M)) :
    Module.finrank (ZMod p)
        ↥((Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)).fixedSubspace
          (⊤ : Subgroup A)) =
      Module.finrank (ZMod p)
        ↥((Representation.ofElementaryAbelianAction (A := B) (G := M) (p := p)).fixedSubspace
          (⊤ : Subgroup B)) := by
  apply Nat.pow_right_injective (Fact.out : Nat.Prime p).one_lt
  calc
    p ^ Module.finrank (ZMod p)
        ↥((Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)).fixedSubspace
          (⊤ : Subgroup A)) =
        Nat.card (fixedPointSubgroup A M) := by
          exact (theorem_9_1_fixedPointSubgroup_card_eq_prime_pow_finrank_sec9
            (A := A) (M := M) (p := p)).symm
    _ = Nat.card (fixedPointSubgroup B M) := hcard
    _ = p ^ Module.finrank (ZMod p)
        ↥((Representation.ofElementaryAbelianAction (A := B) (G := M) (p := p)).fixedSubspace
          (⊤ : Subgroup B)) := by
          exact theorem_9_1_fixedPointSubgroup_card_eq_prime_pow_finrank_sec9
            (A := B) (M := M) (p := p)

private theorem full_finrank_eq_fixedSubspace_finrank_mul_of_fixedPoint_card_pow_sec9
    {A M : Type u} [Group A] [Group M] [Finite M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [MulDistribMulAction A M]
    (n : ℕ)
    (hcard : Nat.card M = Nat.card (fixedPointSubgroup A M) ^ n) :
    Module.finrank (ZMod p) (Additive M) =
      Module.finrank (ZMod p)
          ↥((Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)).fixedSubspace
            (⊤ : Subgroup A)) * n := by
  apply Nat.pow_right_injective (Fact.out : Nat.Prime p).one_lt
  calc
    p ^ Module.finrank (ZMod p) (Additive M) = Nat.card M := by
      have hnat := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive M)
      simpa [Nat.card_eq_fintype_card, ZMod.card] using hnat.symm
    _ = Nat.card (fixedPointSubgroup A M) ^ n := hcard
    _ = (p ^ Module.finrank (ZMod p)
          ↥((Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)).fixedSubspace
            (⊤ : Subgroup A))) ^ n := by
          rw [theorem_9_1_fixedPointSubgroup_card_eq_prime_pow_finrank_sec9
            (A := A) (M := M) (p := p)]
    _ = p ^ (Module.finrank (ZMod p)
          ↥((Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)).fixedSubspace
            (⊤ : Subgroup A)) * n) := by
          rw [pow_mul]

private theorem isNilpotent_of_isMulCommutative_sec9
    {M : Type u} [Group M] (hcommM : IsMulCommutative M) :
    Group.IsNilpotent M := by
  letI : IsMulCommutative M := hcommM
  refine ⟨1, ?_⟩
  have hcenter : Subgroup.center M = ⊤ := by
    ext x
    constructor
    · intro _hx
      simp
    · intro _hx
      rw [Subgroup.mem_center_iff]
      intro y
      simpa using (IsMulCommutative.is_comm (M := M)).comm y x
  simpa [upperCentralSeries_one] using hcenter

private theorem section12ComplementIn_nat_card_eq_mul_sec9
    {G : Type u} [Group G] [Finite G]
    (UE U E : Subgroup G)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E) :
    Nat.card UE = Nat.card U * Nat.card E := by
  classical
  have hUnorm : (U.subgroupOf UE).Normal := by
    have hUnormSup : (U.subgroupOf (U ⊔ E)).Normal :=
      IsFrobeniusGroupWithKernelComplement.normal hfrob
    have hUEeq : UE = U ⊔ E := hcomp.2.2.1
    subst UE
    simpa using hUnormSup
  have hdisjSub : Disjoint (U.subgroupOf UE) (E.subgroupOf UE) := by
    have hdisj := hcomp.2.2.2
    rw [disjoint_iff] at hdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ U ⊓ E := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf] using hx.1,
          by simpa [Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hsupTop : U.subgroupOf UE ⊔ E.subgroupOf UE = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := U) (A' := E) (B := UE) hcomp.1 hcomp.2.1]
    rw [← hcomp.2.2.1]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  have hcompSub : (U.subgroupOf UE).IsComplement' (E.subgroupOf UE) := by
    letI : (U.subgroupOf UE).Normal := hUnorm
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (U.subgroupOf UE) (E.subgroupOf UE) hdisjSub hsupTop
  have hmul := hcompSub.card_mul
  simpa [natCard_subgroupOf_eq U UE hcomp.1,
    natCard_subgroupOf_eq E UE hcomp.2.1] using hmul.symm

private theorem section12FrobeniusJoinWithKernel_subgroupOf_complementIn_sec9
    {G : Type u} [Group G] [Finite G]
    (UE U E : Subgroup G)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E) :
    IsFrobeniusGroupWithKernelComplement (U.subgroupOf UE) (E.subgroupOf UE) := by
  have hUEeq : UE = U ⊔ E := hcomp.2.2.1
  subst UE
  simpa [section12FrobeniusJoinWithKernel] using hfrob

private theorem section12ComplementIn_sup_conj_complement_eq_sec9
    {G : Type u} [Group G]
    (UE U E : Subgroup G)
    (hcomp : section12ComplementIn UE U E)
    (u : U) :
    U ⊔ E.conjBy (u : G) = UE := by
  apply le_antisymm
  · exact sup_le hcomp.1 (section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u)
  · rw [hcomp.2.2.1]
    apply sup_le
    · exact le_sup_left
    · intro e he
      have hconj : (u : G) * e * (u : G)⁻¹ ∈ E.conjBy (u : G) := by
        rw [Subgroup.conjBy, Subgroup.mem_map]
        exact ⟨e, he, rfl⟩
      have hmem : (u : G)⁻¹ * ((u : G) * e * (u : G)⁻¹) * (u : G) ∈
          U ⊔ E.conjBy (u : G) := by
        exact (U ⊔ E.conjBy (u : G)).mul_mem
          ((U ⊔ E.conjBy (u : G)).mul_mem
            (Subgroup.mem_sup_left (U.inv_mem u.2))
            (Subgroup.mem_sup_right hconj))
          (Subgroup.mem_sup_left u.2)
      have hmul : (u : G)⁻¹ * ((u : G) * e * (u : G)⁻¹) * (u : G) = e := by
        group
      simpa [hmul] using hmem

private noncomputable def fixedPointSubgroup_conj_complement_equiv_sec9
    {G M : Type u} [Group G] [Group M]
    {UE U E : Subgroup G}
    [MulDistribMulAction UE M]
    (hcomp : section12ComplementIn UE U E)
    (u : U)
    [MulDistribMulAction (E.conjBy (u : G)) M]
    (hEcompat : ∀ (e : E.conjBy (u : G)) (m : M),
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
          UE) • m) :
    fixedPointSubgroup (↥(E.subgroupOf UE)) M ≃
      fixedPointSubgroup (↥(E.conjBy (u : G))) M := by
  let uUE : UE := ⟨(u : G), hcomp.1 u.2⟩
  refine
    { toFun := fun x =>
        ⟨uUE • x.1, ?_⟩
      invFun := fun y =>
        ⟨uUE⁻¹ • y.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    intro e
    have he := e.2
    change (e : G) ∈ E.map (MulAut.conj (u : G)).toMonoidHom at he
    rw [Subgroup.mem_map] at he
    rcases he with ⟨e0, he0E, heq⟩
    let eUE : UE := ⟨e0, hcomp.2.1 he0E⟩
    have hx := (FixedPoints.mem_subgroup (M := E.subgroupOf UE) (a := x.1)).1 x.2
      ⟨eUE, by
        show (eUE : UE) ∈ E.subgroupOf UE
        exact he0E⟩
    have hxUE : (eUE : UE) • x.1 = x.1 := by
      simpa using hx
    have heUE_eq :
        (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
          UE) = uUE * eUE * uUE⁻¹ := by
      ext
      simpa [uUE, eUE] using heq.symm
    calc
      e • (uUE • x.1) =
          (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
            UE) • (uUE • x.1) := by
            rw [hEcompat e (uUE • x.1)]
      _ = (uUE * eUE * uUE⁻¹) • (uUE • x.1) := by rw [heUE_eq]
      _ = uUE • (eUE • x.1) := by simp [mul_smul, mul_assoc]
      _ = uUE • x.1 := by rw [hxUE]
  · rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    intro e
    let eG : G := (e : UE)
    have heE : eG ∈ E := e.2
    let eConj : E.conjBy (u : G) :=
      ⟨(u : G) * eG * (u : G)⁻¹, by
        change (u : G) * eG * (u : G)⁻¹ ∈
          E.map (MulAut.conj (u : G)).toMonoidHom
        rw [Subgroup.mem_map]
        exact ⟨eG, heE, rfl⟩⟩
    have hy := (FixedPoints.mem_subgroup (M := E.conjBy (u : G)) (a := y.1)).1 y.2 eConj
    have heConj_eq :
        (⟨(eConj : G),
            section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u eConj.2⟩ : UE) =
          uUE * e * uUE⁻¹ := by
      ext
      rfl
    have hyUE : (uUE * e * uUE⁻¹) • y.1 = y.1 := by
      calc
        (uUE * e * uUE⁻¹) • y.1 =
            (⟨(eConj : G),
              section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u eConj.2⟩ : UE) • y.1 := by
              rw [heConj_eq]
        _ = eConj • y.1 := by rw [hEcompat eConj y.1]
        _ = y.1 := hy
    calc
      e • (uUE⁻¹ • y.1) = uUE⁻¹ • ((uUE * (e : UE) * uUE⁻¹) • y.1) := by
        change (e : UE) • (uUE⁻¹ • y.1) =
          uUE⁻¹ • ((uUE * (e : UE) * uUE⁻¹) • y.1)
        simp [mul_smul, mul_assoc]
      _ = uUE⁻¹ • y.1 := by rw [hyUE]
  · intro x
    ext
    simp [uUE]
  · intro y
    ext
    simp [uUE]

private theorem fixedPointSubgroup_conj_complement_eq_of_kernel_fixed_top_sec9
    {G M : Type u} [Group G] [Group M]
    {UE U E : Subgroup G}
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hcomp : section12ComplementIn UE U E)
    (u : U)
    [MulDistribMulAction (E.conjBy (u : G)) M]
    (hUcompat : ∀ (u0 : U) (m : M),
      u0 • m = (⟨(u0 : G), hcomp.1 u0.2⟩ : UE) • m)
    (hEcompat : ∀ (e : E.conjBy (u : G)) (m : M),
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
          UE) • m)
    (hUtop : fixedPointSubgroup (↥U) M = ⊤) :
    fixedPointSubgroup (↥(E.conjBy (u : G))) M = fixedPointSubgroup (↥UE) M := by
  ext m
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hm a
    let aG : G := (a : UE)
    have haUE : aG ∈ UE := a.2
    have hjoin : UE = U ⊔ E.conjBy (u : G) :=
      (section12ComplementIn_sup_conj_complement_eq_sec9 UE U E hcomp u).symm
    have ha_closure :
        aG ∈ Subgroup.closure ((U : Set G) ∪ (E.conjBy (u : G) : Set G)) := by
      simpa [aG, Subgroup.sup_eq_closure, hjoin] using haUE
    refine Subgroup.closure_induction
      (p := fun g _ => ∀ hgUE : g ∈ UE, (⟨g, hgUE⟩ : UE) • m = m)
      ?mem ?one ?mul ?inv ha_closure haUE
    · intro g hg hgUE
      rcases hg with hgU | hgE
      · have hgm : (⟨g, hgU⟩ : U) • m = m := by
          have hmU : m ∈ fixedPointSubgroup (↥U) M := by simp [hUtop]
          exact (FixedPoints.mem_subgroup (M := U) (a := m)).1 hmU ⟨g, hgU⟩
        simpa [hUcompat ⟨g, hgU⟩ m] using hgm
      · have hgm : (⟨g, hgE⟩ : E.conjBy (u : G)) • m = m :=
          hm ⟨g, hgE⟩
        simpa [hEcompat ⟨g, hgE⟩ m] using hgm
    · intro hgUE
      have hone : (⟨1, hgUE⟩ : UE) = 1 := by
        ext
        rfl
      simp [hone]
    · intro x y hx hy hx_fix hy_fix hxyUE
      have hxUE : x ∈ UE := by
        simpa [Subgroup.sup_eq_closure, hjoin] using hx
      have hyUE : y ∈ UE := by
        simpa [Subgroup.sup_eq_closure, hjoin] using hy
      have hx_eq := hx_fix hxUE
      have hy_eq := hy_fix hyUE
      have hmul_eq : (⟨x, hxUE⟩ : UE) * ⟨y, hyUE⟩ = ⟨x * y, hxyUE⟩ := by
        ext
        rfl
      calc
        (⟨x * y, hxyUE⟩ : UE) • m =
            ((⟨x, hxUE⟩ : UE) * ⟨y, hyUE⟩) • m := by rw [hmul_eq]
        _ = (⟨x, hxUE⟩ : UE) • ((⟨y, hyUE⟩ : UE) • m) := by rw [mul_smul]
        _ = (⟨x, hxUE⟩ : UE) • m := by rw [hy_eq]
        _ = m := hx_eq
    · intro x hx hx_fix hxinvUE
      have hxUE : x ∈ UE := by
        simpa [Subgroup.sup_eq_closure, hjoin] using hx
      have hx_eq := hx_fix hxUE
      have hxinv_eq : (⟨x⁻¹, hxinvUE⟩ : UE) = (⟨x, hxUE⟩ : UE)⁻¹ := by
        ext
        rfl
      rw [hxinv_eq]
      exact inv_smul_eq_iff.mpr hx_eq.symm
  · intro hm e
    have hUE := hm
      (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ : UE)
    simpa [hEcompat e m] using hUE

private theorem theorem_9_1_prime_power_product_identity_of_exponent_sum_sec9
    {ι : Type*} [Fintype ι]
    (p a b d m n : ℕ) (c e : ι → ℕ)
    (h : a * m + b * n = (∑ i : ι, c i * e i) + d * n) :
    (p ^ a) ^ m * (p ^ b) ^ n =
      (∏ i : ι, (p ^ c i) ^ e i) * (p ^ d) ^ n := by
  classical
  have hprod : (∏ i : ι, (p ^ c i) ^ e i) = p ^ (∑ i : ι, c i * e i) := by
    calc
      (∏ i : ι, (p ^ c i) ^ e i) = ∏ i : ι, p ^ (c i * e i) := by
        apply Finset.prod_congr rfl
        intro i _hi
        rw [pow_mul]
      _ = p ^ (∑ i : ι, c i * e i) := by
        simpa using
          (Finset.prod_pow_eq_pow_sum (Finset.univ) (fun i : ι => c i * e i) p)
  calc
    (p ^ a) ^ m * (p ^ b) ^ n = p ^ (a * m) * p ^ (b * n) := by
      rw [pow_mul, pow_mul]
    _ = p ^ (a * m + b * n) := by rw [← Nat.pow_add]
    _ = p ^ ((∑ i : ι, c i * e i) + d * n) := by rw [h]
    _ = p ^ (∑ i : ι, c i * e i) * p ^ (d * n) := by rw [Nat.pow_add]
    _ = (∏ i : ι, (p ^ c i) ^ e i) * (p ^ d) ^ n := by rw [hprod, pow_mul]

private theorem theorem_9_1_wielandt_fixedPoint_product_identity_action_elementaryAbelian_of_finrank_identity_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hrank :
      letI : Fintype U := Fintype.ofFinite U
      Module.finrank (ZMod p)
          ↥((Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p)).fixedSubspace
            (⊤ : Subgroup UE)) * Nat.card UE +
        Module.finrank (ZMod p) (Additive M) * Nat.card U =
      (∑ u : U,
        letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        Module.finrank (ZMod p)
            ↥((Representation.ofElementaryAbelianAction
                (A := E.conjBy (u : G)) (G := M) (p := p)).fixedSubspace
              (⊤ : Subgroup (E.conjBy (u : G)))) *
          Nat.card (E.conjBy (u : G))) +
        Module.finrank (ZMod p)
          ↥((Representation.ofElementaryAbelianAction (A := U) (G := M) (p := p)).fixedSubspace
            (⊤ : Subgroup U)) * Nat.card U) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      theorem_9_1_fixedPoint_conjugate_action_product_sec9 U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  let rUE : ℕ := Module.finrank (ZMod p)
    ↥((Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p)).fixedSubspace
      (⊤ : Subgroup UE))
  let rM : ℕ := Module.finrank (ZMod p) (Additive M)
  let rU : ℕ := Module.finrank (ZMod p)
    ↥((Representation.ofElementaryAbelianAction (A := U) (G := M) (p := p)).fixedSubspace
      (⊤ : Subgroup U))
  let rE : U → ℕ := fun u =>
    letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    Module.finrank (ZMod p)
      ↥((Representation.ofElementaryAbelianAction
          (A := E.conjBy (u : G)) (G := M) (p := p)).fixedSubspace
        (⊤ : Subgroup (E.conjBy (u : G))))
  have hUEcard : Nat.card (fixedPointSubgroup (↥UE) M) = p ^ rUE := by
    simpa [rUE] using
      (theorem_9_1_fixedPointSubgroup_card_eq_prime_pow_finrank_sec9
        (A := UE) (M := M) (p := p))
  have hMcard : Nat.card M = p ^ rM := by
    have hnat := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive M)
    simpa [rM, Nat.card_eq_fintype_card, ZMod.card] using hnat
  have hUcard : Nat.card (fixedPointSubgroup (↥U) M) = p ^ rU := by
    simpa [rU] using
      (theorem_9_1_fixedPointSubgroup_card_eq_prime_pow_finrank_sec9
        (A := U) (M := M) (p := p))
  have hEcard : ∀ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) = p ^ rE u := by
    intro u
    letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    simpa [rE] using
      (theorem_9_1_fixedPointSubgroup_card_eq_prime_pow_finrank_sec9
        (A := E.conjBy (u : G)) (M := M) (p := p))
  have hprod : theorem_9_1_fixedPoint_conjugate_action_product_sec9 U E hEact =
      ∏ u : U, (p ^ rE u) ^ Nat.card (E.conjBy (u : G)) := by
    dsimp [theorem_9_1_fixedPoint_conjugate_action_product_sec9]
    apply Finset.prod_congr rfl
    intro u _hu
    letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    rw [hEcard u]
  have hrank' : rUE * Nat.card UE + rM * Nat.card U =
      (∑ u : U, rE u * Nat.card (E.conjBy (u : G))) + rU * Nat.card U := by
    simpa [rUE, rM, rU, rE] using hrank
  rw [hUEcard, hMcard, hUcard, hprod]
  exact
    theorem_9_1_prime_power_product_identity_of_exponent_sum_sec9
      (p := p) (a := rUE) (b := rM) (d := rU)
      (m := Nat.card UE) (n := Nat.card U)
      (c := rE) (e := fun u : U => Nat.card (E.conjBy (u : G))) hrank'

private theorem theorem_9_1_wielandt_fixedSubspace_finrank_identity_kernel_fixed_top_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
          UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hUtop : fixedPointSubgroup (↥U) M = ⊤) :
    letI : Fintype U := Fintype.ofFinite U
    Module.finrank (ZMod p)
        ↥((Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p)).fixedSubspace
          (⊤ : Subgroup UE)) * Nat.card UE +
      Module.finrank (ZMod p) (Additive M) * Nat.card U =
    (∑ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Module.finrank (ZMod p)
          ↥((Representation.ofElementaryAbelianAction
              (A := E.conjBy (u : G)) (G := M) (p := p)).fixedSubspace
            (⊤ : Subgroup (E.conjBy (u : G)))) *
        Nat.card (E.conjBy (u : G))) +
        Module.finrank (ZMod p)
          ↥((Representation.ofElementaryAbelianAction (A := U) (G := M) (p := p)).fixedSubspace
            (⊤ : Subgroup U)) * Nat.card U := by
    classical
    letI : Fintype U := Fintype.ofFinite U
    let rUE : ℕ := Module.finrank (ZMod p)
      ↥((Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p)).fixedSubspace
        (⊤ : Subgroup UE))
    let rM : ℕ := Module.finrank (ZMod p) (Additive M)
    let rU : ℕ := Module.finrank (ZMod p)
      ↥((Representation.ofElementaryAbelianAction (A := U) (G := M) (p := p)).fixedSubspace
        (⊤ : Subgroup U))
    let rE : U → ℕ := fun u =>
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Module.finrank (ZMod p)
        ↥((Representation.ofElementaryAbelianAction
            (A := E.conjBy (u : G)) (G := M) (p := p)).fixedSubspace
          (⊤ : Subgroup (E.conjBy (u : G))))
    have hUrank : rU = rM := by
      simpa [rU, rM] using
        (fixedSubspace_finrank_eq_full_of_fixedPointSubgroup_eq_top_sec9
          (A := U) (M := M) (p := p) hUtop)
    have hErank : ∀ u : U, rE u = rUE := by
      intro u
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      have hfix :
          fixedPointSubgroup (↥(E.conjBy (u : G))) M =
            fixedPointSubgroup (↥UE) M :=
        fixedPointSubgroup_conj_complement_eq_of_kernel_fixed_top_sec9
          (UE := UE) (U := U) (E := E) (M := M)
          hcomp u hUcompat (hEcompat u) hUtop
      have hcard :
          Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) =
            Nat.card (fixedPointSubgroup (↥UE) M) := by
        rw [hfix]
      simpa [rE, rUE] using
        (fixedSubspace_finrank_eq_of_fixedPointSubgroup_nat_card_eq_sec9
          (A := ↥(E.conjBy (u : G))) (B := ↥UE) (M := M) (p := p) hcard)
    have hEcard : ∀ u : U, Nat.card (E.conjBy (u : G)) = Nat.card E := by
      intro u
      exact section11_card_conjBy (G := G) E (u : G)
    have hUEcard : Nat.card UE = Nat.card U * Nat.card E :=
      section12ComplementIn_nat_card_eq_mul_sec9 UE U E hcomp hfrob
    have hsum :
        (∑ u : U, rE u * Nat.card (E.conjBy (u : G))) =
          rUE * Nat.card UE := by
      calc
        (∑ u : U, rE u * Nat.card (E.conjBy (u : G))) =
            ∑ _u : U, rUE * Nat.card E := by
              apply Finset.sum_congr rfl
              intro u _hu
              rw [hErank u, hEcard u]
        _ = Nat.card U * (rUE * Nat.card E) := by
              simp [Nat.card_eq_fintype_card]
        _ = rUE * Nat.card UE := by
              rw [hUEcard]
              ring
    have hmain :
        rUE * Nat.card UE + rM * Nat.card U =
          (∑ u : U, rE u * Nat.card (E.conjBy (u : G))) + rU * Nat.card U := by
      rw [hsum, hUrank]
    simpa [rUE, rM, rU, rE] using hmain

private theorem fixedPointSubgroup_eq_bot_of_fixedPointSubgroup_subgroup_eq_bot_sec9
    {G M : Type u} [Group G] [Group M]
    {UE U : Subgroup G}
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hUle : U ≤ UE)
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hUle u.2⟩ : UE) • m)
    (hUbot : fixedPointSubgroup (↥U) M = ⊥) :
    fixedPointSubgroup (↥UE) M = ⊥ := by
  apply le_antisymm
  · intro m hm
    have hmU : m ∈ fixedPointSubgroup (↥U) M := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hm ⊢
      intro u
      calc
        u • m = (⟨(u : G), hUle u.2⟩ : UE) • m := hUcompat u m
        _ = m := hm ⟨(u : G), hUle u.2⟩
    simpa [hUbot] using hmU
  · exact bot_le

private theorem theorem_9_1_wielandt_fixedSubspace_finrank_identity_of_coinduction_equiv_sec9
    {F : Type*} [Field F] {A : Type*} [Group A] [Finite A]
    {K R : Subgroup A} [K.Normal] (hKR : K.IsComplement' R)
    {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W]
    (ρ : Representation F A V) (τ : Representation F K W)
    (e : ρ ≃ₗ coindRep τ) :
    Module.finrank F V = Module.finrank F ↥(ρ.fixedSubspace R) * Nat.card R := by
  classical
  letI : Fintype (A ⧸ K) := Fintype.ofFinite (A ⧸ K)
  have hquot : Fintype.card (A ⧸ K) = Nat.card R := by
    calc
      Fintype.card (A ⧸ K) = K.index := by
        simpa using K.index_eq_card.symm
      _ = Nat.card R := hKR.symm.index_eq_card
  have hdimV :
      Module.finrank F V = Module.finrank F (Representation.coindV K.subtype τ) := by
    exact LinearEquiv.finrank_eq e.toLinearEquiv
  have hcoind :
      Module.finrank F (Representation.coindV K.subtype τ) =
        Fintype.card (A ⧸ K) * Module.finrank F W := by
    simpa using (finrank_coindRep_eq_card_mul (ρ := τ))
  have hfix_coind :
      Module.finrank F ↥((coindRep (ρ := τ)).fixedSubspace R) = Module.finrank F W := by
    exact LinearEquiv.finrank_eq (coindFixedSubspaceEquiv_of_isComplement' (ρ := τ) hKR)
  have hfixρ :
      Module.finrank F ↥(ρ.fixedSubspace R) =
        Module.finrank F ↥((coindRep (ρ := τ)).fixedSubspace R) := by
    exact LinearEquiv.finrank_eq (fixedSubspace_equiv_of_repEquiv e R)
  calc
    Module.finrank F V = Module.finrank F (Representation.coindV K.subtype τ) := hdimV
    _ = Fintype.card (A ⧸ K) * Module.finrank F W := hcoind
    _ = Nat.card R * Module.finrank F W := by rw [hquot]
    _ = Nat.card R * Module.finrank F ↥((coindRep (ρ := τ)).fixedSubspace R) := by
          rw [hfix_coind]
    _ = Nat.card R * Module.finrank F ↥(ρ.fixedSubspace R) := by rw [← hfixρ]
    _ = Module.finrank F ↥(ρ.fixedSubspace R) * Nat.card R := by rw [Nat.mul_comm]

private theorem theorem_9_1_fixedSubspace_subgroupOf_top_eq_sec9
    {A M : Type u} [Group A] [Group M] [MulDistribMulAction A M]
    (R : Subgroup A) {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] :
    letI : MulDistribMulAction (↥R) M := MulDistribMulAction.compHom M R.subtype
    (Representation.ofElementaryAbelianAction (A := R) (G := M) (p := p)).fixedSubspace
        (⊤ : Subgroup R) =
      (Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)).fixedSubspace R := by
  classical
  ext x
  rw [Representation.fixedSubspace, Representation.mem_invariants]
  rw [Representation.fixedSubspace, Representation.mem_invariants]
  constructor
  · intro hx r
    simpa using hx ⟨r, by simp⟩
  · intro hx r
    simpa using hx r.1

public theorem theorem_9_1_ofElementaryAbelianAction_irreducible_of_minimal_invariant_sec9
    {A M : Type u} [Group A] [Group M] [MulDistribMulAction A M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [Nontrivial M]
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant A M N → N ≠ ⊥ → N = ⊤) :
    Representation.IsIrreducible
      (Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)) := by
  let ρ := Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)
  refine
    { toNontrivial := inferInstance
      eq_bot_or_eq_top := ?_ }
  intro S
  let N : Subgroup M := S.toSubmodule.toAddSubgroup.toSubgroup'
  have hN_inv : IsInvariant A M N := by
    have hmap_mem (a : A) {x : M} (hx : x ∈ N) : a • x ∈ N := by
      change Additive.ofMul (a • x) ∈ S.toSubmodule
      have hx' : Additive.ofMul x ∈ S.toSubmodule := by
        simpa [Submodule.mem_toAddSubgroup] using hx
      have hx'' := S.apply_mem_toSubmodule a hx'
      simpa [ρ, Representation.ofElementaryAbelianAction_apply_ofMul] using hx''
    refine { invariant := ?_ }
    intro a x
    constructor
    · intro hx
      exact hmap_mem a hx
    · intro hx
      have hx' : (a : A)⁻¹ • ((a : A) • x) ∈ N := hmap_mem (a : A)⁻¹ hx
      simpa [smul_smul] using hx'
  by_cases hN_bot : N = ⊥
  · left
    apply Subrepresentation.toSubmodule_injective
    ext x
    have hxN : Additive.toMul x ∈ N ↔ x ∈ S.toSubmodule := by
      simp [N]
    rw [← hxN, hN_bot]
    constructor
    · intro hx
      simpa [hx]
    · intro hx
      simpa using hx
  · right
    have hN_top : N = ⊤ := hminv N inferInstance hN_inv hN_bot
    apply Subrepresentation.toSubmodule_injective
    ext x
    have hxN : Additive.toMul x ∈ N ↔ x ∈ S.toSubmodule := by
      simp [N]
    rw [← hxN, hN_top]
    constructor
    · intro _hx
      exact trivial
    · intro _hx
      exact trivial

private theorem theorem_9_1_fixedSubspace_subgroupOf_eq_bot_of_fixedPointSubgroup_eq_bot_sec9
    {G M : Type u} [Group G] [Group M]
    {UE U : Subgroup G}
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hUle : U ≤ UE)
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hUle u.2⟩ : UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hUbot : fixedPointSubgroup (↥U) M = ⊥) :
    (Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p)).fixedSubspace
        (U.subgroupOf UE) = ⊥ := by
  classical
  let ρ := Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p)
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_bot]
    rw [Representation.fixedSubspace, Representation.mem_invariants] at hx
    have hxU : Additive.toMul x ∈ fixedPointSubgroup (↥U) M := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro u
      let uUE : UE := ⟨(u : G), hUle u.2⟩
      let uK : U.subgroupOf UE := ⟨uUE, by simp [uUE, Subgroup.mem_subgroupOf, u.2]⟩
      have hxK : ρ uK x = x := hx uK
      have hUEsmul : (uUE : UE) • Additive.toMul x = Additive.toMul x := by
        apply Additive.ofMul.injective
        change Additive.ofMul ((uUE : UE) • Additive.toMul x) = x
        simpa [ρ, Representation.ofElementaryAbelianAction_apply_ofMul] using hxK
      calc
        u • Additive.toMul x = (uUE : UE) • Additive.toMul x := hUcompat u (Additive.toMul x)
        _ = Additive.toMul x := hUEsmul
    have hx_bot : Additive.toMul x ∈ (⊥ : Subgroup M) := by
      simpa [hUbot] using hxU
    have hx_one : Additive.toMul x = 1 := by
      simpa using hx_bot
    change Additive.ofMul (Additive.toMul x) = 0
    simp [hx_one]
  · exact bot_le

private theorem theorem_9_1_wielandt_fixedPointSubgroup_complement_card_identity_kernel_fixed_bot_source_bridge_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M] [Nontrivial M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hUbot : fixedPointSubgroup (↥U) M = ⊥) :
    letI : MulDistribMulAction (↥(E.subgroupOf UE)) M :=
      MulDistribMulAction.compHom M (E.subgroupOf UE).subtype
    Nat.card M = Nat.card (fixedPointSubgroup (↥(E.subgroupOf UE)) M) ^ Nat.card E := by
  classical
  exact
    Wielandt.fixedPointSubgroup_complement_card_identity_kernel_fixed_bot
      (p := p) UE U E hcomp hfrob hcop hUcompat hUbot

private theorem theorem_9_1_wielandt_fixedSubspace_complement_finrank_identity_kernel_fixed_bot_source_bridge_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M] [Nontrivial M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hUbot : fixedPointSubgroup (↥U) M = ⊥) :
    letI : MulDistribMulAction (↥(E.subgroupOf UE)) M :=
      MulDistribMulAction.compHom M (E.subgroupOf UE).subtype
    Module.finrank (ZMod p) (Additive M) =
      Module.finrank (ZMod p)
          ↥((Representation.ofElementaryAbelianAction
            (A := E.subgroupOf UE) (G := M) (p := p)).fixedSubspace
          (⊤ : Subgroup (E.subgroupOf UE))) *
        Nat.card E := by
  classical
  letI : MulDistribMulAction (↥(E.subgroupOf UE)) M :=
    MulDistribMulAction.compHom M (E.subgroupOf UE).subtype
  exact
    full_finrank_eq_fixedSubspace_finrank_mul_of_fixedPoint_card_pow_sec9
      (A := E.subgroupOf UE) (M := M) (p := p) (n := Nat.card E)
      (theorem_9_1_wielandt_fixedPointSubgroup_complement_card_identity_kernel_fixed_bot_source_bridge_sec9
        (p := p) UE U E hcomp hfrob hcop hUcompat hUbot)

private theorem theorem_9_1_wielandt_fixedSubspace_finrank_identity_kernel_fixed_bot_reduced_source_bridge_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M] [Nontrivial M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
          UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hUbot : fixedPointSubgroup (↥U) M = ⊥) :
    letI : Fintype U := Fintype.ofFinite U
    Module.finrank (ZMod p) (Additive M) * Nat.card U =
    ∑ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Module.finrank (ZMod p)
          ↥((Representation.ofElementaryAbelianAction
              (A := E.conjBy (u : G)) (G := M) (p := p)).fixedSubspace
            (⊤ : Subgroup (E.conjBy (u : G)))) *
        Nat.card (E.conjBy (u : G)) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  letI : MulDistribMulAction (↥(E.subgroupOf UE)) M :=
    MulDistribMulAction.compHom M (E.subgroupOf UE).subtype
  let rM : ℕ := Module.finrank (ZMod p) (Additive M)
  let rE0 : ℕ := Module.finrank (ZMod p)
    ↥((Representation.ofElementaryAbelianAction
        (A := E.subgroupOf UE) (G := M) (p := p)).fixedSubspace
      (⊤ : Subgroup (E.subgroupOf UE)))
  let rE : U → ℕ := fun u =>
    letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    Module.finrank (ZMod p)
      ↥((Representation.ofElementaryAbelianAction
          (A := E.conjBy (u : G)) (G := M) (p := p)).fixedSubspace
        (⊤ : Subgroup (E.conjBy (u : G))))
  have hbase : rM = rE0 * Nat.card E := by
    simpa [rM, rE0] using
      (theorem_9_1_wielandt_fixedSubspace_complement_finrank_identity_kernel_fixed_bot_source_bridge_sec9
        (p := p) UE U E hcomp hfrob hcop hUcompat hUbot)
  have hErank : ∀ u : U, rE u = rE0 := by
    intro u
    letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    have hequiv :=
      fixedPointSubgroup_conj_complement_equiv_sec9
        (UE := UE) (U := U) (E := E) (M := M) hcomp u (hEcompat u)
    have hcard :
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) =
          Nat.card (fixedPointSubgroup (↥(E.subgroupOf UE)) M) :=
      Nat.card_congr hequiv.symm
    simpa [rE, rE0] using
      (fixedSubspace_finrank_eq_of_fixedPointSubgroup_nat_card_eq_sec9
        (A := ↥(E.conjBy (u : G))) (B := ↥(E.subgroupOf UE)) (M := M) (p := p)
        hcard)
  have hEcard : ∀ u : U, Nat.card (E.conjBy (u : G)) = Nat.card E := by
    intro u
    exact section11_card_conjBy (G := G) E (u : G)
  have hsum :
      (∑ u : U, rE u * Nat.card (E.conjBy (u : G))) =
        Nat.card U * (rE0 * Nat.card E) := by
    calc
      (∑ u : U, rE u * Nat.card (E.conjBy (u : G))) =
          ∑ _u : U, rE0 * Nat.card E := by
            apply Finset.sum_congr rfl
            intro u _hu
            rw [hErank u, hEcard u]
      _ = Nat.card U * (rE0 * Nat.card E) := by
            simp [Nat.card_eq_fintype_card]
  have hmain :
      rM * Nat.card U =
        ∑ u : U, rE u * Nat.card (E.conjBy (u : G)) := by
    rw [hsum, hbase]
    ring
  simpa [rM, rE] using hmain

private theorem theorem_9_1_wielandt_fixedSubspace_finrank_identity_kernel_fixed_bot_source_bridge_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M] [Nontrivial M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
          UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hUbot : fixedPointSubgroup (↥U) M = ⊥) :
    letI : Fintype U := Fintype.ofFinite U
    Module.finrank (ZMod p)
        ↥((Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p)).fixedSubspace
          (⊤ : Subgroup UE)) * Nat.card UE +
      Module.finrank (ZMod p) (Additive M) * Nat.card U =
    (∑ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Module.finrank (ZMod p)
          ↥((Representation.ofElementaryAbelianAction
              (A := E.conjBy (u : G)) (G := M) (p := p)).fixedSubspace
            (⊤ : Subgroup (E.conjBy (u : G)))) *
        Nat.card (E.conjBy (u : G))) +
      Module.finrank (ZMod p)
          ↥((Representation.ofElementaryAbelianAction (A := U) (G := M) (p := p)).fixedSubspace
            (⊤ : Subgroup U)) * Nat.card U := by
    classical
    have hUrank :
        Module.finrank (ZMod p)
            ↥((Representation.ofElementaryAbelianAction (A := U) (G := M) (p := p)).fixedSubspace
              (⊤ : Subgroup U)) = 0 := by
      simpa using
        (fixedSubspace_finrank_eq_zero_of_fixedPointSubgroup_eq_bot_sec9
          (A := U) (M := M) (p := p) hUbot)
    have hUEbot : fixedPointSubgroup (↥UE) M = ⊥ :=
      fixedPointSubgroup_eq_bot_of_fixedPointSubgroup_subgroup_eq_bot_sec9
        (UE := UE) (U := U) hcomp.1 hUcompat hUbot
    have hUErank :
        Module.finrank (ZMod p)
            ↥((Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p)).fixedSubspace
              (⊤ : Subgroup UE)) = 0 := by
      simpa using
        (fixedSubspace_finrank_eq_zero_of_fixedPointSubgroup_eq_bot_sec9
          (A := UE) (M := M) (p := p) hUEbot)
    have hcore :=
      theorem_9_1_wielandt_fixedSubspace_finrank_identity_kernel_fixed_bot_reduced_source_bridge_sec9
        (p := p) UE U E hEact hcomp hfrob hcop hUcompat hEcompat hUbot
    rw [hUErank, hUrank]
    simpa using hcore

private theorem theorem_9_1_wielandt_fixedSubspace_finrank_identity_source_bridge_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M] [Nontrivial M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
          UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant UE M N → N ≠ ⊥ → N = ⊤) :
    letI : Fintype U := Fintype.ofFinite U
    Module.finrank (ZMod p)
        ↥((Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p)).fixedSubspace
          (⊤ : Subgroup UE)) * Nat.card UE +
      Module.finrank (ZMod p) (Additive M) * Nat.card U =
    (∑ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Module.finrank (ZMod p)
          ↥((Representation.ofElementaryAbelianAction
              (A := E.conjBy (u : G)) (G := M) (p := p)).fixedSubspace
            (⊤ : Subgroup (E.conjBy (u : G)))) *
        Nat.card (E.conjBy (u : G))) +
      Module.finrank (ZMod p)
        ↥((Representation.ofElementaryAbelianAction (A := U) (G := M) (p := p)).fixedSubspace
          (⊤ : Subgroup U)) * Nat.card U := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  have hUnorm : (U.subgroupOf UE).Normal := by
    have hUnormSup : (U.subgroupOf (U ⊔ E)).Normal :=
      IsFrobeniusGroupWithKernelComplement.normal hfrob
    have hUEeq : UE = U ⊔ E := hcomp.2.2.1
    subst UE
    simpa using hUnormSup
  have hUeq :
      fixedPointSubgroup (↥U) M =
        letI : MulDistribMulAction (↥(U.subgroupOf UE)) M :=
          MulDistribMulAction.compHom M (U.subgroupOf UE).subtype
        fixedPointSubgroup (↥(U.subgroupOf UE)) M :=
    fixedPointSubgroup_eq_subgroupOf_of_compatible_sec9
      UE U hcomp.1 hUcompat
  have hUinv : IsInvariant UE M (fixedPointSubgroup (↥U) M) := by
    rw [hUeq]
    exact fixedPointSubgroup_invariant_of_normal_sec9 (A := UE) (M := M)
      (U.subgroupOf UE)
  by_cases hUbot : fixedPointSubgroup (↥U) M = ⊥
  · exact
      theorem_9_1_wielandt_fixedSubspace_finrank_identity_kernel_fixed_bot_source_bridge_sec9
        (p := p) UE U E hEact hcomp hfrob hcop hUcompat hEcompat hUbot
  · have hUtop : fixedPointSubgroup (↥U) M = ⊤ :=
      hminv (fixedPointSubgroup (↥U) M) inferInstance hUinv hUbot
    exact
      theorem_9_1_wielandt_fixedSubspace_finrank_identity_kernel_fixed_top_sec9
        (p := p) UE U E hEact hcomp hfrob hUcompat hEcompat hUtop

private theorem theorem_9_1_wielandt_fixedPoint_product_identity_action_elementaryAbelian_source_bridge_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M] [Nontrivial M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
          UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant UE M N → N ≠ ⊥ → N = ⊤) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      theorem_9_1_fixedPoint_conjugate_action_product_sec9 U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  exact
    theorem_9_1_wielandt_fixedPoint_product_identity_action_elementaryAbelian_of_finrank_identity_sec9
      (p := p) UE U E hEact
      (theorem_9_1_wielandt_fixedSubspace_finrank_identity_source_bridge_sec9
        (p := p) UE U E hEact hcomp hfrob hcop hUcompat hEcompat hminv)

private theorem theorem_9_1_wielandt_fixedPoint_product_identity_action_chiefFactor_source_bridge_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hsolvM : IsSolvable M)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
          UE) • m)
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant UE M N → N ≠ ⊥ → N = ⊤) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      theorem_9_1_fixedPoint_conjugate_action_product_sec9 U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  rcases theorem_9_1_chiefFactor_elementaryAbelian_or_subsingleton_sec9
      (A := UE) (M := M) hsolvM hminv with hsub | ⟨hNontriv, p, hp, hElem⟩
  · letI : Subsingleton M := hsub
    have hMcard : Nat.card M = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    have hUEcard : Nat.card (fixedPointSubgroup (↥UE) M) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    have hUcard : Nat.card (fixedPointSubgroup (↥U) M) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    have hEcard : ∀ u : U,
        letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) = 1 := by
      intro u
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    dsimp [theorem_9_1_fixedPoint_conjugate_action_product_sec9]
    rw [hUEcard, hMcard, hUcard]
    letI : Fintype U := Fintype.ofFinite U
    have hprod : (∏ u : U,
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) ^
          Nat.card (E.conjBy (u : G))) = 1 := by
      refine Finset.prod_eq_one ?_
      intro u _hu
      rw [hEcard u]
      simp
    rw [hprod]
    simp
  · letI : Fact p.Prime := ⟨hp⟩
    letI : Nontrivial M := hNontriv
    letI : IsElementaryAbelian p M := hElem
    exact
      theorem_9_1_wielandt_fixedPoint_product_identity_action_elementaryAbelian_source_bridge_sec9
        (p := p) UE U E hEact hcomp hfrob hcop hUcompat hEcompat hminv

private theorem theorem_9_1_wielandt_fixedPoint_product_identity_action_source_bridge_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hsolvM : IsSolvable M)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
          UE) • m) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      theorem_9_1_fixedPoint_conjugate_action_product_sec9 U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  have hEcompat' : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), Wielandt.section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) • m := by
    intro u e m
    simpa using hEcompat u e m
  have haction :=
    Wielandt.fixedPointSubgroup_product_identity_action
      (UE := UE) (U := U) (E := E) (M := M)
      hEact hcomp hfrob hsolvM hcop hUcompat hEcompat'
  rw [Wielandt.fixedPointSubgroup_conjBy_action_product_eq_prod U E hEact] at haction
  simpa [theorem_9_1_fixedPoint_conjugate_action_product_sec9] using haction

private theorem theorem_9_1_wielandt_fixedPoint_product_identity_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (UE U E H : Subgroup G)
    (h91 : frobeniusActionData UE U E H)
    (hUE_norm_H : UE ≤ Subgroup.normalizer (H : Set G))
    (hU_norm_H : U ≤ Subgroup.normalizer (H : Set G))
    (hEnormH : ∀ u : U, E.conjBy (u : G) ≤ Subgroup.normalizer (H : Set G)) :
    letI : Subgroup.Normalizes UE H := ⟨hUE_norm_H⟩
    letI : Subgroup.Normalizes U H := ⟨hU_norm_H⟩
    Nat.card (fixedPointSubgroup (↥UE) H) ^ Nat.card UE *
        Nat.card H ^ Nat.card U =
      theorem_9_1_fixedPoint_conjugate_complement_product_sec9 U E H hEnormH *
        Nat.card (fixedPointSubgroup (↥U) H) ^ Nat.card U := by
  classical
  rcases h91 with ⟨hcomp, hfrob, _hUE_norm_H', hsolvH, hcopHUE⟩
  letI : Subgroup.Normalizes UE H := ⟨hUE_norm_H⟩
  letI : Subgroup.Normalizes U H := ⟨hU_norm_H⟩
  let hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) H := fun u => by
    letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
    infer_instance
  have hUcompat : ∀ (u : U) (h : H),
      u • h = (⟨(u : G), hcomp.1 u.2⟩ : UE) • h := by
    intro u h
    ext
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  have hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (h : H),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) H := hEact u
      e • h =
        (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
          UE) • h := by
    intro u e h
    ext
    simp [hEact, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  have haction :=
    theorem_9_1_wielandt_fixedPoint_product_identity_action_source_bridge_sec9
      (UE := UE) (U := U) (E := E) (M := H) hEact hcomp hfrob hsolvH hcopHUE
      hUcompat hEcompat
  rw [theorem_9_1_fixedPoint_conjugate_complement_product_eq_action_product_sec9 U E H hEnormH]
  simpa [hEact] using haction

private theorem theorem_9_1_wielandt_conjugate_product_identity_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      Nat.card (subgroupCentralizerIn H UE) ^ Nat.card UE *
          Nat.card H ^ Nat.card U =
        theorem_9_1_conjugate_complement_product_sec9 U E H *
          Nat.card (subgroupCentralizerIn H U) ^ Nat.card U := by
  intro h91
  have h91_all : frobeniusActionData UE U E H := h91
  rcases h91 with ⟨hcomp, _hfrob, hUE_norm_H, _hH_solv, _hcop⟩
  have hU_norm_H : U ≤ Subgroup.normalizer (H : Set G) :=
    fun u hu => hUE_norm_H (hcomp.1 hu)
  have hEnormH :
      ∀ u : U, E.conjBy (u : G) ≤ Subgroup.normalizer (H : Set G) := by
    intro u x hx
    apply hUE_norm_H
    rw [Subgroup.conjBy, Subgroup.mem_map] at hx
    rcases hx with ⟨e, heE, hxe⟩
    rw [← hxe]
    exact UE.mul_mem (UE.mul_mem (hcomp.1 u.property) (hcomp.2.1 heE))
      (UE.inv_mem (hcomp.1 u.property))
  have hfixed :=
    theorem_9_1_wielandt_fixedPoint_product_identity_source_bridge_sec9
      UE U E H h91_all hUE_norm_H hU_norm_H hEnormH
  letI : Subgroup.Normalizes UE H := ⟨hUE_norm_H⟩
  letI : Subgroup.Normalizes U H := ⟨hU_norm_H⟩
  have hUEcard :=
    fixedPointSubgroup_card_eq_subgroupCentralizerIn_sec9 H UE hUE_norm_H
  have hUcard :=
    fixedPointSubgroup_card_eq_subgroupCentralizerIn_sec9 H U hU_norm_H
  have hprod :=
    theorem_9_1_fixedPoint_conjugate_complement_product_eq_centralizer_product_sec9
      U E H hEnormH
  rw [hUEcard, hUcard, hprod] at hfixed
  exact hfixed

private theorem theorem_9_1_wielandt_product_identity_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      Nat.card (subgroupCentralizerIn H UE) ^ Nat.card UE *
          Nat.card H ^ Nat.card U =
        Nat.card (subgroupCentralizerIn H E) ^ (Nat.card E * Nat.card U) *
          Nat.card (subgroupCentralizerIn H U) ^ Nat.card U := by
  intro h91
  have hprod :=
    theorem_9_1_wielandt_conjugate_product_identity_source_bridge_sec9 UE U E H h91
  rw [hprod]
  rw [frobeniusActionData_conjugate_complement_product_eq_power_sec9 UE U E H h91]

private theorem theorem_9_1_wielandt_power_identity_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      (Nat.card (subgroupCentralizerIn H (U ⊔ E)) ^ Nat.card E *
          Nat.card H) ^ Nat.card U =
        (Nat.card (subgroupCentralizerIn H E) ^ Nat.card E *
            Nat.card (subgroupCentralizerIn H U)) ^ Nat.card U := by
  intro h91
  rcases h91 with ⟨hcomp, hfrob, hUE_norm_H, hH_solv, hcop⟩
  have h91' : frobeniusActionData UE U E H :=
    ⟨hcomp, hfrob, hUE_norm_H, hH_solv, hcop⟩
  have hraw := theorem_9_1_wielandt_product_identity_source_bridge_sec9 UE U E H h91'
  have hcardUE := frobeniusActionData_nat_card_eq_mul_sec9 UE U E H h91'
  have hUEeq : UE = U ⊔ E := hcomp.2.2.1
  rw [hUEeq] at hraw hcardUE
  rw [mul_pow, mul_pow]
  rw [← pow_mul, ← pow_mul]
  rw [← hraw]
  rw [hcardUE, Nat.mul_comm (Nat.card U) (Nat.card E)]

public theorem theorem_9_1_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      Nat.card (subgroupCentralizerIn H (U ⊔ E)) ^ Nat.card E * Nat.card H =
        Nat.card (subgroupCentralizerIn H E) ^ Nat.card E *
          Nat.card (subgroupCentralizerIn H U) := by
  intro h91
  have hpow :=
    theorem_9_1_wielandt_power_identity_source_bridge_sec9 UE U E H h91
  exact Nat.pow_left_injective (Nat.card_pos (α := U)).ne' hpow

public theorem theorem_9_1_centralizes_of_fixed_points_trivial_sec9
    {G : Type u} [Group G] [Finite G]
    (U E H : Subgroup G)
    (hcard : Nat.card (subgroupCentralizerIn H (U ⊔ E)) ^ Nat.card E * Nat.card H =
      Nat.card (subgroupCentralizerIn H E) ^ Nat.card E *
        Nat.card (subgroupCentralizerIn H U)) :
    subgroupCentralizerIn H E = ⊥ → subgroupCentralizerIn H U = H := by
  intro hCE_bot
  have hCUE_bot : subgroupCentralizerIn H (U ⊔ E) = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxE := subgroupCentralizerIn_sup_le_right_sec9 H U E hx
      simpa [hCE_bot] using hxE
    · exact bot_le
  have hCU_card : Nat.card (subgroupCentralizerIn H U) = Nat.card H := by
    have h := hcard.symm
    simpa [hCUE_bot, hCE_bot] using h
  exact subgroupCentralizerIn_eq_left_of_card_eq_sec9 H U hCU_card

public theorem theorem_9_1_card_eq_of_kernel_fixed_points_trivial_sec9
    {G : Type u} [Group G] [Finite G]
    (U E H : Subgroup G)
    (hcard : Nat.card (subgroupCentralizerIn H (U ⊔ E)) ^ Nat.card E * Nat.card H =
      Nat.card (subgroupCentralizerIn H E) ^ Nat.card E *
        Nat.card (subgroupCentralizerIn H U)) :
    subgroupCentralizerIn H U = ⊥ →
      Nat.card H = Nat.card (subgroupCentralizerIn H E) ^ Nat.card E := by
  intro hCU_bot
  have hCUE_bot : subgroupCentralizerIn H (U ⊔ E) = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxU := subgroupCentralizerIn_sup_le_left_sec9 H U E hx
      simpa [hCU_bot] using hxU
    · exact bot_le
  simpa [hCUE_bot, hCU_bot] using hcard

public theorem theorem_9_1
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      Nat.card (subgroupCentralizerIn H (U ⊔ E)) ^ Nat.card E * Nat.card H =
        Nat.card (subgroupCentralizerIn H E) ^ Nat.card E *
          Nat.card (subgroupCentralizerIn H U) ∧
        (subgroupCentralizerIn H E = ⊥ → subgroupCentralizerIn H U = H) ∧
        (subgroupCentralizerIn H U = ⊥ →
          Nat.card H = Nat.card (subgroupCentralizerIn H E) ^ Nat.card E) := by
  intro h91
  have hcard := theorem_9_1_source_core_sec9 UE U E H h91
  exact ⟨hcard,
    theorem_9_1_centralizes_of_fixed_points_trivial_sec9 U E H hcard,
    theorem_9_1_card_eq_of_kernel_fixed_points_trivial_sec9 U E H hcard⟩

end Section9
