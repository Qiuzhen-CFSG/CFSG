module
public import Theory.GroupAction.AbelianCoprimeFixedGeneration
public import Theory.GroupTheory.NormalizedSupCard

/-!
# A common fixed normalizer point for a rank-three binary actor

Let an elementary abelian 2-group A of order at least eight act on a finite
group G. If two A-invariant q-subgroups, for an odd prime q, both properly
contain their intersection D, some nonidentity element of A fixes points
of each normalizer N_Qᵢ(D) outside D. The conclusion uses the ambient
normalizer and fixed-point subgroups for the original supplied action.

The normalizer condition for finite q-groups makes D proper in N_Qᵢ(D).
Coprime abelian fixed-point generation then supplies actor subgroups Bᵢ
with cyclic quotient whose fixed groups in N_Qᵢ(D) are not contained in D.
Since A has exponent two, each Bᵢ has index at most two. The product-order
formula and |A| ≥ 8 force B₁ ∩ B₂ to be nontrivial. Any nonidentity element
of that intersection fixes both selected fixed groups.

This is the binary-actor specialization of Kurzweil–Stellmacher,
*The Theory of Finite Groups*, Lemma 11.1.7, printed pp. 308–309. Its
hypotheses make sense independently of the signalizer-functor application.
-/

open scoped IsMulCommutative

private theorem cyclic_quotient_intersection_ne_bot
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (Y Z : Subgroup A)
    (hY : IsCyclic (A ⧸ Y)) (hZ : IsCyclic (A ⧸ Z)) : Y ⊓ Z ≠ ⊥ := by
  have hbound (B : Subgroup A) (hB : IsCyclic (A ⧸ B)) :
      Nat.card A ≤ 2 * Nat.card B := by
    have hdiv : Nat.card (A ⧸ B) ∣ 2 := by
      rw [← hB.exponent_eq_card]
      exact (Group.exponent_quotient_dvd B).trans
        (IsElementaryAbelian.exponent_dvd_p 2 A)
    calc
      Nat.card A = Nat.card (A ⧸ B) * Nat.card B :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup B
      _ ≤ 2 * Nat.card B := Nat.mul_le_mul_right _ (Nat.le_of_dvd (by decide) hdiv)
  have hmul := Nat.mul_le_mul (hbound Y hY) (hbound Z hZ)
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes Y Z
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hsup : Nat.card (Y ⊔ Z : Subgroup A) ≤ Nat.card A :=
    Nat.card_le_card_of_injective (Y ⊔ Z : Subgroup A).subtype
      (Y ⊔ Z : Subgroup A).subtype_injective
  intro heq
  rw [heq, Subgroup.card_bot, one_mul] at hprod
  nlinarith

private theorem exists_cyclic_quotient_fixed_normalizer
    {A G : Type*} [CommGroup A] [Finite A] [Group G] [Finite G]
    [MulDistribMulAction A G] {q : ℕ} [Fact q.Prime]
    (hcop : Nat.Coprime (Nat.card A) q) (Q D : Subgroup G)
    [IsInvariant A G Q] [IsInvariant A G D]
    (hQ : IsPGroup q Q) (hD : D < Q) :
    ∃ B : Subgroup A, IsCyclic (A ⧸ B) ∧
      ¬ Q ⊓ Subgroup.normalizer (D : Set G) ⊓ FixedPoints.subgroup B G ≤ D := by
  let N := Q ⊓ Subgroup.normalizer (D : Set G)
  let _ : IsInvariant A G (Subgroup.normalizer (D : Set G)) := isInvariant_normalizer D
  let _ : IsInvariant A G N := isInvariant_inf Q (Subgroup.normalizer (D : Set G))
  let _ : Fact (IsPGroup q N) := ⟨hQ.to_le inf_le_left⟩
  let _ : Group.IsNilpotent Q := hQ.isNilpotent
  have hproper : D.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact not_le_of_gt hD
  have hnormalizer := Group.normalizerCondition_of_isNilpotent (D.subgroupOf Q) hproper
  obtain ⟨x, hxN, hxD⟩ := SetLike.exists_of_lt hnormalizer
  have hxN' : (x : G) ∈ Subgroup.normalizer (D : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hD.le] at hxN
    exact hxN
  have hNnot : ¬ N ≤ D := fun h => hxD (h ⟨x.property, hxN'⟩)
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
    (G := N) (A := A) (q := q) hcop
  by_contra hn
  push Not at hn
  have hle : (⊤ : Subgroup N) ≤ D.subgroupOf N := by
    rw [← hgen]
    refine iSup₂_le fun B hB y hy => ?_
    apply hn B hB
    refine ⟨y.property, ?_⟩
    intro b
    exact congrArg Subtype.val (hy b)
  apply hNnot
  intro y hy
  exact hle (show (⟨y, hy⟩ : N) ∈ (⊤ : Subgroup N) from Subgroup.mem_top _)

/-- Two invariant odd-prime subgroups with proper intersection have a common
nonidentity actor whose fixed normalizer points escape the intersection. -/
public theorem exists_nontrivial_common_fixed_normalizer
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
    [IsElementaryAbelian 2 A] [MulDistribMulAction A G]
    {q : ℕ} [Fact q.Prime] (hA : 8 ≤ Nat.card A) (hq : q ≠ 2)
    (Q₁ Q₂ : Subgroup G) [IsInvariant A G Q₁] [IsInvariant A G Q₂]
    (hQ₁ : IsPGroup q Q₁) (hQ₂ : IsPGroup q Q₂)
    (h₁ : Q₁ ⊓ Q₂ < Q₁) (h₂ : Q₁ ⊓ Q₂ < Q₂) :
    ∃ a : A, a ≠ 1 ∧
      ¬ (Q₁ ⊓ Subgroup.normalizer (↑(Q₁ ⊓ Q₂) : Set G) ⊓
        FixedPoints.subgroup (Subgroup.zpowers a) G ≤ Q₁ ⊓ Q₂) ∧
      ¬ (Q₂ ⊓ Subgroup.normalizer (↑(Q₁ ⊓ Q₂) : Set G) ⊓
        FixedPoints.subgroup (Subgroup.zpowers a) G ≤ Q₁ ⊓ Q₂) := by
  classical
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  let _ : IsInvariant A G (Q₁ ⊓ Q₂) := isInvariant_inf Q₁ Q₂
  have hcop : Nat.Coprime (Nat.card A) q := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    rw [hn]
    exact ((Nat.coprime_primes Nat.prime_two (Fact.out : q.Prime)).mpr hq.symm).pow_left n
  obtain ⟨B₁, hB₁, hfix₁⟩ :=
    exists_cyclic_quotient_fixed_normalizer hcop Q₁ (Q₁ ⊓ Q₂) hQ₁ h₁
  obtain ⟨B₂, hB₂, hfix₂⟩ :=
    exists_cyclic_quotient_fixed_normalizer hcop Q₂ (Q₁ ⊓ Q₂) hQ₂ h₂
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (cyclic_quotient_intersection_ne_bot hA B₁ B₂ hB₁ hB₂)
  have hfixed (B : Subgroup A) (haB : (a : A) ∈ B) :
      FixedPoints.subgroup B G ≤ FixedPoints.subgroup (Subgroup.zpowers (a : A)) G := by
    intro x hx z
    exact hx ⟨z, (Subgroup.zpowers_le.mpr haB) z.property⟩
  refine ⟨a, fun h => ha (Subtype.ext h), ?_, ?_⟩
  · intro h
    apply hfix₁
    exact (inf_le_inf_left _ (hfixed B₁ a.property.1)).trans h
  · intro h
    apply hfix₂
    exact (inf_le_inf_left _ (hfixed B₂ a.property.2)).trans h
