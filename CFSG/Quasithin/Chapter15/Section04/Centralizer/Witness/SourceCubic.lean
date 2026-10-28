module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SourceCubic.Omega
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SourceCubic.NineLift

/-!
# The source normal cubic witness in 15.4.9

Construct P=Ω₁(Z(O₃(H/O₂(H)))) for H=C_G(Z), from the actual earlier
solvability, prime-order and three-rank bounds. If its order is nine and
the Sylow image preserves no cubic subgroup, the literal residual lift
belongs to uppercase Ξ: its iterated Frattini quotient action is
irreducible. This contradicts the original exclusion of Ξ inside H.
The four-point action then supplies a normal cubic subgroup, whose
residual lift belongs to the original NormalCentralizerXi family.

The hypotheses retained here are genuine preceding source reductions:
15.4.2(3), 15.4.5, and the SQTK three-rank bound, owned by
qt-15-04-prime-reduction and qt-15-04-centralizer-witness. Normality,
elementarity, quotient-rank control and reducibility are proved here.
This module does not assume or prove 15.4.10.

Source: Aschbacher--Smith 15.4.9, printed p.1159.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SourceCubic
open FamilySource

private theorem cubic_card_of_proper {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 3 E] (hE : Nat.card E = 9) (A : Subgroup E)
    (hAb : A ≠ ⊥) (hAt : A ≠ ⊤) : Nat.card A = 3 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).mp
    ((IsElementaryAbelian.isPGroup (p := 3) (G := E)).to_subgroup A)
  have hnle : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp
    (by simpa only [hn, hE] using Subgroup.card_le_card_group A)
  have hnzero : n ≠ 0 := by
    intro he
    exact hAb (Subgroup.card_eq_one.mp (by simpa only [he, pow_zero] using hn))
  have hntwo : n ≠ 2 := by
    intro he
    apply hAt
    apply A.eq_top_of_card_eq
    rw [hE, hn, he]
    norm_num
  have he : n = 1 := by omega
  simpa only [he, pow_one] using hn

variable {G : Type*} [Group G] [Finite G]

/-- The actual uppercase-Ξ exclusion supplies a Sylow-invariant cubic
subgroup of the elementary nine-subgroup in the centralizer quotient. -/
theorem invariant_cubic_of_no_upper_Xi (T Z : Subgroup G)
    (hZT : Z ≤ T) (hTC : T ≤ centralizer (Z : Set G))
    (hZne : Z ≠ ⊥) (hZtwo : IsPGroup 2 Z)
    (P : Subgroup (CoreQuotient (centralizer (Z : Set G))))
    [P.Normal] [IsElementaryAbelian 3 P] (hP : Nat.card P = 9)
    (hXi : ∀ X ∈ Chapter1.Xi G T, ¬ X ≤ centralizer (Z : Set G)) :
    ∃ B : Subgroup (CoreQuotient (centralizer (Z : Set G))), B ≤ P ∧
      Nat.card B = 3 ∧ image (centralizer (Z : Set G)) T ≤ normalizer (B : Set _) := by
  classical
  by_contra hnone
  let H := centralizer (Z : Set G)
  let X := lift H P
  have hXH : X ≤ H := lift_le H P
  have hn : T ≤ normalizer (X : Set G) :=
    lift_normalized H T hTC P (by rw [normalizer_eq_top_iff.mpr (inferInstance : P.Normal)]; exact le_top)
  have hZcore : Z ≤ (X ⊔ T).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hZtwo (hZT.trans le_sup_right)
      ((sup_le hXH hTC).trans (Subgroup.centralizer_le_normalizer _))
  have hH : X ⊔ T ∈ Chapter1.H G := by
    intro hbot
    exact hZne (le_bot_iff.mp (hbot ▸ hZcore))
  obtain ⟨e₀, _⟩ := nine_lift_quotient H P hP
  let : IsElementaryAbelian 3 (Chapter1.XiQuotient X) :=
    IsElementaryAbelian.of_surjective e₀.symm.toMonoidHom e₀.symm.surjective
  obtain ⟨e, he⟩ := nine_lift_frattini_quotient H P hP
  let : IsElementaryAbelian 3 (Chapter1.XiFrattiniQuotient X) :=
    IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  apply hXi X (show Chapter1.XiMember T X from ?_) hXH
  refine ⟨lift_perfect H P, hn, hH,
    ⟨3, Nat.prime_three, by decide, Or.inl ⟨inferInstance, ?_⟩⟩, ?_⟩
  · exact (Nat.card_congr e₀.toEquiv).trans hP
  · intro A hA
    by_cases hAb : A = ⊥
    · exact Or.inl hAb
    by_cases hAt : A = ⊤
    · exact Or.inr hAt
    have hA3 : Nat.card A = 3 :=
      cubic_card_of_proper ((Nat.card_congr e.toEquiv).trans hP) A hAb hAt
    let B := (A.map e.toMonoidHom).map P.subtype
    have hB3 : Nat.card B = 3 :=
      (Subgroup.card_map_of_injective P.subtype_injective).trans
        ((Subgroup.card_map_of_injective e.injective).trans hA3)
    have hBN : image H T ≤ normalizer (B : Set (CoreQuotient H)) := by
      change (T.subgroupOf H).map (quotientMap H) ≤ normalizer (B : Set _)
      apply le_normalizer_iff.mpr
      rintro q ⟨t, ht, rfl⟩ b ⟨p, ⟨a, ha, rfl⟩, rfl⟩
      have hmem := mem_map_of_mem P.subtype
        (mem_map_of_mem e.toMonoidHom (hA ⟨(t : G), ht⟩ a ha))
      change (e (Chapter1.xiFrattiniAction T (lift H P) hn ⟨(t : G), ht⟩ a) : CoreQuotient H) ∈ B at hmem
      rw [nine_lift_action_compatible T H hTC P hn e he ⟨(t : G), ht⟩ a] at hmem
      exact hmem
    exact (hnone ⟨B, map_subtype_le _, hB3, hBN⟩).elim

/-- Lemma 15.4.9 from its genuine preceding source reductions. The normal
elementary subgroup and invariant cubic line are both constructed internally. -/
theorem normalCentralizerXi_nonempty_of_earlier_source
    (T : Sylow 2 G) (Z : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G))
    (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G)) (hZne : Z ≠ ⊥)
    (hne : centralizer (Z : Set G) ≠ (T : Subgroup G))
    (hs : Group.IsSolvable (centralizer (Z : Set G)))
    (hp : ∀ p : ℕ, p.Prime → p ∣ Nat.card (centralizer (Z : Set G)) → p = 2 ∨ p = 3)
    (hr : primeRank 3 (centralizer (Z : Set G)) ≤ 2)
    (hXi : ∀ X ∈ Chapter1.Xi G (T : Subgroup G), ¬ X ≤ centralizer (Z : Set G)) :
    (NormalCentralizerXi (T : Subgroup G) Z).Nonempty := by
  let H := centralizer (Z : Set G)
  let P := omegaCandidate H
  let : P.Normal := omegaCandidate_normal H
  let : IsElementaryAbelian 3 P := omegaCandidate_elementary H
  have hZtwo : IsPGroup 2 Z := T.isPGroup'.of_injective
    (Subgroup.inclusion hZT) (Subgroup.inclusion_injective hZT)
  rcases omegaCandidate_card T H hTC hne hs hp hr with hP | hP
  · exact ⟨lift H P, normalCentralizerXi_of_normal_cubic T Z hZT hTC hZne hZtwo P hP inferInstance⟩
  · obtain ⟨B, hBP, hB3, hBT⟩ := invariant_cubic_of_no_upper_Xi T Z hZT hTC hZne hZtwo P hP hXi
    exact normalCentralizerXi_nonempty_of_ternary_section T Z hZT hTC hZne P (Or.inr hP) B hBP hB3 hBT

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SourceCubic
