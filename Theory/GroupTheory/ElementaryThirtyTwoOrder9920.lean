module
public import Theory.GroupTheory.ElementaryThirtyTwoNormalThirtyOne
public import Theory.GroupTheory.ElementaryThirtyTwoThirtyOneNormalizer

/-!
# Excluding a solvable automorphism subgroup of order 9920

A solvable subgroup K of the automorphism group of an elementary abelian
two-group E of order thirty-two cannot have order 9920 = 2^6 * 5 * 31.
The result concerns the actual subgroup of automorphisms and requires no
extra action, faithfulness, or subgroup-model hypothesis.

The order-9920 Fitting argument supplies a normal Sylow thirty-one subgroup
of K. Its image in Aut(E) still has order thirty-one, and K lies in the
normalizer of this image. The imported odd-normalizer theorem makes that
normalizer odd, hence makes its subgroup K odd, contrary to order 9920.

This is the solvable specialization of the order-thirty-one exclusion used
in Parrott, *A characterization of the Tits' simple group* (1972), Lemma 2,
printed p.673. It assembles the two independent normal-subgroup and
normalizer bounds for the local-solvability recognition argument.
-/

/-- No solvable subgroup of Aut(E) has order 9920 when E is elementary of order32. -/
public theorem not_card9920_of_solvable_aut32
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (K : Subgroup (MulAut E))
    (hsolv : Group.IsSolvable K) : Nat.card K ≠ 9920 := by
  intro hK
  obtain ⟨P, hP, hnormal⟩ := normal_thirtyone_of_solvable_aut32_card9920 hE K hsolv hK
  let : (P : Subgroup K).Normal := hnormal
  let A : Subgroup (MulAut E) := (P : Subgroup K).map K.subtype
  have hA : Nat.card A = 31 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hP
  have hle : K ≤ Subgroup.normalizer (A : Set (MulAut E)) := by
    have hmap := (P : Subgroup K).le_normalizer_map K.subtype
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, K.range_subtype]
      using hmap
  have hodd : Odd (Nat.card K) :=
    (odd_card_normalizer_of_elementary_thirtytwo_thirtyone E hE A hA).of_dvd_nat
      (Subgroup.card_dvd_of_le hle)
  rw [hK] at hodd
  exact (by decide : ¬ Odd 9920) hodd
