module

public import Theory.Mathieu.M22.TripleCover
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.Reduction

/-!
# Central scalars detect outer automorphisms of the triple Mathieu cover

The concrete M₂₂ design action bounds the outer group by two. For its perfect
triple cover, central descent gives the same bound. Inner automorphisms fix the
central scalar, whereas the certified outer matrix generator moves it. Comparing
indices therefore identifies its stabilizer with the inner automorphism group.
Every other automorphism inverts that scalar.

The argument concerns automorphisms of the actual cover and is independent of
any chosen module or degree. It supplies the outer-displacement step in the M₂₂
case of Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
pp.15–16, as used by Aschbacher–Smith, Chapter K, printed pp.451 and 457.
The matrix identities and their original attribution are imported from the
native triple-cover construction.
-/

public section

open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace Sporadic.Mathieu.M22TripleCover.ScalarAutomorphisms

/-- The actual outer group of the simple quotient has order dividing two. -/
theorem m22_outer_card_dvd_two : Nat.card (MulAut.Outer M22) ∣ 2 := by
  let N := M22.subgroupOf m22DesignAut
  let : N.Normal := M22_normal_in_m22DesignAut
  have hle : N ≤ (MulAut.innerSubgroup M22).comap m22DesignAutToAut := by
    intro g hg
    refine ⟨⟨g.val, hg⟩, ?_⟩
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [m22DesignAutToAut_apply_perm]
    rfl
  let q : (m22DesignAut ⧸ N) →* MulAut.Outer M22 :=
    QuotientGroup.map N (MulAut.innerSubgroup M22) m22DesignAutToAut hle
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup M22) x
    obtain ⟨g, rfl⟩ := m22DesignAutToAut_surjective a
    exact ⟨QuotientGroup.mk' N g, rfl⟩
  have htwo : Nat.card (m22DesignAut ⧸ N) = 2 := by
    rw [← N.index_eq_card]
    have heq : N = m22EvenDesignAut := by
      ext g
      simp [N, M22, m22EvenDesignAut]
    rw [heq, m22EvenDesignAut_index]
  exact htwo ▸ card_dvd_of_surjective q hq

private lemma inner_of_fixes_of_outer_card_dvd_two
    {D : Type*} [Group D] [Finite D] (z : D) (hz : z ∈ center D)
    (houter : Nat.card (MulAut.Outer D) ∣ 2)
    (hmove : ∃ c : MulAut D, c z ≠ z)
    (a : MulAut D) (ha : a z = z) : ∃ x : D, a = MulAut.conj x := by
  let I := MulAut.innerSubgroup D
  let K := MulAction.stabilizer (MulAut D) z
  have hIK : I ≤ K := by
    rintro _ ⟨x, rfl⟩
    change x * z * x⁻¹ = z
    rw [mem_center_iff.mp hz x, mul_assoc, mul_inv_cancel, mul_one]
  have hK : K ≠ ⊤ := by
    intro h
    obtain ⟨c, hc⟩ := hmove
    exact hc (show c ∈ K from h ▸ mem_top c)
  have hi : I.index ∣ 2 := by
    rw [Subgroup.index_eq_card]
    exact houter
  have hk : K.index = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp ((index_dvd_of_le hIK).trans hi)).resolve_left
      (fun h => hK (Subgroup.index_eq_one.mp h))
  have hi2 : I.index = 2 := Nat.dvd_antisymm hi (hk ▸ index_dvd_of_le hIK)
  have he : I = K := Subgroup.eq_of_le_of_card_ge hIK (by
    have hI := I.card_mul_index
    have hK := K.card_mul_index
    rw [hi2] at hI
    rw [hk] at hK
    omega)
  have haK : a ∈ K := ha
  obtain ⟨x, hx⟩ := (he.symm ▸ haK : a ∈ I)
  exact ⟨x, hx.symm⟩

private lemma exists_moves_scalar : ∃ c : MulAut M22TripleCover, c scalar ≠ scalar := by
  let c := Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.derivedConjugation
    ⟨_, Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.unitC_mem_actionGroup⟩
  refine ⟨c, ?_⟩
  intro hc
  have hinv : c scalar = scalar ^ 2 := by
    apply Subtype.ext
    exact Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.unitC_conj_scalarUnit
  rw [hinv] at hc
  have he : scalar = 1 := by
    apply mul_left_cancel (a := scalar)
    simpa only [pow_two, mul_one] using hc
  have ho := scalar_order
  simp [he] at ho

/-- An automorphism fixing the distinguished central scalar is inner. -/
theorem inner_of_fixes_scalar (a : MulAut M22TripleCover) (ha : a scalar = scalar) :
    ∃ x : M22TripleCover, a = MulAut.conj x := by
  apply inner_of_fixes_of_outer_card_dvd_two scalar scalar_mem_center _ exists_moves_scalar a ha
  exact (card_dvd_of_injective (MulAut.centralQuotientOuter centralQuotientEquiv)
    (MulAut.centralQuotientOuter_injective centralQuotientEquiv)).trans m22_outer_card_dvd_two

/-- Every automorphism fixes or inverts the actual central scalar. -/
theorem scalar_eq_or_inv (a : MulAut M22TripleCover) :
    a scalar = scalar ∨ a scalar = scalar⁻¹ := by
  have hc : a scalar ∈ center M22TripleCover := by
    exact (Subgroup.characteristic_iff_map_eq.mp (inferInstance : (center M22TripleCover).Characteristic) a ▸
      Subgroup.mem_map_of_mem a.toMonoidHom scalar_mem_center)
  rcases Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.mem_center_derivedGroup_iff
    (a scalar) |>.mp hc with h | h | h
  · have he : scalar = 1 := a.injective (h.trans a.map_one.symm)
    have ho := scalar_order
    simp [he] at ho
  · exact Or.inl h
  · right
    rw [h]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.coreScalar_pow_three
end Sporadic.Mathieu.M22TripleCover.ScalarAutomorphisms
