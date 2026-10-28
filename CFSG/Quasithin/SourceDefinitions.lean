module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Source specifications of the quasithin hypotheses

These equivalences connect the established QTKE definitions to the three
conditions printed in Aschbacher–Smith, The Classification of Quasithin Groups,
Hypothesis 0.1.1, pp.3–4 (repeated pp.481–483).

The QT condition bounds elementary abelian p-subgroups in every maximal
2-local for every odd prime p. The prime-rank comparison is proved in the
imported reusable module. The K condition tests actual simple quotients of
proper subgroups; flattening nested subgroups proves its equivalence with
the established section formulation. This uses the source's explicit
convention: composition factors of every subgroup, not just those of the
ambient group. Finally, E is relative to maximal 2-locals containing one
fixed Sylow subgroup; the existing conjugacy theorem makes the choice
irrelevant.

The group class remains a parameter with proved isomorphism invariance.
The main theorem instantiates it with KnownSimple.IsKnownSimple, the full
catalogue. No classification result or model certification is assumed in
these comparisons, and no existing core definition is changed.
-/

public section

namespace CFSG.Quasithin

universe u

/-- Proper-K may be checked on simple quotients of proper subgroups directly. -/
theorem hasProperKSubgroups_iff_proper_simple_quotients {K : GroupClass.{u}} (hK : K.IsIsoInvariant)
    (G : Type u) [Group G] :
    HasProperKSubgroups K G ↔
      ∀ (U : Subgroup G), U ≠ ⊤ → ∀ (N : Subgroup U) [N.Normal],
        IsSimpleGroup (U ⧸ N) → K (U ⧸ N) := by
  constructor
  · intro h U hU N _ hs
    let : IsSimpleGroup (U ⧸ N) := hs
    exact ((h U hU).quotient N).mem
  · intro h U hU S _ hs V f hf
    let : IsSimpleGroup S := hs
    let W := V.map U.subtype
    have hW : W ≠ ⊤ := ne_top_of_le_ne_top hU (Subgroup.map_subtype_le V)
    let e := Subgroup.equivMapOfInjective V U.subtype U.subtype_injective
    let g : W →* S := f.comp e.symm.toMonoidHom
    have hg : Function.Surjective g := hf.comp e.symm.surjective
    let q := QuotientGroup.quotientKerEquivOfSurjective g hg
    exact (hK _ _ q).mp (h W hW g.ker q.isSimpleGroup)

/-- Strong quasithinness in the source elementary-abelian formulation. -/
theorem isStronglyQuasithin_iff_elementary_card_bounds (G : Type*) [Group G] [Finite G] :
    IsStronglyQuasithin G ↔ ∀ p : ℕ, p.Prime → Odd p →
      ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A ≤ p ^ 2 := by
  constructor
  · intro h p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_le_iff_elementary_card_le G).mp (h p hp ho)
  · intro h p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_le_iff_elementary_card_le G).mpr (h p hp ho)

/-- Quasithinness in the source maximal-two-local formulation. -/
theorem isQuasithin_iff_elementary_twoLocal_bounds (G : Type*) [Group G] [Finite G] :
    IsQuasithin G ↔ ∀ M : Subgroup G, IsMaximalTwoLocal M →
      ∀ p : ℕ, p.Prime → Odd p → ∀ A : Subgroup M,
        IsElementaryAbelian p A → Nat.card A ≤ p ^ 2 := by
  rw [Theory.GroupTheory.isQuasithin_iff_maximalTwoLocal]
  constructor
  · intro h M hM p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_le_iff_elementary_card_le M).mp (h M hM p hp ho)
  · intro h M hM p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_le_iff_elementary_card_le M).mpr (h M hM p hp ho)

/-- Hypothesis 0.1.1, using elementary ranks, actual simple quotients, and a fixed Sylow subgroup. -/
theorem isQTKE_iff_source_conditions {K : GroupClass.{u}} (hK : K.IsIsoInvariant)
    (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) :
    IsQTKE K G ↔
      (∀ M : Subgroup G, IsMaximalTwoLocal M →
        ∀ p : ℕ, p.Prime → Odd p → ∀ A : Subgroup M,
          IsElementaryAbelian p A → Nat.card A ≤ p ^ 2) ∧
      (∀ U : Subgroup G, U ≠ ⊤ → ∀ (N : Subgroup U) [N.Normal],
        IsSimpleGroup (U ⧸ N) → K (U ⧸ N)) ∧
      (∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
        Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M) := by
  rw [isQTKE_iff, isQuasithin_iff_elementary_twoLocal_bounds, hasProperKSubgroups_iff_proper_simple_quotients hK,
    isEvenCharacteristic_iff_at T]
  rfl

end CFSG.Quasithin
