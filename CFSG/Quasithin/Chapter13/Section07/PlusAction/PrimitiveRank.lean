module

public import CFSG.Quasithin.Chapter13.Section07.PlusAction.PrimitiveSource
public import Theory.GroupTheory.PrimeRankElementary

/-!
# The source rank bound for primitive odd kernels

The original flag line has order two and H centralizes it. Thus H embeds
in the actual involution centralizer, whose odd-prime ranks are at most
two by the ambient quasithin hypothesis. Odd-prime rank passes through
the intrinsic two-core quotient. Consequently a nonzero elementary
abelian primitive image has order p or p², as in the source selection.

Source: Aschbacher--Smith 13.7.4(1), printed p.936.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The source H is strongly quasithin by its containment in the original
flag involution centralizer. -/
theorem source_H_stronglyQuasithin
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    IsStronglyQuasithin H := by
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp d.line_card
  have hzorder : orderOf z = 2 := orderOf_eq_prime
    (d.line_card ▸ (pow_card_eq_one' (x := z))) hz
  have hzG : orderOf (z : G) = 2 := (orderOf_coe z).trans hzorder
  have hHC : H ≤ centralizer ({(z : G)} : Set G) :=
    h.H_centralizes.trans (centralizer_le (Set.singleton_subset_iff.mpr z.property))
  exact (d.counterexample.qtke.involution_centralizer_sqtk hzG).stronglyQuasithin.of_injective
    (inclusion hHC) (inclusion_injective hHC)

/-- Every intrinsic two-core quotient of a subgroup of H has the same
source upper bound on odd-prime rank. -/
theorem source_subgroup_quotient_odd_rank
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (J : Subgroup H) {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p (J ⧸ pCore 2 J) ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 J) pCore_isPGroup).trans
    ((primeRank_subgroup_le p J).trans (source_H_stronglyQuasithin d h p hp ho))

/-- The odd-chief alternative in primitive selection has precisely the
source dimensions one or two. -/
theorem source_primitive_odd_order
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    {J : Subgroup H} (hJ : IsPPerfect 2 J) (hne : J ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hE : IsElementaryAbelian p (J ⧸ pCore 2 J)) :
    Nat.card (J ⧸ pCore 2 J) = p ∨ Nat.card (J ⧸ pCore 2 J) = p ^ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsElementaryAbelian p (J ⧸ pCore 2 J) := hE
  let Q := J ⧸ pCore 2 J
  have hnQ : Nontrivial Q := by
    apply QuotientGroup.nontrivial_iff.mpr
    intro he
    have htop : IsPGroup 2 (⊤ : Subgroup J) :=
      he ▸ (pCore_isPGroup (p := 2) (G := J))
    have hgroup : IsPGroup 2 J := htop.of_equiv Subgroup.topEquiv
    have hb : (⊥ : Subgroup J) = ⊤ := hJ ⊥ inferInstance (hgroup.to_quotient ⊥)
    have hz : J = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      have hxone : (⟨x, hx⟩ : J) ∈ (⊥ : Subgroup J) := hb.symm ▸ mem_top _
      exact congrArg Subtype.val hxone
    exact hne hz
  let : Nontrivial Q := hnQ
  have hbound : Nat.card Q ≤ p ^ 2 := by
    have ht := (primeRank_le_iff_elementary_card_le Q).mp
      (source_subgroup_quotient_odd_rank d h J hp ho) (⊤ : Subgroup Q)
    let : IsElementaryAbelian p (⊤ : Subgroup Q) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup Q).subtype
        (⊤ : Subgroup Q).subtype_injective
    simpa using ht inferInstance
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p Q).exists_card_eq
  have hnle : n ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hn ▸ hbound)
  have hnpos : 0 < n := by
    by_contra hn0
    have hz : n = 0 := by omega
    have hc : Nat.card Q = 1 := by simpa [hz] using hn
    have hs : Subsingleton Q := Nat.card_eq_one_iff_unique.mp hc |>.1
    exact (not_subsingleton Q) hs
  have : n = 1 ∨ n = 2 := by omega
  rcases this with he | he
  · exact Or.inl (by simpa [he] using hn)
  · exact Or.inr (by simpa [he] using hn)

end CFSG.Quasithin.Chapter13.Section07.PlusAction
