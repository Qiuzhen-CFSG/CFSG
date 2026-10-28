module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
public import Theory.GroupTheory.CComponent.TwoCorePrimeActors

/-!
# The literal two-core reduction for normal split-prime A.3.18

For a normal C-component K with quasisimple K/O₂(K), its image in
H/O₂(H) is an ordinary normal component with the same odd prime ranks.
An actual outside element of odd prime order remains outside and keeps its
order and generation property. The equivalence retains the whole intrinsic
two-core quotient; no centrality of O₂(K) is assumed.

The outside actor excludes the residual equality and, at three, the theta
equality in A.3.18. The remaining projective and full split-cover alternatives
are retained verbatim. This is a reduction, not their classification.
Source: Aschbacher–Smith A.3.18, printed pp.51–53.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
variable {H : Type*} [Group H] [Finite H]

abbrev TwoCoreQuotient (H : Type*) [Group H] := H ⧸ pCore 2 H

abbrev twoCoreComponent (K : Subgroup H) : Subgroup (TwoCoreQuotient H) :=
  K.map (QuotientGroup.mk' (pCore 2 H))

def twoCoreComponentEquiv {K : Subgroup H} (hK : K.IsCComponent) :
    twoCoreComponent K ≃* K ⧸ pCore 2 K :=
  (cComponentTwoCoreQuotientEquiv hK).symm

theorem twoCore_sqtk (hH : IsSQTK KnownSimple.IsKnownSimple H) :
    IsSQTK KnownSimple.IsKnownSimple (TwoCoreQuotient H) := by
  refine ⟨?_, hH.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hH.stronglyQuasithin p hp ho)

theorem twoCore_isComponent {K : Subgroup H} (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)] :
    IsComponent (TwoCoreQuotient H) (twoCoreComponent K) :=
  CComponentPrimeRank.twoCore_image_isComponent hK

omit [Finite H] in
theorem twoCore_normal (K : Subgroup H) [K.Normal] : (twoCoreComponent K).Normal :=
  (inferInstance : K.Normal).map _ (QuotientGroup.mk'_surjective _)

theorem twoCore_rank {K : Subgroup H} (hK : K.IsCComponent)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (twoCoreComponent K) = primeRank p K := by
  rw [primeRank_congr p (twoCoreComponentEquiv hK),
    primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup]

theorem twoCore_actor {K : Subgroup H} [K.Normal] {p : ℕ} (hp : p.Prime)
    (ho : Odd p) (a : H) (ha : orderOf a = p) (haK : a ∉ K) :
    orderOf (QuotientGroup.mk' (pCore 2 H) a) = p ∧
      QuotientGroup.mk' (pCore 2 H) a ∉ twoCoreComponent K := by
  let : Fact p.Prime := ⟨hp⟩
  have hn : QuotientGroup.mk' (pCore 2 H) a ∉ twoCoreComponent K := fun hi =>
    haK (CComponentPrimeRank.prime_actor_mem_of_twoGroup_image _ _ pCore_isPGroup ho a ha hi)
  refine ⟨?_, hn⟩
  apply orderOf_eq_prime
  · rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  · exact fun he => hn (he ▸ (twoCoreComponent K).one_mem)

omit [Finite H] in
theorem twoCore_join {K : Subgroup H} (a : H) (hgen : K ⊔ zpowers a = ⊤) :
    twoCoreComponent K ⊔ zpowers (QuotientGroup.mk' (pCore 2 H) a) = ⊤ := by
  have he := congrArg (Subgroup.map (QuotientGroup.mk' (pCore 2 H))) hgen
  simpa only [Subgroup.map_sup, MonoidHom.map_zpowers,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top_of_surjective _
      (QuotientGroup.mk'_surjective _)] using he

omit [Finite H] in
theorem ne_prime_closures {K : Subgroup H} {p : ℕ}
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) :
    K ≠ closure {x : H | orderOf x = p} ∧ K ≠ primeToResidual p H := by
  constructor
  · intro he
    exact haK (he ▸ subset_closure ha)
  · intro he
    apply haK
    rw [he]
    apply mem_primeToResidual_of_pow (n := 1)
    simpa only [pow_one, ← ha] using pow_orderOf_eq_one a

omit [Finite H] in
theorem alternatives_iff {K : Subgroup H} {p : ℕ}
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) :
    Alternatives p K ↔ ProjectiveAlternative p K ∨
      (p = 3 ∧ CoverAlternative (starComponent p K) ∧
        SplitDiagonalAlternative (starComponent p K)) := by
  have hn := ne_prime_closures a ha haK
  constructor
  · rintro (he | hp | ⟨hp, hc, ht | hs⟩)
    · exact (hn.2 he).elim
    · exact Or.inl hp
    · exact ((ne_prime_closures a (ha.trans hp) haK).1 ht).elim
    · exact Or.inr ⟨hp, hc, hs⟩
  · rintro (hp | ⟨hp, hc, hs⟩)
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr ⟨hp, hc, Or.inr hs⟩)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
