module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.TwoCore
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics

/-!
# Excluding outer-two and alternating rows in the split domain

An actual outside odd-prime actor contradicts the rank-two absorption theorem
when the component's intrinsic two-core quotient has p-prime center and a
two-group outer automorphism group. At three, the actual alternating carriers
and the exceptional triple covers of A₆ and A₇ absorb every cubic actor.
Transport through H/O₂(H) therefore excludes those full marked models in
the original split extension, preserving the covering centers.

These exclusions feed the remaining-case reduction for normal split-prime
A.3.18; no assertion is made here about the other source covers or mixed actors.
Source: Aschbacher–Smith A.3.18, printed pp.51–53.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02.LocalModels
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
variable {H : Type*} [Group H] [Finite H]

theorem outer_not_twoGroup
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) :
    ¬ IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)) := by
  let : Fact p.Prime := ⟨hp⟩
  intro hout
  exact haK (CComponentPrimeRank.prime_actor_mem_of_twoCore_full_rank K hK hz hr
    (hH.stronglyQuasithin p hp ho) ho hout a ha)

theorem not_alternating_cover
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) :
    ¬ (IsAlternatingCover (K ⧸ pCore 2 K) 6 ∨
      IsAlternatingCover (K ⧸ pCore 2 K) 7) := by
  intro hm
  have ha' := twoCore_actor Nat.prime_three (by decide) a ha haK
  exact ha'.2 (AlternatingCubics.cubic_mem_of_alternating_cover_component
    (twoCore_isComponent hK) (twoCoreComponentEquiv hK) hm
    ((twoCore_sqtk hH).stronglyQuasithin 3 Nat.prime_three (by decide)) ha'.1)

theorem not_alternating_model
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)] {n : ℕ} (hn : 6 ≤ n)
    (a : H) (ha : orderOf a = 3) (haK : a ∉ K) :
    ¬ IsAlternating (K ⧸ pCore 2 K) n := by
  rintro ⟨e⟩
  have ha' := twoCore_actor Nat.prime_three (by decide) a ha haK
  exact ha'.2 (AlternatingCubics.cubic_mem_of_alternating_component (twoCore_isComponent hK)
    hn ⟨(twoCoreComponentEquiv hK).trans e⟩
    ((twoCore_sqtk hH).stronglyQuasithin 3 Nat.prime_three (by decide)) ha'.1)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
