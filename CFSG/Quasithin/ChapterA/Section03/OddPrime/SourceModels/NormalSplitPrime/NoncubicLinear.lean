module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ActionBounds
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Binary
public import Theory.SpecificGroups.PSL3.BinaryNoncubicComponents

/-!
# The noncubic binary linear exclusion on the original split domain

The proved binary PSL₃ theorem first forces a split torus prime from rank
two, then constructs the fixed elementary p² subgroup for field actors.
Consequently the original component contains every element of order p > 3.
Apply it to the genuine two-core component and the original outside actor;
its membership in the prime-generated subgroup gives a contradiction.

Source: Aschbacher–Smith A.3.18, printed pp.51–53. The marking is on the
actual intrinsic central quotient, with no extra torus or action premise.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

/-- Eliminate every binary PSL₃ row at an odd prime other than three. -/
theorem not_noncubic_linear_twoCore_model
    {H : Type*} [Group H] [Finite H] (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3)
    (hr : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) 3 (2 ^ n))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  have hz' : Nat.Coprime p (Nat.card (center (twoCoreComponent K))) := by
    rwa [Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
  have hr' : 2 ≤ primeRank p (twoCoreComponent K) := by rw [twoCore_rank hK ho]; omega
  have ha' := twoCore_actor hp ho a ha haK
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ :=
    hm.of_mulEquiv (centralQuotientEquiv (twoCoreComponentEquiv hK))
  have hpgt : 3 < p := by
    have hp2 := hp.two_le
    have hodd := Nat.odd_iff.mp ho
    omega
  have hh := Matrix.PSL3.binary_noncubic_component_eq_primeClosure_and_residual
    (twoCore_isComponent hK) hp hpgt hn hF hz' hr'
    ((twoCore_sqtk hH).stronglyQuasithin p hp ho) e
  apply ha'.2
  rw [hh.1]
  exact subset_closure ha'.1

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
