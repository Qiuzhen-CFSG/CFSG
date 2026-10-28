module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ActionBounds
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Binary
public import Theory.SpecificGroups.SU3.NoncubicFieldActors

/-!
# Noncubic binary unitary actors on the original split extension

The actual unitary component theorem forces a prime of rank two to divide
q+1. Its two norm-one torus directions survive in the coefficient fixed
subgroup, so an outside noncubic field actor would force prime rank three.
Transport the resulting absorption through the literal two-core quotient;
the original outside element then contradicts absorption. The quadratic
coefficient field has order q² throughout.

Source: Aschbacher–Smith A.3.18, printed pp.51–53; the intrinsic unitary
fixed-subfield proof is in SU3.NoncubicFieldActors.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupAction.ComponentRankAction
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

/-- Eliminate every binary PSU₃ row at an odd prime other than three. -/
theorem not_noncubic_unitary_twoCore_model
    {H : Type*} [Group H] [Finite H] (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3)
    (hr : 1 < primeRank p K)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) 3 (2 ^ n))
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : (twoCoreComponent K).Normal := twoCore_normal K
  let := (twoCore_isComponent hK).2
  have hz' : Nat.Coprime p (Nat.card (center (twoCoreComponent K))) := by
    rwa [Nat.card_congr (centerCongr (twoCoreComponentEquiv hK)).toEquiv]
  have hr' : 2 ≤ primeRank p (twoCoreComponent K) := by rw [twoCore_rank hK ho]; omega
  have ha' := twoCore_actor hp ho a ha haK
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ :=
    hm.of_mulEquiv (centralQuotientEquiv (twoCoreComponentEquiv hK))
  have hpgt : 3 < p := by
    have hp2 := hp.two_le
    have hodd := Nat.odd_iff.mp ho
    omega
  have hh := BenderSuzuki.MatrixGroups.HermitianForm.NoncubicFieldActors.component_eq_primeClosure_and_residual
    J hn hF hconj (twoCore_isComponent hK) hpgt hz' hr'
    ((twoCore_sqtk hH).stronglyQuasithin p hp ho) e
  apply ha'.2
  rw [hh.1]
  exact subset_closure ha'.1

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
