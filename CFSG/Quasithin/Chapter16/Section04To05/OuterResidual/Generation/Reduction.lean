module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Basic
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Residual generation criteria for the ordinary branch

One odd prime with rank greater than one in L suffices when its prime-to-p
residual generates D. For a two-perfect D with normal two-subgroup and simple
quotient, it is enough for that prime to divide the quotient order. The source
residual Lᵣ is automatically two-perfect; that condition is proved, not added
as a model assumption. The ordinary centralizer identities then transfer Lᵣ
into the conjugate component.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the subgroup
Λ(Lᵣ) in the proof of Lemma 16.4.8, printed pp.1187–1188. Model coverage and
its prime-rank calculations are separate obligations.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual
open Subgroup Theory.GroupTheory ComponentTransfer
variable {G : Type*} [Group G]

/-- A single admissible prime can generate the whole rank-residual span. -/
theorem rankResidualSpan_eq_of_primeToResidual_top {L D : Subgroup G} {p : ℕ}
    (hp : p ∈ residualPrimes L) (hD : primeToResidual p D = ⊤) :
    rankResidualSpan L D = D := by
  apply le_antisymm (rankResidualSpan_le L D)
  have hle : (primeToResidual p D).map D.subtype ≤ rankResidualSpan L D :=
    le_iSup_of_le p (le_iSup_of_le hp le_rfl)
  simpa only [hD, ← MonoidHom.range_eq_map, range_subtype] using hle

/-- A simple quotient above a normal two-subgroup supplies the generating prime. -/
theorem rankResidualSpan_eq_of_simple_quotient [Finite G]
    {L D : Subgroup G} {p : ℕ} (hp : p ∈ residualPrimes L)
    (Q : Subgroup D) [Q.Normal] [IsSimpleGroup (D ⧸ Q)]
    (hQ : IsPGroup 2 Q) (hD : IsPPerfect 2 D)
    (hd : p ∣ Nat.card (D ⧸ Q)) : rankResidualSpan L D = D := by
  let : Fact p.Prime := ⟨hp.1⟩
  exact rankResidualSpan_eq_of_primeToResidual_top hp
    (primeToResidual_eq_top_of_simple_quotient p 2 Q hQ hD hd)

/-- The actual two-residual supplies its own two-perfectness hypothesis. -/
theorem involutionResidual_rankSpan_eq_of_simple_quotient [Finite G]
    {L : Subgroup G} {r : G} {p : ℕ} (hp : p ∈ residualPrimes L)
    (Q : Subgroup (involutionResidual L r)) [Q.Normal]
    [IsSimpleGroup (involutionResidual L r ⧸ Q)] (hQ : IsPGroup 2 Q)
    (hd : p ∣ Nat.card (involutionResidual L r ⧸ Q)) :
    rankResidualSpan L (involutionResidual L r) = involutionResidual L r := by
  exact rankResidualSpan_eq_of_simple_quotient hp Q hQ
    (isPPerfect_embedded_pResidual 2 (centralizerIn L r)) hd

/-- Transfer after the model calculation has established residual generation. -/
theorem involutionResidual_le_conjugate_of_rankSpan_eq [Finite G]
    {L : Subgroup G} {g r : G}
    (hspan : rankResidualSpan L (involutionResidual L r) = involutionResidual L r)
    (hres : ∀ p ∈ residualPrimes (L.conjBy g),
      (primeToResidual p (involutionCentralizer r)).map
        (involutionCentralizer r).subtype = L.conjBy g) :
    involutionResidual L r ≤ L.conjBy g := by
  rw [← hspan]
  exact rankResidualSpan_le_of_centralizer_residuals
    ((involutionResidual_le L r).trans inf_le_right) hres

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual
