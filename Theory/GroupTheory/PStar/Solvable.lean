module

public import Theory.GroupTheory.PStar.Basic
public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.GroupTheory.CoprimeQuotientNormalizer

/-!
# Solvable p-star groups have order prime to p

Pass to the quotient by the prime-complement core. Its Fitting subgroup is
the p-core and is central by the p-star condition. Fitting self-centralization
makes the quotient a p-group; p-perfectness makes it trivial.

Source: the solvable specialization of GLS II, Chapter B, Lemma 5.2(v).
In particular a solvable two-star group has odd order.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {p : ℕ} {G : Type*} [Group G] [Finite G] [Fact p.Prime]

/-- A solvable p-star group has order prime to p. -/
theorem IsPStar.coprime_card_of_solvable (hG : IsPStar p G) [Group.IsSolvable G] :
    Nat.Coprime p (Nat.card G) := by
  let O := pPrimeCore p G
  let Q := G ⧸ O
  have hQ : IsPStar p Q := hG.quotient O
  have hc : pCore p Q ≤ center Q := hQ.normal_pSubgroup_le_center _ pCore_isPGroup
  have hfit : fittingSubgroup Q = pCore p Q :=
    Fitting_eq_pcore Q p (pPrimeCore_quotient_pPrimeCore_eq_bot p)
  have hctop : centralizer (pCore p Q : Set Q) = ⊤ :=
    centralizer_eq_top_iff_subset.mpr hc
  have hptop : pCore p Q = ⊤ := by
    apply top_unique
    rw [← hctop, ← hfit]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance
  have hpQ : IsPGroup p Q := by
    have h : IsPGroup p (⊤ : Subgroup Q) := hptop ▸ pCore_isPGroup
    exact h.of_equiv Subgroup.topEquiv
  let : Subsingleton Q := hQ.subsingleton_of_isPGroup hpQ
  have hO : O = ⊤ := by
    apply top_unique
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim (QuotientGroup.mk' O x) 1)
  have hcop : Nat.Coprime p (Nat.card O) := pPrimeCore_coprime_card
  simpa [hO] using hcop

/-- The prime-two source specialization. -/
theorem IsPStar.odd_card_of_solvable (hG : IsPStar 2 G) [Group.IsSolvable G] :
    Odd (Nat.card G) :=
  Nat.coprime_two_left.mp hG.coprime_card_of_solvable
end Theory.GroupTheory
