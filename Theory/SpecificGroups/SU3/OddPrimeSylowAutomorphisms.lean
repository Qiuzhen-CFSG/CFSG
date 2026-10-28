module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.GraphComparison
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.OrthogonalOrder
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Odd-prime PSU₃ involutions fixing subgroups of order 32

The fixed subgroup of a normalized graph involution embeds in the actual
ternary special orthogonal group over the fixed field. When `p ≡ 3 mod 8`,
`p(p² - 1)` is eight modulo sixteen and cannot be divisible by 32. Thus a
subgroup of order 32 cannot be fixed by an outer involution. Every outer
involution is transported to entrywise conjugation on an antidiagonal model,
and the orthogonal group has order `p(p² - 1)`.

The conditional reduction remains available separately. The final theorem
`inner_of_involutive_fixing_order_thirtyTwo` discharges its two structural
premises using `NormalizedOuterInvolutions` and `OrthogonalOrder`. It retains
the prime, congruence, matrix-field and fixed-field hypotheses, and uses only
the source-supplied simplicity of the projective group. Normalization uses
actual multiplicative equivalences and preserves the stored field involution;
arbitrary-automorphism coverage includes `p = 3`. The subgroup of order 32
need not be supplied with any Sylow or geometry hypothesis.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.6.18(10)–(11), printed pp.309–310, and the component
argument of 15.4.18, printed pp.1162–1163. The further four-group fixed-action
obstruction and SU₃ comparison are assembled by the Chapter 15 consumer.
-/

namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
universe u
variable {E : Type u} [Field E] (J : HermitianForm 3 E)

/-- The ternary orthogonal order has precisely three factors of two when the
field order is three modulo eight. Only its failure of divisibility by 32 is needed. -/
public theorem not_thirtyTwo_dvd_orthogonal_order {p : ℕ} (hp : p % 8 = 3) :
    ¬ 32 ∣ p * (p ^ 2 - 1) := by
  have hp3 : 3 ≤ p := by omega
  have hs : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have hsq : p ^ 2 % 16 = 9 := by
    have hres : p % 16 = 3 ∨ p % 16 = 11 := by omega
    rcases hres with h | h <;> norm_num [Nat.pow_mod, h]
  have hm : (p ^ 2 - 1) % 16 = 8 := by omega
  have hprod : (p * (p ^ 2 - 1)) % 16 = 8 := by
    have hres : p % 16 = 3 ∨ p % 16 = 11 := by omega
    rcases hres with h | h <;> norm_num [Nat.mul_mod, h, hm]
  intro hd
  have hd16 : 16 ∣ p * (p ^ 2 - 1) := dvd_trans (by decide : 16 ∣ 32) hd
  have := Nat.mod_eq_zero_of_dvd hd16
  omega

/-- Conditional final reduction. The normal form must cover every outer
involution on the original Gram matrix, through an actual group equivalence.
The other premise concerns only a concrete ternary orthogonal group. -/
public theorem inner_of_normalized_outer_and_orthogonal_bound
    {p : ℕ} (hp : p % 8 = 3)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (hnormal : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J), a ^ 2 = 1 →
      (¬ ∃ k, a = MulAut.conj k) →
      ∃ (J₀ : HermitianForm 3 E)
        (e : ProjectiveSpecialUnitaryMatrixGroup J ≃*
          ProjectiveSpecialUnitaryMatrixGroup J₀),
        J₀.conj = J.conj ∧ J₀.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
          J₀.IsEntrywiseConjugation (MulAut.congr e a))
    (horder : ∀ (F : Type u) [Field F] [Finite F], Nat.card F = p →
      Nat.card (splitOrthogonalForm F).specialSubgroup ∣ p * (p ^ 2 - 1))
    [Finite E] (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hQ : Nat.card Q = 32) (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : a ^ 2 = 1) (hfix : ∀ x : Q, a x = x) :
    ∃ k : ProjectiveSpecialUnitaryMatrixGroup J, a = MulAut.conj k := by
  by_contra houter
  obtain ⟨J₀, e, hc, hJ₀, hgraph⟩ := hnormal a ha houter
  have hQle : Q ≤ a.fixedSubgroup := by
    intro x hx
    exact (MulAut.mem_fixedSubgroup _ _).mpr (hfix ⟨x, hx⟩)
  have hdiv : 32 ∣ Nat.card a.fixedSubgroup := by
    rw [← hQ]
    exact Subgroup.card_dvd_of_le hQle
  have htransfer : Nat.card a.fixedSubgroup =
      Nat.card (MulAut.congr e a).fixedSubgroup :=
    Nat.card_congr (MulAut.fixedSubgroupCongr e a).toEquiv
  rw [htransfer] at hdiv
  have hf : Nat.card (FixedBy.subfield E J₀.conj) = p := by
    rw [hc]
    exact hfixed
  exact not_thirtyTwo_dvd_orthogonal_order hp
    (hdiv.trans ((card_projectiveFixed_dvd_orthogonal J₀ hJ₀ hgraph).trans
      (horder (FixedBy.subfield E J₀.conj) hf)))

/-- An involutory automorphism fixing a subgroup of order 32 pointwise is
inner for the actual PSU₃ image over a field of order `p²`, with prime
fixed-field order `p ≡ 3 (mod 8)`. The Gram matrix is arbitrary, and `p = 3`
is included. No semilinearity, normalization, descent or Sylow hypothesis
is required. -/
public theorem inner_of_involutive_fixing_order_thirtyTwo [Finite E]
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hQ : Nat.card Q = 32)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : a ^ 2 = 1) (hfix : ∀ x : Q, a x = x) :
    ∃ k : ProjectiveSpecialUnitaryMatrixGroup J, a = MulAut.conj k := by
  exact inner_of_normalized_outer_and_orthogonal_bound J hp8 hfixed
    (NormalizedOuter.normalized_outer J hp hp8 hcard hfixed)
    (fun F _ _ hF => card_splitOrthogonal_specialSubgroup_dvd (F := F) hp8 hF)
    Q hQ a ha hfix

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
