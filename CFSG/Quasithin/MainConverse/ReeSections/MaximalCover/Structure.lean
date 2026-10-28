module

public import CFSG.Quasithin.MainConverse.ReeSections.Reduction
public import Theory.SpecificGroups.ReeF4.ConverseParabolics

/-!
# Structural inputs for the Ree maximal-subgroup cover

For `q = 2^(2*m+1)`, Malle's list consists of the two full parabolics,
five solvable torus normalizers, SU₃(q):2, PGU₃(q):2, Sz(q)≀2,
Sp₄(q):2, and subfield groups ²F₄(q₀) with `q = q₀^a`, `a` prime.
`MaximalAlternative` retains the actual matrix carriers and normal subgroups
needed to turn this list into `Envelope`. The two unitary cases are distinct:
SU₃ has a central kernel over PSU₃, whereas PGU₃ is the scalar image of
the full unitary group. All four outer layers have order two, and normality
is inside the subgroup being described. No splitting is needed by the consumer.

The five torus cases are coarsened to solvability. In the source these have
complements GL₂(3), two groups of order 96, and two cyclic groups of order 12;
the minus-sign order-96 case is listed only for `q > 8`. The subfield alternative
keeps both strict decrease and odd-degree divisibility, including `k = 0`.
The full group `Model 0` is not replaced by its simple derived subgroup.

These definitions do not assert exhaustiveness or a parabolic calculation.
`MalleMaximalAlternatives` and `ParabolicProjections` are independent remaining
proof obligations. Neither permits assumptions of ambient simplicity or of
known simple sections. Their assembly remains in `ReeSections.MaximalCover`.

Source: G. Malle, *The maximal subgroups of ²F₄(q²)*, J. Algebra 139
(1991), 52–69, DOI 10.1016/0021-8693(91)90283-E. The list appears in the
proof of Theorem 5, pp.2–3, of Himstedt–Nguyen–Tiep, arXiv:0910.4758.
We use that proof's unconditional maximal-subgroup list, not the additional
representation-theoretic assumptions of Theorem 5 itself.
-/

@[expose] public section

namespace CFSG.Quasithin.MainConverse.ReeSections

open Matrix BenderSuzuki.MatrixGroups

/-- The group structures from Malle's list, with actual multiplicative
equivalences and relative normal extensions. This is a list of possible
structures, not an assertion that every maximal subgroup has one of them. -/
inductive MaximalAlternative (m : ℕ) (H : Type) [Group H] : Prop where
  | parabolic (s : ReeF4.LargeLocalSeeds.Side)
      (e : H ≃* ReeF4.ConverseParabolics.parabolic m s)
  | torusNormalizer (hH : Group.IsSolvable H)
  | specialUnitary (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F = (2 ^ (2 * m + 1)) ^ 2)
      (hconj : ∀ x, J.conj x = x ^ (2 ^ (2 * m + 1)))
      (N : Subgroup H) [N.Normal] (e : N ≃* J.specialSubgroup)
      (hindex : Nat.card (H ⧸ N) = 2)
  | projectiveUnitary (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F = (2 ^ (2 * m + 1)) ^ 2)
      (hconj : ∀ x, J.conj x = x ^ (2 ^ (2 * m + 1)))
      (N : Subgroup H) [N.Normal]
      (e : N ≃* (J.unitarySubgroup.map ProjGenLinGroup.mk))
      (hindex : Nat.card (H ⧸ N) = 2)
  | suzukiWreath (N : Subgroup H) [N.Normal]
      (e : N ≃* (SuzukiMatrixGroup m × SuzukiMatrixGroup m))
      (hindex : Nat.card (H ⧸ N) = 2)
  | symplectic (F : Type) [Field F] [Finite F]
      (hcard : Nat.card F = 2 ^ (2 * m + 1))
      (N : Subgroup H) [N.Normal] (e : N ≃* symplecticGroup (Fin 2) F)
      (hindex : Nat.card (H ⧸ N) = 2)
  | subfield (k : ℕ) (hlt : k < m) (hdiv : (2 * k + 1) ∣ (2 * m + 1))
      (hprime : Nat.Prime ((2 * m + 1) / (2 * k + 1))) (e : H ≃* ReeF4.Model k)

/-- Convert the prime-extension clause in Malle's source notation into the
strict decrease and odd-degree divisibility required by the section induction.
The smaller parameter is allowed to be zero. -/
theorem MaximalAlternative.subfield_of_fieldSize_pow_eq
    {m k a : ℕ} {H : Type} [Group H] (ha : Nat.Prime a)
    (hfield : 2 ^ (2 * m + 1) = (2 ^ (2 * k + 1)) ^ a)
    (e : H ≃* ReeF4.Model k) : MaximalAlternative m H := by
  have hdegree : 2 * m + 1 = (2 * k + 1) * a :=
    Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa only [pow_mul] using hfield)
  have hlt : 2 * k + 1 < 2 * m + 1 := by
    rw [hdegree]
    exact lt_mul_of_one_lt_right (by omega) ha.one_lt
  have hquotient : (2 * m + 1) / (2 * k + 1) = a := by
    rw [hdegree, Nat.mul_div_cancel_left a (by omega)]
  exact .subfield k (by omega) ⟨a, hdegree⟩ (hquotient.symm ▸ ha) e


/-- The intrinsic maximal-subgroup classification still to be proved for the
genuine exceptional fixed-point construction, for every positive parameter. -/
def MalleMaximalAlternatives : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (ReeF4.Model m), IsCoatom M → MaximalAlternative m M

/-- Only the two Levi maps with two-group kernels are needed. Surjectivity,
exact radical orders, and simplicity are not premises of this contract. -/
def ParabolicProjections : Prop :=
  ∀ m, 1 ≤ m →
    (∃ π : ReeF4.ConverseParabolics.parabolic m .linear →*
      SpecialLinearGroup (Fin 2) (ReeF4.CoefficientField m) ×
        (ReeF4.CoefficientField m)ˣ, IsPGroup 2 π.ker) ∧
    (∃ π : ReeF4.ConverseParabolics.parabolic m .suzuki →*
      SuzukiMatrixGroup m × (ReeF4.CoefficientField m)ˣ, IsPGroup 2 π.ker)

end CFSG.Quasithin.MainConverse.ReeSections
