module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.FixedFieldNormalizer.Sylow
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.FixedFieldNormalizer.Dihedral

/-!
# Prime field degree and the dihedral coefficient normalizer

Under scalar normal generation and the earlier scalar-order coprimality
input, a coefficient Sylow subgroup is Sylow in the whole actor. Burnside
transfer and detection on its first omega subgroup yield an order-p
coefficient subgroup with noncentral normalizer. Its common fixed field
has two elements, so Artin's degree formula gives n = p. The coefficient
order divides n, hence this subgroup is the full two-point stabilizer Γ.

The normalizer acts transitively on the two common fixed points with
stabilizer Γ. Thus its order is 2p. An actual involution in the normalizer
acts nontrivially on Γ and inverts it, yielding the displayed equivalence
with `DihedralGroup p` for the literal normalizer.

Source: GLS, Volume 4, Chapter 1, Lemma 3.9, after Q = R,
`refs/KGroup/GLS4/Chapter1.tex`, lines 444–451. The conclusion includes p = 3;
the final exclusion of p = 3 uses a separate degree-eight recognition argument.
-/

public section

namespace MulAction.SemilinearPointStabilizer.Coordinates

variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
variable [MulAction X F] [FaithfulSMul X F]

/-- The fixed-field and normalizer conclusions of GLS Lemma 3.9, with exactly
the earlier-step scalar-generation and coprimality inputs. The degree lower
bound and trivial two-core are retained from the original action contract;
this branch needs no further use of them after scalar generation. -/
theorem prime_degree_card_and_dihedral_normalizer (c : Coordinates X F)
    (htwo : IsMultiplyPretransitive X F 2) {n : ℕ} (_hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (_hcore : pCore 2 X = ⊥)
    (hgen : c.scalarClosure = ⊤) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpdvd : p ∣ Nat.card (twoPoint (X := X) (F := F)))
    (hcop : p.Coprime (Nat.card F - 1)) :
    n = p ∧ Nat.card (twoPoint (X := X) (F := F)) = p ∧
      Nonempty (Subgroup.normalizer (twoPoint (X := X) (F := F) : Set X) ≃*
        DihedralGroup p) := by
  obtain ⟨P, hP, hPcard, hNC⟩ :=
    c.exists_prime_coefficient_noncentral_normalizer hp hodd htwo hF hgen hcop hpdvd
  obtain ⟨hn, hΓ⟩ := c.degree_and_card_twoPoint_of_prime_normalizer_not_le hF hP hPcard hNC
  have heq : P = twoPoint (X := X) (F := F) :=
    Subgroup.eq_of_le_of_card_ge hP (by rw [hPcard, hΓ])
  subst P
  exact ⟨hn, hΓ, c.twoPoint_normalizer_dihedral_of_prime_card hp hodd hΓ hNC⟩

end MulAction.SemilinearPointStabilizer.Coordinates
