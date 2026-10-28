module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.Normalizers
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.ScalarQuotients
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.TwoGroupExclusion
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.MetacyclicTransfer
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.FixedFieldNormalizer

/-!
# Prime degree and the dihedral coefficient normalizer

The trivial two-core excludes the solvable radical, and Burnside's
prime-power-index argument then shows that the coefficient group Γ is not
a two-group. Choose an odd prime p dividing its order. Scalar normal
generation and the metacyclic transfer argument make p coprime to |F| - 1.
The fixed-field argument forces the field degree and |Γ| to equal p and
constructs a dihedral isomorphism for the literal normalizer of Γ.

All three branches are proved in the imported descendants and assembled
below from the original action hypotheses and scalar normal generation.
The case p = 3 is retained: its degree-eight recognition is a separate
part of the source theorem. `DihedralGroup p` has order 2p.

Source: GLS, Volume 4, Chapter 1, Lemmas 3.8(a,b) and 3.9,
`refs/KGroup/GLS4/Chapter1.tex`, lines 419–451.
-/

public section

namespace MulAction.SemilinearPointStabilizer

/-- The prime-degree reduction in GLS 4, Lemmas 3.8(a,b) and 3.9, with scalar
normal generation supplied by the earlier reduction. The two-group exclusion,
transfer coprimality and fixed-field premises are all discharged. -/
theorem Coordinates.prime_degree_and_dihedral_normalizer
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [MulAction X F] [FaithfulSMul X F] (c : Coordinates X F)
    (htwo : IsMultiplyPretransitive X F 2) {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hcore : pCore 2 X = ⊥)
    (hgen : c.scalarClosure = ⊤) :
    n.Prime ∧ Odd n ∧ Nat.card (twoPoint (X := X) (F := F)) = n ∧
      Nonempty (Subgroup.normalizer (twoPoint (X := X) (F := F) : Set X) ≃*
        DihedralGroup n) := by
  obtain ⟨p, hp, hodd, hpdvd⟩ :=
    exists_odd_prime_dvd_twoPoint (c.not_isPGroup_twoPoint hn htwo hF hcore)
  have hcop := c.coprime_scalar_order_of_odd_coefficient_prime hp hodd htwo hF hgen hpdvd
  obtain ⟨hnp, hΓ, hnormalizer⟩ :=
    c.prime_degree_card_and_dihedral_normalizer htwo hn hF hcore hgen hp hodd hpdvd hcop
  subst n
  exact ⟨hp, hodd, hΓ, hnormalizer⟩

/-- Source application of the transfer obstruction, with the two-group
exclusion and metacyclic prime-divisibility step explicitly supplied. -/
theorem exists_odd_prime_noncentral_sylow_normalizer
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [MulAction X F] [FaithfulSMul X F] (c : Coordinates X F)
    (hgen : c.scalarClosure = ⊤)
    (hΓ : ¬ IsPGroup 2 (twoPoint (X := X) (F := F)))
    (htransfer : ∀ p : ℕ, p.Prime → Odd p →
      p ∣ Nat.card (twoPoint (X := X) (F := F)) → p.Coprime (Nat.card F - 1)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      p ∣ Nat.card (twoPoint (X := X) (F := F)) ∧
      ∀ Q : Sylow p X,
        ¬ Subgroup.normalizer (Q : Set X) ≤ Subgroup.centralizer (Q : Set X) := by
  obtain ⟨p, hp, hodd, hdvd⟩ := exists_odd_prime_dvd_twoPoint hΓ
  let : Fact p.Prime := ⟨hp⟩
  have hpX : p ∣ Nat.card X :=
    hdvd.trans (twoPoint (X := X) (F := F)).card_subgroup_dvd_card
  exact ⟨p, hp, hodd, hdvd, fun Q =>
    c.sylow_normalizer_not_le_centralizer hgen (htransfer p hp hodd hdvd) hpX Q⟩

end MulAction.SemilinearPointStabilizer
